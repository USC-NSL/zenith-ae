import json
import pika
import pika.exceptions
import pika.exchange_type
from threading import Condition
from typing import Dict, Any, FrozenSet, List, Tuple, Set, Optional, Generator
from pynadir.providers import AbstractProvider
from pynadir.structures import NadirPID, from_nadir_type, as_nadir_type
from pynadir.nadir import NadirGlobalParams
from pynadir.exceptions import ExecutionHalted, RepeatLabel

import nib.nib_settings


NADIR_EXCHANGE_NAME = "Nadir"


class SimpleRabbitQueue:
    BLOCKING_TIMEOUT = 5.0
    NONBLOCKING_TIMEOUT = 0.1

    @staticmethod
    def purge(names: List[str]):
        params = pika.ConnectionParameters(
            host=nib.nib_settings.DEFAULT_RBQ_HOST,
            credentials=pika.PlainCredentials(
                nib.nib_settings.DEFAULT_RBQ_USER,
                nib.nib_settings.DEFAULT_RBQ_PASS
            )
        )

        # A non-existant queue cannot be purged, thus we must check
        # to see which one of the given queues actually exist.
        with pika.BlockingConnection(parameters=params) as con:
            existing_queues = []
            for name in names:
                with con.channel() as ch:
                    try:
                        ch.queue_declare(name, passive=True)
                        existing_queues.append(name)
                    except pika.exceptions.ChannelClosed:
                        pass
            for name in existing_queues:
                with con.channel() as ch:
                    ch.queue_purge(name)

    def __init__(self, name: str, exchange: str, pids: List[NadirPID], declare: bool = True) -> None:
        self.name = name
        self.exchange = exchange
        self.pids = pids
        
        self._params = pika.ConnectionParameters(
            host=nib.nib_settings.DEFAULT_RBQ_HOST,
            credentials=pika.PlainCredentials(
                nib.nib_settings.DEFAULT_RBQ_USER,
                nib.nib_settings.DEFAULT_RBQ_PASS
            )
        )

        # Each PID will get its own connection/channel instance
        self._connections: Dict[NadirPID, pika.BlockingConnection] = dict()
        self._channels: Dict[NadirPID, pika.adapters.blocking_connection.BlockingChannel] = dict()

        # Delivery tags of messages
        self._tags: Dict[NadirPID, Optional[int]] = {pid: None for pid in self.pids}

        """
        Generators for consuming on a queue for each PID (thread).
        Maps PIDs to a pair of consumer generator, and a boolean value.
        The boolean value is `True` for non-blocking generators (meaning
        generators that have a very short timeout). These generators
        are used to issue non-blocking `peek` calls.
        
        Since RabbitMQ prefetches messages, we cannot have multiple consumer
        generators on the same channel, and we cannot change the timeout of
        a generator midway. It is very possible that the same PID can issue
        both non-blocking and blocking calls, as such, we need to close and
        cancel a generator if we are switching from being blocking to non-
        blocking and vice-versa.
        """
        self._consumer_generators: Dict[NadirPID, Tuple[Generator, bool]] = dict()

        # Now, prepare the exchange and the queues
        if declare:
            with pika.BlockingConnection(parameters=self._params) as con:
                with con.channel() as ch:
                    self._exchange = ch.exchange_declare(
                        NADIR_EXCHANGE_NAME, pika.exchange_type.ExchangeType.direct,
                        durable=True, auto_delete=False
                    )

                    # Declare and bind the queue
                    ch.queue_declare(self.name, durable=True, auto_delete=False)

                    # For now, use the queue name as the routing key
                    ch.queue_bind(self.name, self.exchange, routing_key=self.name)

    def get_or_make_channel(self, pid: NadirPID) -> pika.adapters.blocking_connection.BlockingChannel:
        chan = self._channels.get(pid)
        if chan is None:
            assert self._connections.get(pid) is None

            # Make the channel for this PID
            con = pika.BlockingConnection(parameters=self._params)
            chan = con.channel()

            # Consume one message at a time!
            chan.basic_qos(prefetch_count=1)

            self._connections[pid] = con
            self._channels[pid] = chan
        return chan

    def get_or_make_consumer_generator(self, pid: NadirPID, nonblocking: bool = False) -> Generator:
        res = self._consumer_generators.get(pid)
        channel = self.get_or_make_channel(pid)

        if res is not None:
            gen, _nonblocking = res
            if nonblocking != _nonblocking:
                # We MUST close this generator, cancel it and return all prefetched messages
                channel.cancel()
            else:
                return gen

        gen = channel.consume(
            self.name, auto_ack=False,
            inactivity_timeout=self.NONBLOCKING_TIMEOUT if nonblocking else self.BLOCKING_TIMEOUT
        )
        self._consumer_generators[pid] = (gen, nonblocking)
        return gen
    
    def put(self, pid: NadirPID, name: str, value: Any):
        if isinstance(value, (bytearray, bytes, str)):
            message = value
        else:
            message = json.dumps(from_nadir_type(value))
        self.get_or_make_channel(pid).basic_publish(self.exchange, name, message)

    def handle_outstanding_events(self, pid):
        if pid in self._connections:
            self._connections[pid].process_data_events()

    def peek(self, pid: NadirPID, name: str, nonblocking: bool = False) -> Tuple[int, Any]:
        # This method should return ONE message at most with NO ACKs
        (meth, _, body) = next(self.get_or_make_consumer_generator(pid, nonblocking))

        if not NadirGlobalParams.is_active:
            # No longer working, reject the message and exit
            if meth:
                self.get_or_make_channel(pid).basic_reject(meth.delivery_tag)
            raise ExecutionHalted

        if not body:
            if nonblocking:
                # self.handle_outstanding_events(pid)
                return -1, None
            else:
                raise RepeatLabel
        
        tag = meth.delivery_tag
        assert self._tags[pid] is None
        
        self._tags[pid] = tag

        try:
            return tag, as_nadir_type(json.loads(body))
        except ValueError:
            return tag, body
    
    def looks_empty(self, pid: NadirPID, name: str) -> bool:
        status = self.get_or_make_channel(pid).queue_declare(name, passive=True)
        return status.method.message_count == 0

    def pop(self, pid: NadirPID, tag):
        assert tag is not None
        assert self._tags[pid] == tag

        self.get_or_make_channel(pid).basic_ack(tag, multiple=False)
        self._tags[pid] = None

    def reject(self, pid: NadirPID, _tag: Optional[int]=None):
        tag = self._tags[pid]

        if tag is not None and _tag is not None:
            assert tag == _tag
            self.get_or_make_channel(pid).basic_reject(tag, requeue=True)
        elif tag is not None:
            self.get_or_make_channel(pid).basic_reject(tag, requeue=True)
        elif _tag is not None:
            self.get_or_make_channel(pid).basic_reject(tag, requeue=True)

    def nack_all(self, pid: NadirPID, _tag: Optional[int]=None):
        tag = self._tags[pid]

        if tag is not None and _tag is not None:
            assert tag == _tag
        self.get_or_make_channel(pid).basic_nack(0, requeue=True, multiple=True)
        self._tags[pid] = None

    def clear(self):
        with pika.BlockingConnection(parameters=self._params) as con:
            with con.channel() as chan:
                chan.queue_purge(self.name)
    
    def get_all(self, pid: NadirPID, name: str) -> List:
        """
        This is really dangerous, we need a better method.
        We need to create a new channel item, since the prefetch count on the current
        channel will not allow us to use it to get more messages.
        """

        with pika.BlockingConnection(parameters=self._params) as con:
            with con.channel() as channel:
                channel.basic_qos(prefetch_count=0)

                last_tag = None
                messages = []

                for meth, _, body in channel.consume(name, auto_ack=False, inactivity_timeout=self.NONBLOCKING_TIMEOUT):
                    if meth is None:
                        return []
                    last_tag = meth.delivery_tag
                    try:
                        messages.append(as_nadir_type(json.loads(body)))
                    except ValueError:
                        messages.append(body)

                channel.basic_nack(last_tag, multiple=True)
        return messages


class RabbitProvider(AbstractProvider):
    def __init__(self) -> None:
        self.pids = set()
        self._queues: Dict[str, SimpleRabbitQueue] = dict()
        self._keys: Dict[str, Set] = dict()

        # List of messages to commit to each queue in the end
        self._uncommitted_messages: Dict[NadirPID, List[Tuple[str, Any]]] = dict()
        
        # Each PID can have one un-acked message per queue
        self._peeked_tags: Dict[NadirPID, Dict[str, int]] = dict()

        # If popping a message is delayed, we move it to this dict
        self._delayed_tags: Dict[NadirPID, Dict[str, int]] = dict()

        # Messages explicitly stated to be done
        self._done_tags: Dict[NadirPID, Dict[str, int]] = dict()

        # This maps a tag to the actual message. It helps with house-keeping
        self._message_cache: Dict[NadirPID, Dict[int, Any]] = dict()

    def is_global(self) -> bool:
        return True

    def register_pid(self, pid: NadirPID):
        assert pid not in self.pids
        self.pids.add(pid)
        self._uncommitted_messages[pid] = list()
        self._peeked_tags[pid] = dict()
        self._delayed_tags[pid] = dict()
        self._done_tags[pid] = dict()
        self._message_cache[pid] = dict()
    
    def add_value(self, name: str, value: Any, *args, **kwargs):
        assert name not in self._queues
        assert 'interacting_pids' in kwargs
        assert isinstance(kwargs['interacting_pids'], list)

        interacting_pids: List[NadirPID] = kwargs['interacting_pids']
        
        self._queues[name] = SimpleRabbitQueue(
            name, NADIR_EXCHANGE_NAME, interacting_pids
        )

        if value is None:
            return
        elif isinstance(value, list):
            for val in value:
                assert isinstance(val, dict)

                self._queues[name].put(interacting_pids[0], name, val)
        elif isinstance(value, dict):
            self._queues[name].put(interacting_pids[0], name, value)
        else:
            raise ValueError

    def register_value(self, name: str, *args, **kwargs):
        assert name not in self._queues
        assert 'interacting_pids' in kwargs
        assert isinstance(kwargs['interacting_pids'], list)

        interacting_pids: List[NadirPID] = kwargs['interacting_pids']

        self._queues[name] = SimpleRabbitQueue(
            name, NADIR_EXCHANGE_NAME, interacting_pids, declare=False
        )

    def put_message(self, pid: NadirPID, queue_name: str, msg):
        self._uncommitted_messages[pid].append((queue_name, msg))
    
    def peek_message(self, pid: NadirPID, queue_name: str, nonblocking: bool = False):
        # We will not let double peeks!
        assert self._peeked_tags[pid].get(queue_name) is None

        # If the peeked tag was delayed, then you should get the message back after doing another peek!
        # For now, we will NOT allow peeking multiple messages (so no pre-fetches!)
        _tag = self._delayed_tags[pid].get(queue_name)
        if _tag:
            return self._message_cache[pid][_tag]

        tag, message = self._queues[queue_name].peek(pid, queue_name, nonblocking=nonblocking)
        if message is not None:
            self._peeked_tags[pid][queue_name] = tag
            self._message_cache[pid][tag] = message
        return message

    def get_message(self, pid: NadirPID, queue_name: str, nonblocking: bool = False):
        res = self.peek_message(pid, queue_name, nonblocking=nonblocking)
        self.pop_message(pid, queue_name)
        return res
    
    def pop_message(self, pid: NadirPID, queue_name: str):
        assert self._done_tags[pid].get(queue_name) is None

        """
        If we are ACKing a message, either we just peeked it, or it was
        delayed.
        """

        _peek_tag = self._peeked_tags[pid].get(queue_name)
        _delay_tag = self._delayed_tags[pid].get(queue_name)

        if _peek_tag is not None:
            self._done_tags[pid][queue_name] = _peek_tag
        else:
            assert _delay_tag is not None
            self._done_tags[pid][queue_name] = _delay_tag
    
    def looks_empty(self, pid: NadirPID, queue_name: str):
        return self._queues[queue_name].looks_empty(pid, queue_name)

    def fifo_peek(self, pid: NadirPID, queue_name: str) -> Any:
        # print(f"PEEKING QUEUE {queue_name}")
        return self.peek_message(pid, queue_name, nonblocking=False)
    def fifo_put(self, pid: NadirPID, queue_name: str, msg):
        self.put_message(pid, queue_name, msg)
    def fifo_peek_nb(self, pid: NadirPID, queue_name: str) -> Any:
        return self.peek_message(pid, queue_name, nonblocking=True)
    def fifo_pop(self, pid: NadirPID, queue_name: str):
        self.pop_message(pid, queue_name)
    def fifo_get(self, pid: NadirPID, queue_name: str) -> Any:
        return self.get_message(pid, queue_name)
    def ack_queue_ack(self, pid: NadirPID, queue_name: str):
        self.pop_message(pid, queue_name)
    def ack_queue_get(self, pid: NadirPID, queue_name: str) -> Any:
        return self.peek_message(pid, queue_name)
    def ack_queue_put(self, pid: NadirPID, queue_name: str, msg):
        return self.put_message(pid, queue_name, msg)
    def fanout_fifo_put(self, pid: NadirPID, queue_name: str, destination, msg):
        self.put_message(pid, queue_name, {
            '$destination': destination,
            '$message': msg
        })

    def send_keepalive(self, pid: NadirPID):
        for queue in self._queues.values():
            queue.handle_outstanding_events(pid)
    
    def abort(self, pid: NadirPID):
        # Just clear the uncommitted messages
        self._uncommitted_messages[pid].clear()

        # Reject all recently peeked messages
        for key, tag in self._peeked_tags[pid].items():
            self._queues[key].nack_all(pid, tag)
            # self._queues[key[0]].reject(pid, tag)
        
        # Clear any tags scheduled as done
        self._done_tags[pid].clear()
        self._peeked_tags[pid].clear()

        """
        It is also important to send a heartbeat here. When a process blocks
        for a very long time, RabbitMQ might think the connection is dead.
        So we manually send a heartbeat for the connection here.
        """
        self.send_keepalive(pid)

    def commit(self, pid: NadirPID):
        # print(f"(BEFORE) PID: {pid} =>\n{self._peeked_tags[pid]}\n{self._delayed_tags[pid]}\n{self._done_tags[pid]}")

        # Publish all uncommitted messages
        for name, message in self._uncommitted_messages[pid]:
            self._queues[name].put(pid, name, message)
        
        # Ack all done messages
        for queue_name, tag in self._done_tags[pid].items():
            self._queues[queue_name].pop(pid, tag)
            self._peeked_tags[pid].pop(queue_name, None)
            self._delayed_tags[pid].pop(queue_name, None)
            self._message_cache[pid].pop(tag, None)
        
        # Flag remaining peeked messages as delayed messages
        for key, value in self._peeked_tags[pid].items():
            assert key not in self._delayed_tags[pid]
            self._delayed_tags[pid][key] = value
        
        # Cleanup
        self._uncommitted_messages[pid].clear()
        self._peeked_tags[pid].clear()
        self._done_tags[pid].clear()

        # for queue in self._queues.values():
        #     queue.handle_outstanding_events(pid)

        # print(f"(AFTER) PID: {pid} =>\n{self._peeked_tags[pid]}\n{self._delayed_tags[pid]}\n{self._done_tags[pid]}")
    
    def nuke(self, queue_names: List[str] = None):
        if queue_names is None or len(queue_names) == 0:
            for queue in self._queues.values():
                queue.clear()
        else:
            SimpleRabbitQueue.purge(queue_names)
        
    def get_value(self, name: str, pid: NadirPID = None, address = ...) -> Any:
        return self._queues[name].get_all(pid, name)

    def set_value(self, pid: NadirPID, name: str, value: Any, address = ...):
        raise NotImplementedError
    def domain(self, name: str, address = ...):
        raise NotImplementedError
    def wait(self, pid: NadirPID, cv: Condition, condition_function, *args, **kwargs):
        raise NotImplementedError
    def register_cv(self, pids: FrozenSet[NadirPID], cv: Condition, index: int):
        raise NotImplementedError
