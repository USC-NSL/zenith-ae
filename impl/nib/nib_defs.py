import bson
import enum
import json
import pika
import pymongo
import threading
import networkx as nx
import datetime
import nib.nib_settings
from bson import json_util
from typing import List, Dict, Tuple, Set, Callable, Any
from pika.exchange_type import ExchangeType
from pynadir.utils.logging import TitledLog
from openflow.ryulib.openflow_v13_defs import OFPCR_ROLE_MASTER, OFPCR_ROLE_EQUAL, OFPCR_ROLE_SLAVE, OFPCR_ROLE_NOCHANGE

"""
UPDATE:
    In order to redistribute the workload and make things a bit more
    useful, we are moving the queues from NIB to RabbitMQ.
    Since we don't need transactional semantics or atomicity, we don't
    need to be worried about RabbitMQ's simplicity, it will suffice (if
    we were worried about that, Kafka would be our only option).
    
    I am going to start with a simple port, and see how things end up.
    It is expected that once this is done, we can do away with all the
    poll operations on the database and keep everything clean.
"""

short_uid = lambda uid: str(uid)[-2:] if nib.nib_settings.USE_SHORT_ID else str(uid)


class NIBBase:
    def __init__(self, path: str = nib.nib_settings.LOCAL_PATH, db_name='nib'):
        assert path is not None

        self.path = path
        self.db_name = db_name
        self.client = pymongo.MongoClient(self.path)
        self.db = self.client[self.db_name]

    def insert_document(self, collection: str, document: Dict, session=None):
        return self.db[collection].insert_one(document, session=session).inserted_id

    def insert_documents(self, collection: str, documents: List[Dict], session=None, ordered=True):
        return self.db[collection].insert_many(documents, session=session, ordered=ordered).inserted_ids

    def create_unique_index(self, collection: str, field: str):
        self.db[collection].create_index(keys=field, unique=True)
    
    def drop_collection(self, collection: str):
        return self.db.drop_collection(collection)

    def count_documents(self, collection: str):
        return self.db[collection].count_documents(filter={})

    def put_on_queue(self, queue: str, document: Dict):
        document_with_t = document.copy()
        document_with_t['t'] = datetime.datetime.now()
        return self.insert_document(queue, document_with_t)

    def put_many_in_queue(self, queue: str, documents: List[Dict]):
        for document in documents:
            return self.put_on_queue(queue, document)

    def pop_from_queue(self, queue: str):
        """ Note:
            This is non-blocking, it might return None.
            Mongo guarantees that only a single subscriber to this queue is going
            to actually receive anything.
        """

        nib_res = self.db[queue].find_one_and_delete(filter={}, sort=[("t", 1)])
        nib_res.pop('t')
        return nib_res

    def read_from_queue(self, queue: str):
        nib_res = self.db[queue].find_one(filter={}, sort=[("t", 1)])
        if nib_res:
            nib_res.pop('t')
        return nib_res

    def query_document(self, collection: str, filter: Dict, projection: Dict = None, session = None):
        return self.db[collection].find(filter=filter, projection=projection, session=session)

    def query_one_document(self, collection: str, filter: Dict, projection: Dict = None, sort = None, session=None):
        if sort is None:
            return self.db[collection].find_one(filter=filter, session=session)
        try:
            return next(self.db[collection].find(filter=filter, sort=sort, session=session))
        except StopIteration:
            return None

    def aggregate(self, collection: str, pipeline: List):
        return self.db[collection].aggregate(pipeline)

    def update_document(self, collection: str, filter: Dict, update: Dict, upsert: bool = False, session = None):
        return self.db[collection].update_one(filter, update, upsert=upsert, session=session)

    def update_documents(self, collection: str, filter: Dict, update: Dict):
        return self.db[collection].update_many(filter, update)

    def replace_one_document(self, collection: str, filter: Dict, replacement: Dict, upsert: bool = False):
        return self.db[collection].replace_one(filter, replacement, upsert)

    def find_and_update_document(self, collection: str, filter: Dict, update: Dict, after: bool = True,
                                 sort=None):
        if sort is None:
            sort = [("_id", 1)]
        if after:
            return self.db[collection].find_one_and_update(
                filter, update, return_document=pymongo.collection.ReturnDocument.AFTER, sort=sort
            )
        return self.db[collection].find_one_and_update(filter, update, sort=sort)

    def delete_one_document(self, collection: str, filter: Dict):
        return self.db[collection].delete_one(filter)

    def do_transaction(self, callback: Callable, rc=nib.nib_settings.DEFAULT_READ_CONCERN,
                       wc=nib.nib_settings.DEFAULT_WRITE_CONCERN,
                       rp=nib.nib_settings.DEFAULT_READ_PREFERENCE,
                       **callback_kwargs):
        """
        If nib.nib_settings.DISABLE_TRANSACTIONS is enabled, then this
        does NOT actually do a transaction, it will not open a session
        and just commit the operation non-atomically.

        This is the default behavior, we allow this to be turned off in
        order to evaluate performance.
        """

        if not nib.nib_settings.DISABLE_TRANSACTIONS:
            with self.client.start_session() as session:
                return session.with_transaction(
                    lambda s: callback(s, **callback_kwargs),
                    write_concern=wc,
                    read_concern=rc,
                    read_preference=rp
                )
        else:
            return callback(None, **callback_kwargs)

    def block_until_insertion(self, collection: str, timeout=1, wc=None):
        """
        Block for `timeout` seconds until an insertion is done into collection
        `collection`.
        When `wc` is None, a new change stream will be created, but if not, that
        particular change stream will be used again.

        Upon the detection of a change, the change stream is closed and None
        will be returned, if not, then `wc` will be returned and the caller
        can retry.

        This is mostly used for queues, and since they have their own semantics,
        we refrain from using the exact result returned from the change stream.

        TODO: Think really hard whether or not we still need the above!!!
        """

        if not wc or wc == -1:
            wc = self.db[collection].watch(
                max_await_time_ms=timeout * 1000
            )
        else:
            if not wc.alive:
                TitledLog.warning('nib', "Invalidation event occurred on NIB, retrying!")
                return -1

        res = wc.try_next()
        if res and res["operationType"] == "insert":
            wc.close()
            return None
        return wc

    def block_until_state_change(self, collection: str, desired_state, state_name='state', timeout=1, wc=None, _id=None):
        if not wc or wc == -1:
            wc = self.db[collection].watch(
                max_await_time_ms=timeout * 1000
            )
        else:
            if not wc.alive:
                TitledLog.warning('nib', "Invalidation event occurred on NIB, retrying!")
                return -1

        res = wc.try_next()
        if res and res["operationType"] == "update":
            if _id and res['documentKey']['_id'] != _id:
                return wc
            if res["updateDescription"]["updatedFields"][state_name] == desired_state:
                wc.close()
                return
        return wc
    
    def watch_document(self, _id: bson.ObjectId, collection: str, state_name: str, desired_state: Any, token: Any, timeout=1) -> Tuple[bool, Any]:
        pipe = [{"$match": {f"fullDocument.{state_name}": desired_state, "fullDocument._id": _id}}]
        with self.db[collection].watch(pipeline=pipe, full_document="updateLookup", max_await_time_ms=int(timeout * 1000), start_after=token) as stream:
            while True:
                res = stream.try_next()
                if res is None:
                    if stream.alive:
                        return False, stream.resume_token
                    return False, None
                else:
                    if res["operationType"] == "update":
                        if res['documentKey']['_id'] == _id and res["updateDescription"]["updatedFields"][state_name] == desired_state:
                            return True, None
    
    def get_resume_token(self, collection: str) -> Any:
        with self.db[collection].watch() as stream:
            return stream.resume_token

    def stop_queues(self):
        # Stops all NIBQueue instances connected to this interface
        for attribute_name in dir(self):
            attribute = getattr(self, attribute_name)
            if isinstance(attribute, NIBQueue):
                attribute.stop()


def _ack(channel, delivery_tag):
    if channel.is_open:
        channel.basic_ack(delivery_tag)
    else:
        TitledLog.warning('nib', f"Unable to ACK tag {delivery_tag}, channel is closed.")


class NIBQueue:
    """
    This object instance may only access the RBQ channel from
    a single thread, though it can be safely called by multiple
    threads.

    UPDATE:
        In order to move IR_QUEUE into RBQ, we need to make sure that only
        the assigned OFC Worker Pool threads do the actual consuming.
        Pika just creats a thread and does it there, we don't want that.
        Since Pika channels may not be used in different threads, then
        we need to create connections for each thread, and then consume
        data in that thread in a blocking manner. While the overhead of
        setting up the connections is quite large in the beginning, this
        pays off for very busy queues, since it reduces the number of context
        switchings that the kernel needs to handle.
    """

    def __init__(self, name, exchange_name, produce=False, threads=None):
        self.name = name
        self.exchange_name = exchange_name
        self.function_maps = {}
        self.is_active = True
        self.producer = produce
        self.threads = threads

        self._params = pika.ConnectionParameters(
            host=nib.nib_settings.DEFAULT_RBQ_HOST,
            credentials=pika.PlainCredentials(
                nib.nib_settings.DEFAULT_RBQ_USER,
                nib.nib_settings.DEFAULT_RBQ_PASS
            )
        )

        if self.threads is not None and self.producer:
            raise NotImplementedError("Thread dedicated producer has not yet been implemented")
        elif self.threads is None:
            self._init_callback()
        else:
            self._init_threaded()

    def _init_callback(self):
        self._connection = pika.BlockingConnection(parameters=self._params)
        self._channel = self._connection.channel()

        self._exchange = self._channel.exchange_declare(
            exchange=self.exchange_name,
            exchange_type=ExchangeType.direct,
            passive=False,
            durable=True,
            auto_delete=False
        )

        self._channel.basic_qos(prefetch_count=nib.nib_settings.DEFAULT_PREFETCH_COUNT)

        self._producer_thread = None
        if self.producer:
            self._producer_thread = threading.Thread(target=self.start_production)
            self._producer_thread.start()

    def _init_threaded(self):
        self._connections = {thread.name: pika.BlockingConnection(parameters=self._params) for thread in self.threads}
        self._channels = {thread_name: _connection.channel() for thread_name, _connection in self._connections.items()}

        thread_name = self.threads[0].name

        self._exchange = self._channels[thread_name].exchange_declare(
            exchange=self.exchange_name,
            exchange_type=ExchangeType.direct,
            passive=False,
            durable=True,
            auto_delete=False
        )

        for _channel in self._channels.values():
            _channel.basic_qos(prefetch_count=nib.nib_settings.DEFAULT_PREFETCH_COUNT)

    def declare(self):
        """
        We should be careful if we are using threads != None
        for this.
        Eventlet does not seem to like it.
        """

        if self.threads:
            _channel = self._channels[0]
        else:
            _channel = self._channel

        _channel.queue_declare(
            queue=self.name,
            passive=False,
            durable=True,
            auto_delete=False
        )

    def bind(self, key = None):
        """
        Like the above, Eventlet again complains if this method is used
        as is with threads != None.
        For OFC, the Failover Handler will call these.
        """

        routing_key = key if key is not None else self.name

        self._channel.queue_bind(
            queue=self.name,
            exchange=self.exchange_name,
            routing_key=routing_key
        )

        TitledLog.info('nib', f"Declared binding {self.exchange_name}:{self.name} --- {routing_key}")

    def unbind(self, who, key):
        """
        Like the above, Eventlet again complains if this method is used
        as is with threads != None.
        For OFC, the Failover Handler will call these.
        """

        self._channel.queue_unbind(
            queue=who,
            exchange=self.exchange_name,
            routing_key=key
        )

        TitledLog.debug('nib', f"Removed binding {self.exchange_name}:{who} --- {key}")

    def delete(self, who=None, if_empty=False):
        who = who if who else self.name

        self._channel.queue_delete(who, if_empty=if_empty)

        TitledLog.warning('nib', f"Removed queue {who}")

    def start_production(self):
        while self.is_active:
            self._connection.process_data_events(time_limit=1)

    def close(self):
        self.stop()
        if self.producer:
            self._connection.process_data_events(time_limit=1)
            self._producer_thread.join()
        else:
            self._channel.stop_consuming()
        if self._connection.is_open:
            self._connection.close()

    def stop(self):
        self.is_active = False

    def _publish(self, msg_bytes, key=None):
        routing_key = key if key is not None else self.name

        self._channel.basic_publish(
            exchange=self.exchange_name,
            routing_key=routing_key,
            body=msg_bytes
        )

    def publish(self, msg_bytes, key=None):
        self._connection.add_callback_threadsafe(lambda: self._publish(msg_bytes, key))

    def publish_many(self, ls_msg_bytes, key=None):
        for msg_bytes in ls_msg_bytes:
            self.publish(msg_bytes, key)

    @staticmethod
    def _do_work(channel, delivery_tag, body, func, eager=False, *args):
        if eager:
            channel.connection.add_callback_threadsafe(lambda : _ack(channel, delivery_tag))

        ret = func(body, delivery_tag, *args)

        if ret == -1:
            # No ACK!
            return

        if not eager:
            channel.connection.add_callback_threadsafe(lambda : _ack(channel, delivery_tag))

    def _consume(self, channel, method_frame, _header_frame, body, name, eager=False, on_thread=True, *args):
        delivery_tag = method_frame.delivery_tag
        func = self.function_maps.get(name)

        if not func:
            raise RuntimeError(f"No subscribed function for {name}")

        if on_thread:
            t = threading.Thread(target=self._do_work, args=(channel, delivery_tag, body, func, eager) + args)
            t.start()
        else:
            self._do_work(channel, delivery_tag, body, func, eager, *args)

    def _subscribe_callback(self, name, eager=False, *args):
        for message in self._channel.consume(queue=self.name, inactivity_timeout=1):
            if not self.is_active:
                TitledLog.info('nib', f"Finished consuming on queue {self.exchange_name}:{self.name}")
                break

            if not all(message):
                continue

            method, properties, body = message
            self._consume(self._channel, method, properties, body, name, eager, True, *args)
        self.close()

    def _subscribe_threaded(self, name, _channel, eager=False, *args):
        for message in _channel.consume(queue=self.name, inactivity_timeout=1):
            if not self.is_active:
                TitledLog.info('nib', f"Finished consuming on queue {self.exchange_name}:{self.name}")
                break

            if not all(message):
                continue

            method, properties, body = message
            self._consume(_channel, method, properties, body, name, eager, False, *args)
        # Do NOT call `close`

    def subscribe(self, func, eager=False, *args):
        name = threading.current_thread().name

        if self.threads:
            _channel = self._channels.get(name)
            if not _channel:
                raise ValueError(f"Thread {name} is not assigned to this consumer pool")

        if name not in self.function_maps:
            self.function_maps[name] = func
            TitledLog.info('nib', f"{name} subscribed to {self.exchange_name}:{self.name}")
        else:
            TitledLog.info('nib', f"Consumer {name} of {self.exchange_name}:{self.name} has returned")

        if self.threads:
            self._subscribe_threaded(name, _channel, eager, *args) # noqa
        else:
            self._subscribe_callback(name, eager, *args)


class COLLECTIONS:
    TE_EVENT = "te_event"
    DATAPATH = "datapath"
    IR = "ir"
    DAG = "dag"
    ACTIVE_DAG = "active_dag"
    IR_QUEUE = "ir_queue"
    ROLE = "role"
    FAILOVER_STATE = "failover_state"
    PENDING_IR = "pending_ir"


class IR_STATE:
    IR_NONE = "IR_NONE"
    IR_UNLOCK = "IR_UNLOCK"
    IR_SENT = "IR_SENT"
    IR_DONE = "IR_DONE"


class SW_STATE:
    SW_SUSPEND = "SW_SUSPEND"
    SW_RUN = "SW_RUN"
    SW_RECONCILE = "SW_RECONCILE"


class DAG_STATE:
    DAG_NONE = "DAG_NONE"
    DAG_SUBMIT = "DAG_SUBMIT"
    DAG_STALE = "DAG_STALE"


class OFC_ROLE(enum.Enum):
    ROLE_SLAVE = OFPCR_ROLE_SLAVE
    ROLE_EQUAL = OFPCR_ROLE_EQUAL
    ROLE_MASTER = OFPCR_ROLE_MASTER

    # This will be the initial role of the switch
    ROLE_UNKNOWN = OFPCR_ROLE_NOCHANGE

    def __str__(self):
        return self.name

    def __eq__(self, other):
        if isinstance(other, int):
            return self.value == other
        elif isinstance(other, str):
            return self.name == other
        return id(self) == id(other)

    def __hash__(self):
        return hash(self.value)


class FAILOVER_STATE_NIB:
    FAILOVER_NONE = "FAILOVER_NONE"
    FAILOVER_INIT = "FAILOVER_INIT"
    FAILOVER_READY = "FAILOVER_READY"
    FAILOVER_TERMINATE = "FAILOVER_TERMINATE"
    FAILOVER_TERMINATE_DONE = "FAILOVER_TERMINATE_DONE"


class CONTROLLER_MODULES(enum.Enum):
    OFC_WORKER_POOL = 0
    OFC_MONITORING_SERVER = 1
    OFC_EVENT_HANDLER = 2
    RC = 3
    OFC_FAILOVER_HANDLER = 4

    def __str__(self):
        return self.name

    def __eq__(self, other):
        if isinstance(other, int):
            return self.value == other
        elif isinstance(other, str):
            return self.name == other
        return id(self) == id(other)

    def __hash__(self):
        return hash(self.value)


class SAVED_STATE_TYPES:
    class OFC:
        NO_STATUS = "NO_STATUS"
        STATUS_LOCKING = "STATUS_LOCKING"
        STATUS_SENT_DONE = "STATUS_SENT_DONE"
        START_RESET_IR = "START_RESET_IR"

    class RC:
        NO_STATUS = "NO_STATUS"
        STATUS_START_SCHEDULING = "STATUS_START_SCHEDULING"


class IR_TYPE:
    INSTALL_FLOW = "INSTALL_FLOW"
    DELETE_FLOW = "DELETE_FLOW"
    FLOW_STAT_REQ = "FLOW_STAT_REQ"
    PERIODIC_REQ = "PERIODIC_REQ"
    INSTALL_GROUP = "INSTALL_GROUP"
    DELETE_GROUP = "DELETE_GROUP"
    GROUP_STAT_REQ = "GROUP_STAT_REQ"
    PERIODIC_GROUP_REQ = "PERIODIC_GROUP_REQ"
    ROLE_REQ = "ROLE_REQ"


class IR:
    def __init__(self, command: str, dp_id: int, uid: bson.ObjectId = None,
                 state: IR_STATE = IR_STATE.IR_NONE, type: IR_TYPE = IR_TYPE.INSTALL_FLOW, target=None,
                 cookie=0):
        self.command = command
        self.dp_id = dp_id
        self.uid = uid
        self.state = state
        self.type = type

        # For DELETE_FLOW only. Specifies which IR ID you are trying to kill ...
        self.target = target

        # For giving IDs to flows in the switches
        # UPDATE: For Group declarations, this feild is actually the group ID plus an offset
        self.cookie = cookie
        if type == IR_TYPE.INSTALL_GROUP:
            self.cookie = cookie + nib.nib_settings.GROUP_IR_START_COOKIE

    def __str__(self) -> str:
        if self.type == IR_TYPE.DELETE_FLOW:
            return (f"TYPE = {self.type}, COMMAND = {self.command}, DP = {self.dp_id}, STATE = {self.state}, "
                    f"TARGET = {short_uid(self.target)}, COOKIE = {self.cookie}")
        return (f"TYPE = {self.type}, COMMAND = {self.command}, DP = {self.dp_id}, STATE = {self.state}, "
                f"COOKIE = {self.cookie}")

    def __eq__(self, other):
        if isinstance(other, IR):
            if self.uid == other.uid:
                return True
            if self.command == other.command and self.dp_id == other.dp_id and self.cookie == other.cookie:
                return True
        return False

    def __hash__(self):
        return int.from_bytes(self.uid.binary, 'big')

    def get_dict(self):
        return {
            'type': self.type, 'command': self.command,
            'dp_id': self.dp_id, 'state': self.state, 'target': self.target,
            'cookie': self.cookie
        }

    def get_full_dict(self):
        return {
            'type': self.type, 'command': self.command, 'dp_id': self.dp_id,
            'state': self.state, 'target': self.target, 'cookie': self.cookie,
            '_id': self.uid
        }

    def get_json_dict(self):
        return {
            'type': self.type, 'command': self.command, 'dp_id': self.dp_id,
            'state': self.state, 'target': json_util.dumps(self.target),
            'cookie': self.cookie, 'uid': json_util.dumps(self.uid)
        }

    def has_uid(self):
        return self.uid is not None

    def serialize(self):
        return json.dumps(self.get_dict()).encode('utf-8')

    @classmethod
    def parse_from_nib(cls, nib_res):
        return IR(
            type=nib_res['type'],
            command=nib_res['command'],
            dp_id=nib_res['dp_id'],
            uid=nib_res['_id'],
            state=nib_res['state'],
            target=nib_res['target'],
            cookie=nib_res['cookie']
        )

    @classmethod
    def serialize_many(cls, irs: List):
        aggregate = {'irs': irs}
        return json.dumps(aggregate).encode('utf-8')

    @classmethod
    def deserialize_one(cls, ir_bytes: bytes):
        return cls(**json.loads(ir_bytes.decode('utf-8')))

    @classmethod
    def deserialize_many(cls, ir_bytes: bytes):
        ir_dicts = json.loads(ir_bytes.decode('utf-8'))
        return [cls(**ir_dict) for ir_dict in ir_dicts]

    @classmethod
    def parse_from_json_dict(cls, d):
        return cls(d['command'], d['dp_id'], json_util.loads(d['uid']),
                   d['state'], d['type'], json_util.loads(d['target']),
                   d['cookie'])

    def set_state(self, state):
        self.state = state

    def is_done(self):
        return self.state == IR_STATE.IR_DONE

    def set_uid(self, uid=None):
        uid = uid if uid is not None else bson.ObjectId()
        self.uid = uid

    def set_cookie(self, new_cookie):
        prev_cookie = self.cookie
        self.cookie = new_cookie

        return prev_cookie

    def get_full_command(self):
        if self.cookie:
            return f"cookie={self.cookie},{self.command}"
        return self.command


class IREncoder(json.JSONEncoder):
    def default(self, obj):
        assert isinstance(obj, IR)
        return {
            'type': obj.type, 'command': obj.command, 'dp_id': obj.dp_id, 'cookie': obj.cookie,
            'state': obj.state, 'target': json_util.dumps(obj.target), 'uid': json_util.dumps(obj.uid)
        }


class IRDecoder(json.JSONDecoder):
    def decode(self, s, **kwargs):
        d = json.loads(s)
        return IR(d['command'], d['dp_id'], json_util.loads(d['uid']),
                  d['state'], d['type'], json_util.loads(d['target']), d['cookie'])


class UID_DAG:
    def __init__(self, v, e: Set[Tuple], uid: int = None, state: str = DAG_STATE.DAG_NONE):
        self.root = v[0]
        self.v = set(v)
        self.e = set(tuple(pair) for pair in e)
        self.uid = uid
        self.state = state
        self.dag = nx.DiGraph()
        self.dag.add_nodes_from(self.v)
        self.dag.add_edges_from(self.e)

    def get_ir_dependencies(self, ir_uid):
        return nx.ancestors(self.dag, ir_uid)

    # The _only_ valid way to expand the DAG is with these methods!

    def add_node(self, ir_uid):
        self.v.add(ir_uid)
        self.dag.add_node(ir_uid)

    def add_edge(self, src_uid, dst_uid):
        self.e.add((src_uid, dst_uid))
        self.dag.add_edge(src_uid, dst_uid)


class DAG:
    def __init__(self, v: List[IR], e: List[Tuple[IR, IR]], uid: int = None, make=True,
                 state: str = DAG_STATE.DAG_NONE, trig_set = None):
        self.v = v
        self.e = e
        self.state = state
        self.uid = uid
        self.dag = None
        self.ir_order = None
        self.done_order = None
        self.trig_set = trig_set
        if not trig_set:
            self.trig_set = []
        if make:
            self.make()

    def _get_vertex_uids(self):
        return [ir.uid for ir in self.v]

    def _get_edge_uids(self):
        return [(a.uid, b.uid) for a, b in self.e]

    def get_dict(self):
        return {
            'v': self._get_vertex_uids(),
            'e': self._get_edge_uids(),
            'state': self.state,
            'trig_set': self.trig_set
        }

    def get_dict_with_uid(self):
        assert self.uid
        return {
            'v': self._get_vertex_uids(),
            'e': self._get_edge_uids(),
            'state': self.state,
            'trig_set': self.trig_set,
            '_id': self.uid
        }

    def make(self):
        self.dag = nx.DiGraph(self.e)

    def is_ir_ready(self, ir: IR):
        if hasattr(self, 'dag'):
            return all([ir.is_done() for ir in nx.ancestors(self.dag, ir)])
        raise ValueError("Graph not \'make\'d!")

    def order(self):
        if self.dag:
            self.ir_order = list(nx.topological_sort(self.dag))
            # shallow copy is enough, we want the state changes to be seen
            # in both lists.
            self.done_order = self.ir_order.copy()
            return

        raise ValueError("Graph not \'make\'d!")

    def get_next_ir(self):
        if self.done_order:
            if len(self.done_order) > 0:
                return self.done_order[0]
            return None
        raise ValueError("Graph not \'make\'d!")

    def mark_ir_as_done(self, ir: IR):
        if self.dag:
            raise ValueError("Graph not \'make\'d!")

        if ir in self.v:
            ir.set_state(IR_STATE.IR_DONE)
            if self.done_order:
                if ir in self.done_order:
                    self.done_order.remove(ir)
                return
            raise ValueError("Graph not \'order\'ed!")

    def mark_ir_as_not_done(self, ir: IR, state: IR_STATE):
        assert state != IR_STATE.IR_DONE

        if not hasattr(self, 'dag'):
            raise ValueError("Graph not \'make\'d!")

        if ir in self.v:
            ir.set_state(state)
            if hasattr(self, 'done_order'):
                if ir not in self.done_order:
                    self.done_order = [ir] + self.done_order
                return
            raise ValueError("Graph not \'order\'ed!")

    def set_ir_state(self, ir: IR, state: IR_STATE):
        if state == IR_STATE.IR_DONE:
            self.mark_ir_as_done(ir)
        else:
            self.mark_ir_as_not_done(ir, state)

    def set_state(self, state: DAG_STATE):
        self.state = state

    def dag_is_done(self):
        return all([ir.is_done() for ir in self.v])

    def set_ir_state_by_id(self, ir_id: int, state: IR_STATE):
        for ir in self.v:
            if ir.uid == ir_id:
                self.set_ir_state(ir, state)


class Datapath:
    def __init__(self, dp_id: int, state: SW_STATE, ofproto: int):
        self.dp_id = dp_id
        self.state = state
        self.ofproto = ofproto

        self.ir_set = set()
        self.sched_ir_set = set()
        self.roles = dict()

    def get_dict(self, include_role=False):
        dp_dict = {
            'dp_id': self.dp_id,
            'state': self.state,
            'ofproto': self.ofproto,
            'sched_ir': [ir.uid for ir in self.sched_ir_set],
            'roles': self.roles
        }

        if not include_role:
            dp_dict.pop('roles')
        return dp_dict

    def add_ir(self, ir: IR):
        self.ir_set.add(ir)

    def add_irs(self, irs: Set[IR]):
        self.ir_set.union(irs)

    def set_ir_set(self, ir_set: Set[IR]):
        self.ir_set = ir_set

    def set_sched_ir_set(self, sched_ir_set: Set[IR]):
        self.sched_ir_set = sched_ir_set

    def set_role(self, identity, role: OFC_ROLE = None):
        if not role:
            role = OFC_ROLE.ROLE_UNKNOWN
        self.roles[identity] = role.name


class UIDWithCookie:
    def __init__(self, uid, cookie, type):
        self.uid = uid
        self.cookie = cookie
        self.type = type

    def __eq__(self, other):
        if isinstance(other, UIDWithCookie):
            return self.uid == other.uid
        elif isinstance(other, bson.ObjectId):
            return self.uid == other
        return id(self) == id(other)

    def __hash__(self):
        return self.uid.__hash__()