import sys
import queue
from abc import ABC, abstractmethod
from threading import Condition
from typing import Any, List, Callable, Dict, Tuple, FrozenSet
from pynadir.exceptions import ExecutionHalted, RepeatLabel
from pynadir.params import NadirGlobalParams
from pynadir.structures import NadirStructBase, NadirPID, HasDomain, NadirType, NadirAddress
from pynadir.utils.logging import TitledLog


class AbstractProvider(ABC):
    @property
    @abstractmethod
    def is_global(self) -> bool:
        pass

    @staticmethod
    def _get_addressed_value(start, address: NadirAddress):
        if address is not None:
            for addr in address:
                try:
                    start = start[addr]
                except KeyError:
                    TitledLog.fail("provider", f"Address error for {[str(item) for item in address]} with value: {start}")
                    raise ValueError
        if isinstance(start, set):
            return frozenset(start)
        return start

    @staticmethod
    def _set_addressed_value(start, address: NadirAddress, value: Any):
        assert address is not None and len(address) > 0
        for addr in address[:-1]:
            start = start[addr]
        if isinstance(start, NadirStructBase):
            start.update(address[-1], value)
        else:
            start[address[-1]] = value

    @staticmethod
    def _address_is_subset_of(short_address: NadirAddress, long_address: NadirAddress) -> bool:
        if short_address is None:
            res = True
            # return True
        elif short_address is not None and long_address is not None:
            short_len = len(short_address)
            if long_address[:short_len] == short_address:
                res = True
                # return True
            else:
                res = False
            # return False
        else:
            res = False
        # return False
        # print(f"{long_address} is subset of {short_address} --> {res}")
        return res

    @staticmethod
    def _get_subtracted_address(short_address: NadirAddress, long_address: NadirAddress) -> NadirAddress:
        if long_address is None:
            return None
        else:
            if short_address is None:
                return long_address
            else:
                return long_address[len(short_address):]

    @abstractmethod
    def add_value(self, name: str, value: Any, *args, **kwargs):
        """
        Register a variable with a given name under this provider.
        The provider will use this to initiate an entry for the
        variable as required.
        """
        pass

    @abstractmethod
    def register_value(self, name: str, *args, **kwargs):
        """
        Make a variable known to the provider, without actually initializing
        it; instead it assumes that somewhere else, this has been handled.
        Useful for databases in particular.
        """
        pass

    @abstractmethod
    def register_cv(self, pids: FrozenSet[NadirPID], cv: Condition, index: int):
        """
        Register the condition variable associated with an `await`
        statement which must be passed to `wait` to wake up the
        thread.
        """
        pass

    @abstractmethod
    def register_pid(self, pid: NadirPID):
        """
        Register the `NadirPID` of the process that is attached to
        this provider.
        """
        pass

    @abstractmethod
    def get_value(self, name: str, pid: NadirPID = None, address: NadirAddress = None) -> Any:
        """
        Given the name of a variable and the address of the required 
        part of it, retrieve the current value of it.
        If a value has uncommitted changes, the return value MUST
        reflect these changes as well.
        """
        pass

    @abstractmethod
    def set_value(self, pid: NadirPID, name: str, value: Any, address: NadirAddress = None):
        """
        Set the addressed value of a variable. This creates an
        uncommitted update for this variable that must be committed
        later by calling `commit`.
        """
        pass

    @abstractmethod
    def fifo_peek(self, pid: NadirPID, queue_name: str) -> Any:
        """Read (and tag) the head of a FIFO or block"""
        pass

    @abstractmethod
    def fifo_peek_nb(self, pid: NadirPID, queue_name: str) -> Any:
        """Read (and tag) the head of a FIFO. Move on if empty ..."""
        pass

    @abstractmethod
    def fifo_pop(self, pid: NadirPID, queue_name: str):
        """Remove (i.e. ACK) the head of a FIFO"""
        pass

    @abstractmethod
    def fifo_get(self, pid: NadirPID, queue_name: str) -> Any:
        """Get (i.e. peek + pop) and item from a FIFO"""
        pass

    @abstractmethod
    def fifo_put(self, pid: NadirPID, queue_name: str, msg):
        """Put an item on a FIFO"""
        pass

    @abstractmethod
    def ack_queue_get(self, pid: NadirPID, queue_name: str) -> Any:
        """Fetch and tag an item from a queue"""
        pass

    @abstractmethod
    def ack_queue_put(self, pid: NadirPID, queue_name: str, msg):
        """Put an untagged item on the queue"""
        pass

    @abstractmethod
    def ack_queue_ack(self, pid: NadirPID, queue_name: str):
        """ACK an item on the queue"""
        pass

    @abstractmethod
    def fanout_fifo_put(self, pid: NadirPID, queue_name: str, destination, msg):
        """Put an item on a fanout queue to a particular destination"""
        pass

    @abstractmethod
    def domain(self, name: str, address: NadirAddress = None):
        """
        Return the domain of the function that is identified with
        given name and address.
        """
        pass

    @abstractmethod
    def commit(self, pid: NadirPID):
        """
        Commit all outstanding changes.
        """
        pass

    @abstractmethod
    def abort(self, pid: NadirPID):
        """
        Discard all outstanding changes.
        """
        pass

    @abstractmethod
    def wait(self, pid: NadirPID, cv: Condition, condition_function: Callable[..., bool], *args, **kwargs):
        """
        Evaluate the condition function. As long as it is false, go to 
        sleep. Wake either if there is an error, or if the condition is
        satisfied.
        """
        pass


"""
The following defines the `simple` queue and value provider.
These are designed for pure local execution (i.e. you just want
to see how the algorithm executes without wanting to bother
actually implementing remote variable/queue access).
"""


class NadirSimpleQueue(NadirType):
    MAX_SIZE = 1024
    TIMEOUT = 1

    def __init__(self, items: List[Any] = None) -> None:
        self._queue = queue.Queue(maxsize=self.MAX_SIZE)

        if items:
            for item in items:
                self._queue.put_nowait(item)

    def peek(self, nonblocking=False) -> Any:
        """
        Simple queues do not implement a `true` peek method.
        Essentially, they cannot function as legitimate ACK
        queues, since if the calling process dies, the queue
        is destroyed with it as well.
        """
        while NadirGlobalParams.is_active:
            try:
                return self._queue.get(timeout=self.TIMEOUT)
            except queue.Empty:
                if nonblocking:
                    return None
                pass
        
        # Just exit immediately if the program is done
        sys.exit(0)
    
    def put(self, item: Any):
        while NadirGlobalParams.is_active:
            try:
                self._queue.put(item, timeout=self.TIMEOUT)
                return
            except TimeoutError:
                pass
        
        # Just exit immediately if the program is done
        sys.exit(0)

    def pop(self):
        """
        This should ACK the message and let the queue remove it
        completely. This simple queue does not do such a thing.
        """
        pass

    """
    Serializing a queue would be a step too far for being `simple`!
    """
    
    def json(self):
        raise ValueError
    
    @classmethod
    def from_json(cls, d: Dict):
        raise ValueError


class NadirSimpleProvider(AbstractProvider):
    AWAIT_TIMEOUT = 5

    def __init__(self, data: Dict = None):
        # Map CVs to a dict of callable condition functions for each PID
        self._events: Dict[Condition, Dict[NadirPID, Callable]] = dict()

        # Map a PID, to a dict of updates to be committed
        self._updates: Dict[NadirPID, Dict[str, List[Tuple[NadirAddress, Any]]]] = dict()

        if data:
            self._dict = data.copy()
        else:
            self._dict = dict()

    def is_global(self) -> bool:
        return False

    def add_value(self, name: str, value: Any, *args, **kwargs):
        assert name not in self._dict
        self._dict[name] = value

    def register_value(self, name: str, *args, **kwargs):
        pass
    
    def get_value(self, name: str, pid: NadirPID = None, address: NadirAddress = None):
        if \
        pid is not None and \
        pid in self._updates and \
        name in self._updates[pid]:
            for update_addr, value in self._updates[pid][name]:
                if self._address_is_subset_of(update_addr, address):
                    subtracted_address = self._get_subtracted_address(update_addr, address)
                    return self._get_addressed_value(value, subtracted_address)

        return self._get_addressed_value(self._dict[name], address)
    
    def set_value(self, pid: NadirPID, name: str, value: Any, address: NadirAddress = None):
        if name not in self._updates[pid]:
            self._updates[pid][name] = list()
        self._updates[pid][name].append((address, value))
        # print(f"Local update queued: {name}.{address} <-- {value}")

    def put_message(self, pid: NadirPID, queue_name: str, msg):
        q = self.get_value(queue_name, address=[])
        assert isinstance(q, NadirSimpleQueue)
        q.put(msg)

    def pop_message(self, pid: NadirPID, queue_name: str):
        q = self.get_value(queue_name, address=[])
        assert isinstance(q, NadirSimpleQueue)
        q.pop()

    def peek_message(self, pid: NadirPID, queue_name: str, nonblocking: bool = False):
        q = self.get_value(queue_name, address=[])
        assert isinstance(q, NadirSimpleQueue)
        return q.peek(nonblocking=nonblocking)

    def fifo_peek(self, pid: NadirPID, queue_name: str):
        return self.peek_message(pid, queue_name)
    def fifo_peek_nb(self, pid: NadirPID, queue_name: str):
        return self.peek_message(pid, queue_name, nonblocking=True)
    def fifo_pop(self, pid: NadirPID, queue_name: str):
        self.pop_message(pid, queue_name)
    def fifo_put(self, pid: NadirPID, queue_name: str, msg):
        self.put_message(pid, queue_name, msg)
    def fifo_get(self, pid: NadirPID, queue_name: str) -> Any:
        return self.peek_message(pid, queue_name)
    def ack_queue_get(self, pid: NadirPID, queue_name: str):
        return self.peek_message(pid, queue_name)
    def ack_queue_ack(self, pid: NadirPID, queue_name: str):
        self.pop_message(pid, queue_name)
    def ack_queue_put(self, pid: NadirPID, queue_name: str, msg):
        self.put_message(pid, queue_name, msg)
    def fanout_fifo_put(self, pid: NadirPID, queue_name: str, destination, msg):
        self.put_message(pid, queue_name, {
            '$destination': destination,
            '$message': msg
        })
    
    def domain(self, name: str, address: NadirAddress = None):
        value = self.get_value(name, address=address)
        if isinstance(value, tuple):
            return range(len(value))
        elif isinstance(value, HasDomain):
            return value.domain
        elif isinstance(value, NadirSimpleQueue):
            raise ValueError
        else:
            return value.keys()

    @staticmethod
    def _signal_condition(cond: Condition, func: Callable) -> bool:
        cond.notify_all()
        return True
    
    def register_pid(self, pid: NadirPID):
        assert pid not in self._updates
        self._updates[pid] = dict()

    def register_cv(self, pids: FrozenSet[NadirPID], cv: Condition, index: int):
        assert cv not in self._events
        self._events[cv] = dict()

    def _push(self, pid):
        for name, updates in self._updates[pid].items():
            for address, value in updates:
                if address is None or len(address) == 0:
                    # print(f"Committing change: {name} <-- {value}")
                    self._dict[name] = value
                else:
                    # print(f"Committing change: {name}.{address} <-- {value}")
                    self._set_addressed_value(self._dict[name], address, value)
        
        self._updates[pid].clear()

    def commit(self, pid):
        # Anything to do?
        if len(self._updates[pid]) == 0:
            return

        # Submit updates
        self._push(pid)

        # Signal changes
        for cv in self._events:
            if cv.acquire(blocking=False):
                self._events[cv] = {
                    k: f for k, f in self._events[cv].items() if not self._signal_condition(cv, f)
                }
                cv.release()

    def abort(self, pid):
        self._updates[pid].clear()

    def _evaluate_condition_function(self, condition_function: Callable[..., bool]) -> bool:
        return condition_function(self)

    def wait(self, pid: NadirPID, cv: Condition, condition_function: Callable[..., bool], *args, **kwargs):
        """
        This implements a TLA+ `await` statement.
        Each of these statements has a dedicated condition variable
        associated with it during the creation of the IR-AST from
        Nadir, and the code will decide how to pass it.

        Within the body of this code, the lock is acquired, and
        it is then released only at the end of the current step.
        The only exception here is the case where the system has
        a global exit flag set for it, in which case the lock is
        released, or if a timeout happens.

        The timeout is optional, but we add it to make sure that
        the user is able to interrupt the execution at any moment
        if they see fit to do that, even if it might cause the
        algorithm to break.
        """

        # First, before doing anything, is global exit flag set?
        if not NadirGlobalParams.is_active:
            raise ExecutionHalted

        # Now, acquire the lock for the current await
        cv.acquire()

        # Is the guard clause already satisfied?
        if self._evaluate_condition_function(condition_function):
            # Clear the current event for the CV
            self._events[cv].pop(pid, None)
            # Return, but do NOT release the lock.
            return
        else:
            # No, go to sleep and let other threads queue up
            self._events[cv][pid] = condition_function
            if cv.wait(self.AWAIT_TIMEOUT):
                # Woken up! Reevaluate the current step
                cv.release()
                raise RepeatLabel
            else:
                if not NadirGlobalParams.is_active:
                    # Time to exit! Wakeup everyone and return
                    if cv._lock.locked():  # noqa
                        cv.notify_all()
                    raise ExecutionHalted
                # Timeout, reevaluate the label
                cv.release()
                raise RepeatLabel


# TODO: This should use a simple SQL-like database, any simple thing would do ...

class NadirModuleProvider(NadirSimpleProvider):
    AWAIT_TIMEOUT = 1

    def put_message(self, pid: NadirPID, queue_name: str, msg):
        raise ValueError("You should never use this!")
    def pop_message(self, pid: NadirPID, queue_name: str):
        raise ValueError("You should never use this!")
    def peek_message(self, pid: NadirPID, queue_name: str, nonblocking: bool = False):
        raise ValueError("You should never use this!")
    def fifo_peek(self, pid: NadirPID, queue_name: str):
        raise ValueError("You should never use this!")
    def fifo_peek_nb(self, pid: NadirPID, queue_name: str):
        raise ValueError("You should never use this!")
    def fifo_pop(self, pid: NadirPID, queue_name: str):
        raise ValueError("You should never use this!")
    def fifo_put(self, pid: NadirPID, queue_name: str, msg):
        raise ValueError("You should never use this!")
    def fifo_get(self, pid: NadirPID, queue_name: str) -> Any:
        raise ValueError("You should never use this!")
    def ack_queue_get(self, pid: NadirPID, queue_name: str):
        raise ValueError("You should never use this!")
    def ack_queue_ack(self, pid: NadirPID, queue_name: str):
        raise ValueError("You should never use this!")
    def ack_queue_put(self, pid: NadirPID, queue_name: str, msg):
        raise ValueError("You should never use this!")
    def fanout_fifo_put(self, pid: NadirPID, queue_name: str, destination, msg):
        raise ValueError("You should never use this!")

    def nuke(self):
        self._events.clear()
        self._dict.clear()
        self._updates.clear()
