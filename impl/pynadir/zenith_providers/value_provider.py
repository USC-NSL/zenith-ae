import random
import pymongo
from threading import Condition

import pymongo.errors
from pymongo.client_session import ClientSession
from pynadir.providers import AbstractProvider
from pynadir.structures import *
from pynadir.zenith_providers.uid import *
from pynadir.exceptions import ExecutionHalted, RepeatLabel, GreedyAccessDomainError, WaitThenRepeat

import nib.nib_settings
from nib.nib_defs import NIBBase
from nib.nib_nuke import nuke_db


NADIR_DB_NAME = "Nadir"


class MongoProvider(NIBBase, AbstractProvider):
    """
    This extends the original Zenith NIB provider, with the definitions
    of Nadir's AbstractProvider, so it can also be used for Nadir processes
    without having to rewrite the NIB for them.

    The main goal of this provider is to cleanly convert Python values into
    BSON and vice versa, while also taking into account how to use them
    with Nadir.
    The detail are given when needed.
    """

    NADIR_CV_COLLECTION = "NADIR_CVS"
    """The collection where we keep all CVs on the Nadir database"""

    CV_TIMEOUT_MIN = 0.2
    """
    To implement `await` statement in a manner that is somewhat agnostic
    to the specification, we essentially poll the document associated with
    a CV to see what is happening to it.
    This value dictates the minimum time the database will wait before returning
    and telling the process to re-evaluate the operator within its `await` statement.
    The smaller this value, the higher the rate of requests to the database, thus
    it should be carefuly chosen.
    """

    CV_MAX_BACKOFF = 4
    """
    It is best for `await` statements to have a backoff, otherwise, Nadir processes
    will not idle out when nothing is happening. We do exponential backoff by default
    and cap it to this value.
    """

    P_WAKEUP = 0.05
    """
    The probability that a commit wakes up any sleeping process.
    See issue #14 to see why this may have benefits.
    The closer this value to 1.0, the tighter the tail latency of
    operations get, however, it also puts a huge pressure on the
    database to handle this many requests.
    """

    class BSONTypes:
        INT = "int"       # Directly convertable into Python integers
        STR = "str"       # Directly convertable into Python strings
        OBJ = "obj"       # These are Mongo documents (perhaps embedded), made from unwrapped dicts
        ARR = "arr"       # Directly convertable into Python lists or sets
        NIL = "nil"       # Directly convertable into Python `None`

    def __init__(self, path: str = nib.nib_settings.LOCAL_PATH):
        super().__init__(path, db_name=NADIR_DB_NAME)
        self._updates: Dict[NadirPID, Dict[str, List[Tuple[NadirAddress, Any]]]] = dict()
        self._collections = set()
        self._functions = set()
        self._cvs = dict()
        self._cv_backoffs = dict()
        self._tokens = dict()
        self._constant_values = dict()

    def is_global(self) -> bool:
        return True

    @staticmethod
    def nuke():
        """Drop the `Nadir` database. Never touches `NIB` or any other database."""
        nuke_db(db_name=NADIR_DB_NAME)

    def register_pid(self, pid: NadirPID):
        assert pid not in self._updates

        """
        Each Nadir process must introduce itself to the provider. This is needed
        in order to know who to wakeup when condition variables are signaled.
        """

        self._updates[pid] = dict()       # Queued updates from this PID, awaiting commits
        self._tokens[pid] = dict()        # Resume tokens, for watching CVs

    def register_cv(self, pids: FrozenSet[NadirPID], cv: Condition, index: int):
        assert cv not in self._cvs
        assert isinstance(pids, frozenset)

        """
        The CV entry in Mongo is created by taking the hash of the `frozenset`
        of PIDs and the index in string format, and create an entry for it that
        has a `true` or `false` value.

        If the value is `true`, then a thread is waiting on it, and every commit
        will set it to `false` and wake the instance up.
        """

        cv_name = str(abs(hash(pids))) + str(index)
        self._cvs[cv] = (pids, index, cv_name)
        self._cv_backoffs[cv] = 0
        for pid in pids:
            # Get some resume token to start from
            self._tokens[pid][cv] = self.get_resume_token(self.NADIR_CV_COLLECTION)
        self.update_document(
            self.NADIR_CV_COLLECTION, filter={'name': cv_name}, 
            update={'$set': {'waiting': False}}, upsert=True
        )
    
    def get_cv_timeout(self, cv: Condition) -> float:
        return self.CV_TIMEOUT_MIN * (2 ** self._cv_backoffs[cv])
    
    def backoff_cv(self, cv: Condition):
        self._cv_backoffs[cv] = min(self._cv_backoffs[cv]+1, self.CV_MAX_BACKOFF)
    
    def reset_cv_backoff(self, cv: Condition):
        self._cv_backoffs[cv] = 0
    
    def do_transaction(self, callback: Callable, wc=None, session=None, **callback_kwargs):
        if session is None:
            with self.client.start_session() as session:
                return session.with_transaction(
                    lambda s: callback(s, **callback_kwargs), write_concern=wc
                )
        return session.with_transaction(
            lambda s: callback(s, **callback_kwargs), write_concern=wc
        )

    def get_document_count(self, collection: str):
        return self.db[collection].count_documents(filter={})

    def _as_bson_type(self, value: Any):
        """
        Convert any Python/Nadir value, into a BSON-friendly type.
        """

        if isinstance(value, int):
            return {
                '_bson_type': self.BSONTypes.INT, 
                'value': value
            }
        elif isinstance(value, str):
            return {
                '_bson_type': self.BSONTypes.STR, 
                'value': value
            }
        elif isinstance(value, list):
            return {
                '_bson_type': self.BSONTypes.ARR,
                'value': [self._as_bson_type(val) for val in value]
            }
        elif isinstance(value, dict):
            """
            There are a two cases here:
                - If the dict has any of '_nadir_type', '_is_set' and '_class_name'
                  keys set for it, then we should not touch it.
                - If it does not, then we should unwrap it.
            """

            if dict_has_nadir_type(value):
                return value
            return [{
                '_bson_type': self.BSONTypes.OBJ,
                'key': self._as_bson_type(key),
                'value': self._as_bson_type(value)
            } for key, value in value.items()]
        elif isinstance(value, tuple):
            """
            Tuples happen when the json doc is unwrapping a map.
            So the first item is the key, and the other is the value.
            """
            assert len(value) == 2

            return {
                '_bson_type': self.BSONTypes.OBJ,
                'key': self._as_bson_type(value[0]),
                'value': self._as_bson_type(value[1])
            }
        elif value is None:
            return {'_bson_type': self.BSONTypes.NIL}
        else:
            raise ValueError
        
    def _from_bson_type(self, value: Any):
        """
        This converts a document loaded from Mongo into a Python/Nadir
        type that we can use directly.
        """

        if isinstance(value, dict):
            tpe = value.get('_bson_type')
            if tpe is None:
                assert dict_has_nadir_type(value)
                return value
            
            if tpe == self.BSONTypes.INT:
                return value['value']
            elif tpe == self.BSONTypes.STR:
                return value['value']
            elif tpe == self.BSONTypes.ARR:
                return [self._from_bson_type(item) for item in value['value']]
            elif tpe == self.BSONTypes.OBJ:
                return (
                    self._from_bson_type(value['key']),
                    self._from_bson_type(value['value'])
                )
            elif tpe == self.BSONTypes.NIL:
                return None
            else:
                raise ValueError
        elif isinstance(value, list):
            """
            We will receive a list in the case that we had unwrapped
            a dict that had no nadir type value attached to it. So
            essentially, we need to loop on each member, get the json
            value and then cast it to a dict.
            """
            return dict([self._from_bson_type(item) for item in value])
        else:
            raise ValueError
        
    def from_nadir_to_bson(self, value: Any, is_function: bool):
        json_doc = from_nadir_type(value)
        if is_function:
            assert json_doc["_is_map"]
            return [self._as_bson_type(item) for item in json_doc["value"]]
        return self._as_bson_type(json_doc)
    
    def as_nadir_from_bson(self, value: Any, is_function_element: bool):
        if isinstance(value, dict):
            json_doc = self._from_bson_type(value)
            if is_function_element:
                return as_nadir_type({
                    '_is_map': True,
                    'value': [json_doc]
                })
            else:
                return as_nadir_type(json_doc)
        elif isinstance(value, list):
            """
            The ONLY time where we get a list is when we have requested an
            entire function, in which case this is a list of function elements which
            are just tuples.
            We need to return the '_is_map' value and make a dict.
            """

            return as_nadir_type({
                '_is_map': True,
                'value': [self._from_bson_type(item) for item in value]
            })
        else:
            print(f"GOT {value}")
            raise ValueError

    def _add_value_transaction(self, session, name: str, value: Any, is_function: bool):
        # First, is there a collection with this name that is not empty?
        if self.query_one_document(name, filter={}, session=session):
            # Yes, nothing to do then
            return

        # There is no such collection, create it
        docs = self.from_nadir_to_bson(value, is_function)
        if isinstance(docs, list):
            self.insert_documents(name, docs, session=session)
        elif isinstance(docs, dict):
            self.insert_document(name, docs, session=session)
        else:
            raise ValueError

        # TODO: We need to fix this at some point, it's not good
        # # If this is a function, create a unique index on the `key` field
        # self.create_unique_index(name, 'key')

    def add_value(self, name: str, value: Any, *args, **kwargs):
        assert name not in self._collections
        assert 'is_function' in kwargs
        assert isinstance(kwargs['is_function'], bool)
        assert 'is_constant' in kwargs
        assert isinstance(kwargs['is_constant'], bool)

        self._collections.add(name)
        is_function = kwargs['is_function']
        is_constant = kwargs['is_constant']

        if is_function:
            self._functions.add(name)

        # if value is None:
        #     return

        if is_constant:
            self._constant_values[name] = value
        
        # Open a transaction and insert the value
        self.do_transaction(self._add_value_transaction, name=name, value=value, is_function=is_function)

    def register_value(self, name: str, *args, **kwargs):
        assert name not in self._collections
        assert 'is_function' in kwargs
        assert isinstance(kwargs['is_function'], bool)
        assert 'is_constant' in kwargs
        assert isinstance(kwargs['is_constant'], bool)

        self._collections.add(name)
        is_function = kwargs['is_function']
        is_constant = kwargs['is_constant']

        if is_function:
            self._functions.add(name)

        if is_constant:
            if 'value' in kwargs:
                value = kwargs['value']
            else:
                raise ValueError
            self._constant_values[name] = value
    
    def get_value(self, name: str, pid: NadirPID = None, address: NadirAddress = None, session: ClientSession = None):
        # Are we requesting a constant?
        if name in self._constant_values:
            res = self._constant_values[name]
            if res is not None:
                return self._get_addressed_value(res, address)
            else:
                raise ValueError(f"Constant value {name} is not cached!")

        # Are we requesting an uncommitted value?
        if \
        pid is not None and \
        pid in self._updates and \
        name in self._updates[pid]:
            # print(f"Requesting uncommitted value for {name} at address: {address}")
            for update_addr, value in self._updates[pid][name]:
                if self._address_is_subset_of(update_addr, address):
                    subtracted_address = self._get_subtracted_address(update_addr, address)
                    return self._get_addressed_value(value, subtracted_address)

        # No, query the database
        if name in self._functions:
            if address is not None and len(address) > 0:
                function_key = self.from_nadir_to_bson({address[0]: 1}, True)[0]['key']
                # print(f"Requesting function value {name} at key: {str(function_key)}")
                res = self.query_one_document(name, filter={'key': function_key}, session=session)
            else:
                # print(f"Requesting total function value for {name}")
                res = list(self.query_document(name, filter={}, session=session))
        else:
            # print(f"Requesting non-function value for {name}")
            res = self.query_one_document(name, filter={}, session=session)
        
        if res is None and name in self._functions:
            if address is not None:
                function_key = self.from_nadir_to_bson({address[0]: 1}, True)[0]['key']
                raise GreedyAccessDomainError(f"No value associated with key {function_key} for function {name}")
            else:
                raise GreedyAccessDomainError(f"Function {name} is empty!")
        if res is None:
            raise RuntimeError(f"Query of collection {name} returned None. The collection is empty!")
        
        if \
        name in self._functions and \
        address is not None and \
        len(address) > 0:
            doc = self.as_nadir_from_bson(res, True)
        else:
            doc = self.as_nadir_from_bson(res, False)
        
        if address is None or len(address) == 0:
            return doc
        else:
            return self._get_addressed_value(doc, address)
    
    def set_value(self, pid: NadirPID, name: str, value: Any, address: NadirAddress = None):
        """
        This just queues the updates, it will not actually set any value until
        we actually need to commit.
        """

        assert name not in self._constant_values

        if name not in self._updates[pid]:
            self._updates[pid][name] = list()
        self._updates[pid][name].append((address, value))

    def domain(self, name: str, address: NadirAddress = None):
        assert name in self._functions
        assert address is None

        return set(self.as_nadir_from_bson(item['key'], is_function_element=False) for item in self.query_document(name, filter={}, projection={'key': True}))
    
    def abort(self, pid):
        self._updates[pid].clear()

    def _replace_function(self, name: str, value: Any, session: ClientSession):
        docs = self.from_nadir_to_bson(value, True)
        self.insert_documents(name, docs, session=session)
        
    def _replace_value(self, name: str, value: Any, session: ClientSession):
        doc = self.from_nadir_to_bson(value, False)
        self.update_document(name, filter={}, update={'$set': doc}, session=session)

    def _update_function(self, name, pid, address, value, session: ClientSession):
        assert address is not None
        if len(address) > 1:
            current_value = self.get_value(name, pid=pid, address=[address[0]], session=session)
            self._set_addressed_value(current_value, address[1:], value)
            self.update_document(
                name, filter={'key': self.from_nadir_to_bson({address[0]: 1}, True)[0]['key']},
                update={
                    '$set': {
                        'value': self.from_nadir_to_bson(current_value, False)
                    }
                },
                session=session
            )
        else:
            self.update_document(
                name, filter={'key': self.from_nadir_to_bson({address[0]: 1}, True)[0]['key']},
                update={
                    '$set': self.from_nadir_to_bson({address[0]: value}, True)[0]
                }, upsert=True, session=session
            )

    def _update_value(self, name, pid, address, value, session: ClientSession):
        current_value = self.get_value(name, pid=pid)
        if current_value is not None:
            self._set_addressed_value(current_value, address, value)
            self.update_document(
                name, filter={}, update={'$set': self.from_nadir_to_bson(current_value, False)},
                session=session
            )
        else:
            self.insert_document(name, self.from_nadir_to_bson(value, False), session=session)
    
    def _is_function_replace(self, pid: NadirPID) -> Optional[str]:
        if len(self._updates[pid]) > 0:
            for name, updates in self._updates[pid].items():
                for address, _ in updates:
                    if address is None or len(address) == 0:
                        if name in self._functions:
                            """
                            LIMITATION: If we are doing a function replace, then this MUST be 
                                        the ONLY update that we do under the current label ...
                            """
                            if len(self._updates[pid]) > 1 or len(updates) > 1:
                                raise NotImplementedError
                            print(f"FUNCTION REPLACE ON {name}")
                            return name
        return None

    def _push(self, pid: NadirPID, session: ClientSession):
        for name, updates in self._updates[pid].items():
            for address, value in updates:
                if address is None or len(address) == 0:
                    if name in self._functions:
                        """
                        Replacing an entire function.
                        """
                        self._replace_function(name, value, session)
                    else:
                        """
                        Replacing an entire value.
                        """
                        self._replace_value(name, value, session)
                else:
                    if name in self._functions:
                        """
                        We are updating a particular function entry or adding a new one.
                        So this should be an upsert operation.
                        """
                        self._update_function(name, pid, address, value, session)
                    else:
                        """
                        We are updating a particular part of a data structure
                        """
                        self._update_value(name, pid, address, value, session)

    def commit(self, pid):
        # Anything to do?
        if len(self._updates[pid]) == 0:
            return

        # Update your resume tokens
        _token = self.get_resume_token(self.NADIR_CV_COLLECTION)
        for _cv in self._tokens[pid]:
            self._tokens[pid][_cv] = _token

        # Submit updates
        try:
            replaced_function = self._is_function_replace(pid)
            if replaced_function is not None:
                self.drop_collection(replaced_function)
            with self.client.start_session() as session:
                with session.start_transaction(write_concern=nib.nib_settings.DEFAULT_WRITE_CONCERN):
                    replaced_function = self._push(pid, session)
        except pymongo.errors.OperationFailure:
            # Transaction failed. Wait, then repeat!
            raise WaitThenRepeat(1.0)
        finally:
            self._updates[pid].clear()

        # Signal changes if you can
        if random.random() < self.P_WAKEUP:
            self.update_documents(
                self.NADIR_CV_COLLECTION, filter={'waiting': True},
                update={'$set': {'waiting': False}}
            )
    
    def _wait_transaction(self, session, pid: NadirPID, cv: Condition, condition_function: Callable[..., bool]) -> Optional[ObjectId]:
        # Get the CV name
        (pids, _, cv_name) = self._cvs[cv]
        assert pid in pids

        # Is the condition already true?
        if condition_function(self):
            # It is, wakeup anyone that might be sleeping on the cv
            self.update_document(self.NADIR_CV_COLLECTION, filter={'name': cv_name, 'waiting': True}, 
                                 update={'$set': {'waiting': False}}, session=session)
            self.reset_cv_backoff(cv)
            return None
        else:
            # No. Go to sleep and wait until you are woken up
            self.update_document(self.NADIR_CV_COLLECTION, filter={'name': cv_name, 'waiting': False}, 
                                 update={'$set': {'waiting': True}}, session=session)
            return self.query_one_document(self.NADIR_CV_COLLECTION, filter={'name': cv_name}, session=session)['_id']
    
    def wait(self, pid: NadirPID, cv: Condition, condition_function: Callable[..., bool], *args, **kwargs):
        # First, before doing anything, is global exit flag set?
        if not NadirGlobalParams.is_active:
            raise ExecutionHalted
        
        # This is critical section start, so start a transaction
        res = self.do_transaction(self._wait_transaction, pid=pid, cv=cv, condition_function=condition_function)
        if not res:
            # Free to move forward!
            return
        else:
            # Must wait
            (_, token) = self.watch_document(
                _id=res, collection=self.NADIR_CV_COLLECTION, state_name='waiting',
                desired_state=False, timeout=self.get_cv_timeout(cv), token=self._tokens[pid][cv]
            )
            
            if not NadirGlobalParams.is_active:
                raise ExecutionHalted
            
            if token:
                self._tokens[pid][cv] = token
            self.backoff_cv(cv)
            raise RepeatLabel
            
    """
    This provider is NOT responsible for any of these calls.
    """
    def fifo_pop(self, pid: NadirPID, queue_name: str):
        raise NotImplementedError
    def fifo_peek(self, pid: NadirPID, queue_name: str) -> Any:
        raise NotImplementedError
    def fifo_put(self, pid: NadirPID, queue_name: str, msg):
        raise NotImplementedError
    def fifo_peek_nb(self, pid: NadirPID, queue_name: str) -> Any:
        raise NotImplementedError
    def fifo_get(self, pid: NadirPID, queue_name: str) -> Any:
        raise NotImplementedError
    def ack_queue_ack(self, pid: NadirPID, queue_name: str):
        raise NotImplementedError
    def ack_queue_put(self, pid: NadirPID, queue_name: str, msg):
        raise NotImplementedError
    def ack_queue_get(self, pid: NadirPID, queue_name: str) -> Any:
        raise NotImplementedError
    def fanout_fifo_put(self, pid: NadirPID, queue_name: str, destination, msg):
        raise NotImplementedError
