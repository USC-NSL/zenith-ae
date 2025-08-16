from threading import Condition
from typing import Any, Callable, FrozenSet, List, Set, Dict
from pynadir.structures import NadirPID, NadirUID, NadirAddress
from pynadir.providers import AbstractProvider, NadirModuleProvider
from pynadir.zenith_providers.value_provider import MongoProvider
from pynadir.zenith_providers.queue_provider import RabbitProvider
from pynadir.zenith_providers.uid import *
from pynadir.zenith_providers.mongo_provider import ReadOnlyMongoProvider


class ZenithProvider(AbstractProvider):
    def __init__(self, nib_db_name=None, tracked_collections: Set[str] = None) -> None:
        self.value_provider = MongoProvider()
        self.queue_provider = RabbitProvider()
        self._module_provider = NadirModuleProvider()
        
        self._tracked_collections: Set[str] = set()
        self._module_level_values: Set[str] = set()
        self._collection2id: Dict[str, int] = {}
        self._id2collection: Dict[int, str] = {}

        self.queue_names = set()

        if nib_db_name:
            self.nib_read_only_provider = ReadOnlyMongoProvider(nib_db_name)
            if tracked_collections:
                for collection_name in tracked_collections:
                    self.track_collection(collection_name)
        else:
            assert tracked_collections is None or len(tracked_collections) == 0
            self.nib_read_only_provider = None

    def is_global(self) -> bool:
        return True
    
    def _update_tracked_collection_mapping(self):
        # First, insert all of your collections
        for collection_name in self._tracked_collections:
            self.value_provider.update_document(
                NADIR_UID_COLLECTION_MAP, filter={'name': collection_name},
                update={'$set': {'name': collection_name}}, upsert=True
            )
        
        # Second, get all the tracked collections
        docs = self.value_provider.query_document(
            NADIR_UID_COLLECTION_MAP, {}
        )
        for doc in docs:
            lsb_id = int.from_bytes(doc['_id'].binary[-4:], 'big')
            
            assert doc['name'] in self._tracked_collections
            assert lsb_id not in self._id2collection

            self._collection2id[doc['name']] = lsb_id
            self._id2collection[lsb_id] = doc['name']
    
    def track_collection(self, name: str):
        """
        Instruct this provider to track a collection in the `NIB` database.
        Doing this, allows this provider to retrieve data associated with a
        `NadirUID` that points to an object in that collection.

        This function is idempotent.
        """
        assert name not in self._tracked_collections

        self._tracked_collections.add(name)
        self.value_provider.update_document(
            NADIR_UID_COLLECTION_MAP, filter={'name': name},
            update={'$set': {'name': name}}, upsert=True
        )
        
        doc = self.value_provider.query_one_document(
            NADIR_UID_COLLECTION_MAP, filter={'name': name}
        )

        lsb_id = int.from_bytes(doc['_id'].binary[-4:], 'big')
        
        assert lsb_id not in self._id2collection

        self._collection2id[doc['name']] = lsb_id
        self._id2collection[lsb_id] = doc['name']

    def enable_read_only_provider(self, db_name: str):
        assert self.nib_read_only_provider is None
        self.nib_read_only_provider = ReadOnlyMongoProvider(db_name)

    def get_uid(self, collection_name: str, bson_id: ObjectId):
        lsb_id = self._collection2id[collection_name]
        return NadirUID(make_id(lsb_id, bson_id))

    def get_uid_from_int(self, collection_name: str, _int: int):
        lsb_id = self._collection2id[collection_name]
        return NadirUID(make_id(lsb_id, _int))

    @staticmethod
    def get_int_from_uid(uid: NadirUID):
        return int.from_bytes(uid.id.to_bytes(16, 'big')[4:], 'big')

    @classmethod
    def uid_as_int(cls, uid: NadirUID) -> int:
        res = cls.get_int_from_uid(uid)
        # print(f"{uid} to integer --> {res}")
        return res

    def int_as_uid(self, collection_name: str, _int: int):
        res = self.get_uid_from_int(collection_name, _int)
        # print(f"{_int} : {collection_name} to UID --> {res}")
        return res

    def get_uid_iterator(self, collection_name: str, inclusive_start: int, inclusive_end: int):
        for i in range(inclusive_start, inclusive_end+1):
            yield self.get_uid_from_int(collection_name, i)
    
    def get_tracked_object(self, uid: NadirUID):
        """
        Returns the raw object from Mongo, given its Nadir UID.
        NOTE: This does not filter the `_id` field, thus passing it
        as a Nadir type would cause an exception!
        """

        (col_id, obj_id) = get_ids(uid.id)

        obj = self.nib_read_only_provider.query_one_document(
            self._id2collection[col_id], filter={'_id': obj_id}
        )

        assert obj is not None
        if uid.obj is not None:
            assert uid.obj == obj
        
        return obj
    
    def get_tracked_nadir_object(self, uid: NadirUID):
        obj = self.get_tracked_object(uid)
        obj.pop('_id', None)
        return self.value_provider.as_nadir_from_bson(obj, False)
    
    def get_object_uid(self, collection_name, filter):
        assert collection_name in self._tracked_collections

        doc = self.nib_read_only_provider.query_one_document(collection_name, filter=filter)
        assert doc is not None

        lsb_id = self._collection2id[collection_name]
        return NadirUID(
            make_id(lsb_id, doc['_id']), doc
        )
    
    def get_all_tracked_uids(self, collection_name):
        assert collection_name in self._tracked_collections

        docs = self.nib_read_only_provider.query_document(collection_name, filter={}, projection={'_id': True})
        lsb_id = self._collection2id[collection_name]
        
        return [NadirUID(make_id(lsb_id, doc['_id'])) for doc in docs]

    def get_tracked_collection_document_count(self, collection_name):
        assert collection_name in self._tracked_collections

        return self.nib_read_only_provider.count_documents(collection_name)
    
    def insert_read_only_collection(self, collection_name: str, values: List[Any]):
        assert collection_name in self._tracked_collections

        docs = [self.value_provider.from_nadir_to_bson(value, False) for value in values]
        self.nib_read_only_provider.make_read_only_collection(collection_name, docs)

    def register_pid(self, pid: NadirPID):
        self.value_provider.register_pid(pid)
        self._module_provider.register_pid(pid)
        self.queue_provider.register_pid(pid)
    
    def register_cv(self, pids: FrozenSet[NadirPID], cv: Condition, index: int):
        self.value_provider.register_cv(pids, cv, index)
        self._module_provider.register_cv(pids, cv, index)
    
    def add_value(self, name: str, value: Any, is_queue: bool = False, is_function: bool = False,
        interacting_pids: List[NadirPID] = None, is_constant: bool = False, is_module_level: bool = False):
        assert not (is_queue and is_function), "You can't be both a queue and a function in Nadir!"
        assert not (is_constant and is_module_level), "Module level variables that are constant should be stored locally"

        if is_queue:
            assert interacting_pids is not None and len(interacting_pids) > 0
            self.queue_provider.add_value(name, value, interacting_pids=interacting_pids)
            self.queue_names.add(name)
        else:
            if is_module_level:
                self._module_provider.add_value(name, value)
                self._module_level_values.add(name)
            else:
                self.value_provider.add_value(name, value, is_function=is_function, is_constant=is_constant)

    def register_value(self, name: str, value: Any = None, is_queue: bool = False, is_function: bool = False,
        interacting_pids: List[NadirPID] = None, is_constant: bool = False, is_module_level: bool = False):
        assert not (is_queue and is_function), "You can't be both a queue and a function in Nadir!"
        assert not (is_constant and is_module_level), "Module level variables that are constant should be stored locally"

        if is_queue:
            assert interacting_pids is not None and len(interacting_pids) > 0
            self.queue_provider.register_value(name, interacting_pids=interacting_pids)
            self.queue_names.add(name)
        else:
            if is_module_level:
                self._module_provider.register_value(name, value=value)
                self._module_level_values.add(name)
            else:
                self.value_provider.register_value(name, value=value, is_function=is_function, is_constant=is_constant)


    def get_value(self, name: str, pid: NadirPID = None, address: NadirAddress = None) -> Any:
        if name in self.queue_names:
            return self.queue_provider.get_value(name, pid, address)
        if name in self._module_level_values:
            return self._module_provider.get_value(name, pid, address)
        return self.value_provider.get_value(name, pid, address)
    
    def set_value(self, pid: NadirPID, name: str, value: Any, address: NadirAddress = None):
        if name in self._module_level_values:
            self._module_provider.set_value(pid, name, value, address)
        else:
            self.value_provider.set_value(pid, name, value, address)

    def fifo_pop(self, pid: NadirPID, queue_name: str):
        self.queue_provider.fifo_pop(pid, queue_name)

    def fifo_put(self, pid: NadirPID, queue_name: str, msg):
        self.queue_provider.fifo_put(pid, queue_name, msg)

    def fifo_peek(self, pid: NadirPID, queue_name: str) -> Any:
        return self.queue_provider.fifo_peek(pid, queue_name)

    def fifo_peek_nb(self, pid: NadirPID, queue_name: str) -> Any:
        return self.queue_provider.fifo_peek_nb(pid, queue_name)

    def fifo_get(self, pid: NadirPID, queue_name: str) -> Any:
        return self.queue_provider.fifo_get(pid, queue_name)

    def ack_queue_put(self, pid: NadirPID, queue_name: str, msg):
        self.queue_provider.ack_queue_put(pid, queue_name, msg)

    def ack_queue_ack(self, pid: NadirPID, queue_name: str):
        self.queue_provider.ack_queue_ack(pid, queue_name)

    def ack_queue_get(self, pid: NadirPID, queue_name: str) -> Any:
        return self.queue_provider.ack_queue_get(pid, queue_name)

    def fanout_fifo_put(self, pid: NadirPID, queue_name: str, destination, msg):
        return self.queue_provider.fanout_fifo_put(pid, queue_name, destination, msg)
    
    def domain(self, name: str, address: NadirAddress = None):
        return self.value_provider.domain(name, address)

    def wait(self, pid: NadirPID, cv: Condition, condition_function: Callable[..., bool], *args, **kwargs):
        if 'is_module_level' in kwargs:
            is_module_level = kwargs.get('is_module_level')
            assert isinstance(is_module_level, bool)
            if is_module_level:
                return self._module_provider.wait(pid, cv, condition_function)
        return self.value_provider.wait(pid, cv, condition_function)

    def abort(self, pid: NadirPID):
        self._module_provider.abort(pid)
        self.queue_provider.abort(pid)
        self.value_provider.abort(pid)
    
    def commit(self, pid: NadirPID):
        self._module_provider.commit(pid)
        self.value_provider.commit(pid)
        self.queue_provider.commit(pid)

    def nuke(self, queue_names: List[str]):
        self._module_provider.nuke()
        self.value_provider.nuke()
        self.queue_provider.nuke(queue_names)

    def aggregate(self, collection: str, pipeline: List):
        assert collection not in self._module_level_values
        return self.value_provider.aggregate(collection, pipeline)
    
    def looks_empty(self, pid: NadirPID, queue_name: str) -> bool:
        return self.queue_provider.looks_empty(pid, queue_name)
