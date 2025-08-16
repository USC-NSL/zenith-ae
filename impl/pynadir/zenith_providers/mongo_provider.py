import pymongo
from abc import ABC, abstractmethod
from typing import Dict, Union, List, Any, Callable

import nib.nib_settings


class ReadOnlyProvider(ABC):
    @abstractmethod
    def query_document(self, collection: str, filter: Dict, projection: Dict = None) -> List:
        pass

    @abstractmethod
    def query_one_document(self, collection: str, filter: Dict, projection: Dict = None) -> Union[Dict, None]:
        pass

    @abstractmethod
    def make_read_only_collection(self, collection: str, documents: List[Any]):
        pass

    @abstractmethod
    def count_documents(self, collection: str):
        pass


class ReadOnlyMongoProvider(ReadOnlyProvider):
    """
    The input values are always read-only.
    For Zenith, these would be DAGs, IRs and Datapaths.
    We don't need fancy semantics to read these, thus this provider
    gives the minimum interface to quickly query these objects.

    Since collections attached to this provider are read-only, we
    can cache query results to prevent bothering the NIB.
    """
    
    def __init__(self, db_name: str, db_path: str = nib.nib_settings.LOCAL_PATH) -> None:
        self.db_name = db_name
        self.db_path = db_path

        self.client = pymongo.MongoClient(self.db_path)
        self.db = self.client[self.db_name]

    def query_document(self, collection: str, filter: Dict, projection: Dict = None) -> pymongo.cursor.Cursor[Any]:
        # print(f"Read-only query: {collection} | {filter} | {projection}")
        return self.db[collection].find(filter=filter, projection=projection)

    def query_one_document(self, collection: str, filter: Dict, projection: Dict = None) -> Union[Dict, None]:
        # print(f"Read-only query: {collection} | {filter} | {projection}")
        return self.db[collection].find_one(filter=filter)

    def count_documents(self, collection: str):
        # print(f"Read-only count query: {collection}")
        return self.db[collection].count_documents(filter={})

    def _insert_value_transaction(self, session, name: str, values: List[Any]):
        if self.query_one_document(name, filter={}):
            return
        self.db[name].insert_many(values, session=session)
    
    def _do_transaction(self, callback: Callable, wc=None, **callback_kwargs):
        with self.client.start_session() as session:
            return session.with_transaction(
                lambda s: callback(s, **callback_kwargs), write_concern=wc
            )
    
    def make_read_only_collection(self, collection: str, documents: List[Any]):
        # First, make sure the collection does not already exist
        assert self.query_one_document(collection, {}) is None
        assert isinstance(documents, list)

        self._do_transaction(self._insert_value_transaction, name=collection, values=documents)
