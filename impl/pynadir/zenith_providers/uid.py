from typing import Tuple, Union
from bson.objectid import ObjectId


"""
In MongoDB, we usually let the database index things with
the BSON ObjectId and just call it a day.

All the IRs, DAG objects and such things are also usually
just addressed with these ids and the collection name.

In Nadir, we can only use a global UID for all objects though,
so we need to find some way to do this.

Our current solution is this:
    - Keep the collections untouched, we expect everything to be 
      keyed with an ObjectId. 
    - A unique collection, "NADIR_UID_COLLECTION_MAP" will be 
      created upon startup. This collection will insert the collection
      name of all objects that are tracked with a UID. So each
      document in this collection will be of the form:

            {
                '_id': $oid
                'name': <str>
            }

      we will use the oid of this document to create an identifier
      for the collection. In particular, the 4 LSB bytes will be
      used.
      The final UID of every object within the program is then 
      generated with as follows:

    +----------------------+---------------------------------------+
    | 4 LSB Bytes From Map | 12 Bytes OID From Original Collection |
    +----------------------+---------------------------------------+
"""


NADIR_UID_COLLECTION_MAP = "NADIR_UID_COLLECTION_MAP"


def make_id(id1: Union[ObjectId, int], id2: Union[ObjectId, int]) -> int:
    """
    Make an integer value that can be used as a UID.
    Argument 1 is the collection OID, and Argument 2 is the object instance
    OID in that collection.
    """

    if isinstance(id1, ObjectId):
        id1_binary = id1.binary[-4:]
    elif isinstance(id1, int):
        id1_binary = id1.to_bytes(4, 'big')
    else:
        raise ValueError
    
    if isinstance(id2, ObjectId):
        id2_binary = id2.binary
    elif isinstance(id2, int):
        id2_binary = id2.to_bytes(12, 'big')
    else:
        raise ValueError
    
    return int.from_bytes(id1_binary + id2_binary, 'big')


def get_ids(uid: int) -> Tuple[int, ObjectId]:
    """
    Get the 4 LSB bytes of the collection OID and the instance
    OID from a given UID.
    """

    _bytes = uid.to_bytes(16, 'big')
    
    return int.from_bytes(_bytes[:4], 'big'), ObjectId(_bytes[4:])


def has_col_id(uid: int) -> bool:
    """
    Check if a given integer UID, actually has the 4 LSB bytes
    that identify its collection OID.
    """

    _bytes = uid.to_bytes(16, 'big')
    return int.from_bytes(_bytes[:4], 'big') > 0
