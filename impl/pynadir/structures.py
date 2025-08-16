import inspect
from abc import ABC, abstractmethod
from dataclasses import dataclass, fields
from typing import List, Any, Set, Dict, Callable, Type, Optional, Union, FrozenSet
from pynadir.params import NadirGlobalParams
from pynadir.exceptions import NadirLazyAccessDomainError, UnsupportedType


_KNOWN_CLASSES: Dict[str, Type] = dict()


def add_external_class(cls: Type):
    _KNOWN_CLASSES[cls.__name__] = cls


def dict_has_nadir_type(obj: Dict):
    """
    Some `dict` objects are serialized Nadir types, or other types
    that are not actually maps in reality. These dicts would have
    a type name (some string field starting with `_` and followed
    with a pre-determined string value) to show this.
    These values are:
        - `_nadir_type`: A derived class from `NadirType`. These can
          be Python representations of TLC types; so structs, model
          values, PIDs, etc.
        - `_class_name`: An instance of a POJO class that is globally
          known. There are a few cases that these are needed.
        - `_is_set` and `_is_fset`: Instances of Python set and 
          frozen set objects.
        - `_is_tuple`: Just Python tuples.
        - `_is_map`: Functions
    """
    return obj.get("_nadir_type") or \
           obj.get("_class_name") or \
           obj.get("_is_set") or \
           obj.get("_is_fset") or \
           obj.get("_is_tuple") or \
           obj.get("_is_map")


def as_nadir_type(obj: Any):
    """
    Converts elementary Python representation of certain types
    into their original versions.
    """

    global _KNOWN_CLASSES

    if obj is None:
        return None
    elif isinstance(obj, (int, float, str)):
        return obj
    elif isinstance(obj, dict):
        tpe = obj.get("_nadir_type")
        class_name = obj.get("_class_name")
        is_set = obj.get("_is_set")
        is_fset = obj.get("_is_fset")
        is_tuple = obj.get("_is_tuple")
        is_map = obj.get("_is_map")

        if tpe:
            # Is it a base Nadir type? (MV/PID/UID/Nat and UID sets)
            for cls in NadirType.__subclasses__():
                if cls._TYPE_NAME == tpe:
                    return cls.from_json(obj)
            # Is it a derived type? (structs/messages)
            for cls in NadirStructBase.__subclasses__():
                if cls._TYPE_NAME == tpe:
                    return cls.from_json(obj)
            # If we are here, this is not a supported type
            raise UnsupportedType
        elif is_set:
            return {as_nadir_type(x) for x in obj["value"]}
        elif is_fset:
            return frozenset({as_nadir_type(x) for x in obj["value"]})
        elif is_tuple:
            return tuple([as_nadir_type(x) for x in obj["value"]])
        elif class_name:
            cls = _KNOWN_CLASSES[class_name]
            cls_params = inspect.signature(cls.__init__).parameters
            return cls(**{
                arg_name: obj[arg_name] for arg_name in cls_params.keys() if arg_name != "self"
            })
        elif is_map:
            return dict((as_nadir_type(item[0]), as_nadir_type(item[1])) for item in obj["value"])
        else:
            raise ValueError(f"Cannot convert {obj} to a Nadir type.\ntpe={tpe}\tclass_name={class_name}\t"
                             f"is_set={is_set}\tis_fset={is_fset}\tis_tuple={is_tuple}\tis_map={is_map}")
    elif isinstance(obj, list):
        return [as_nadir_type(item) for item in obj]
    elif isinstance(obj, set):
        return {as_nadir_type(item) for item in obj}
    elif isinstance(obj, frozenset):
        return frozenset({as_nadir_type(item) for item in obj})
    elif isinstance(obj, tuple):
        print(obj)
        return as_nadir_type(dict(obj))
    else:
        raise UnsupportedType
    

def from_nadir_type(value: Any):
    """
    Convert a Nadir value, into a simple Python representation
    of that object.
    """

    if value is None:
        return None
    elif isinstance(value, NadirType):
        return value.json()
    elif isinstance(value, dict):
        return {
            "_is_map": True,
            "value": [(from_nadir_type(key), from_nadir_type(value)) for key, value in value.items()]
        }
    elif isinstance(value, list):
        return [from_nadir_type(x) for x in value]
    elif isinstance(value, tuple):
        return {
            "_is_tuple": True,
            "value": [from_nadir_type(x) for x in value]
        }
    elif isinstance(value, set):
        return {
            "_is_set": True,
            "value" : [from_nadir_type(x) for x in value]
        }
    elif isinstance(value, frozenset):
        return {
            "_is_fset": True,
            "value" : [from_nadir_type(x) for x in value]
        }
    elif isinstance(value, (int, float, str)):
        return value
    else:
        """
        This just uses the __dict__ attribute of the object to serialize
        it.
        """

        obj_dict: Dict = value.__dict__
        obj_dict.update({"_class_name": type(value).__name__})
        return obj_dict


class NadirType(ABC):
    """
    The base class of which all Nadir types derive from.
    Such types include things like MVs, PIDs and UIDs ...

    The attribute `_TYPE_NAME` is crucial for finding the
    correct constructor of a serialized Nadir object.
    """

    _TYPE_NAME = ""

    @classmethod
    @abstractmethod
    def from_json(cls, d: Dict):
        """Make an instance of this type from a dict representation of it"""
        pass

    @abstractmethod
    def json(self):
        """
        Convert this instance into a json-like dict representation. This is
        prioritized for simplicity first in practice.
        """
        pass

    def _with_type(self, d: Dict):
        """Tag the representation of the object with its type name"""
        d.update({"_nadir_type": self._TYPE_NAME})
        return d


def fnv64_str(data):
    assert isinstance(data, str)
    hash_ = 0xcbf29ce484222325
    for b in data.encode():
        hash_ *= 0x100000001b3
        hash_ &= 0xffffffffffffffff
        hash_ ^= b
    return hash_


class NadirModelValue(NadirType):
    """
    TLC Model Values, equal only to themselves, and are comparable to
    any other type.
    Our TLC Model Value implementations receive just a singular name from
    Nadir, but upon creation, a hash is calculated by combining both the 
    hash of the name and the hash of the random sequence assigned to the
    Nadir global parameter configuration.

    This makes a best effort case that these Model Values will only
    equate themselves, whether here or in another module of the same 
    Nadir build.
    """

    _TYPE_NAME = "NADIR_MODEL_VALUE"

    def __init__(self, name: str) -> None:
        self.name = name

        """
        This hash MUST be stable across the same build, so we need a stable,
        unsalted hash. We use fnv64 for now.
        """

        self._mv_hash = fnv64_str(name + NadirGlobalParams.build_id)

    def __str__(self) -> str:
        return self.name
    
    def __eq__(self, value: object) -> bool:
        if isinstance(value, NadirModelValue):
            return self._mv_hash == value._mv_hash
        return False
    
    def __hash__(self) -> int:
        return self._mv_hash
    
    def json(self):
        return self._with_type({"name": self.name})
    
    @classmethod
    def from_json(cls, d: Dict):
        return NadirModelValue(d["name"])
    

class NadirModelValueAggregate:
    """
    A Nadir spec will register its Model Values with this aggregator
    object, and then create a global instance to keep track of them.
    """

    def __init__(self, names: List[str]) -> None:
        self.names = names
        for name in names:
            setattr(self, name, NadirModelValue(name))

    def is_model_value(self, mv: str) -> bool:
        return hasattr(self, mv)

    def add_mv(self, new_names: Union[str, List[str]]):
        """Be careful when calling this!"""

        if isinstance(new_names, str):
            assert new_names not in self.names
            self.names.append(new_names)
            setattr(self, new_names, NadirModelValue(new_names))
        else:
            assert isinstance(new_names, list)
            for new_name in new_names:
                assert new_name not in self.names
                setattr(self, new_name, NadirModelValue(new_name))
            self.names += new_names


@dataclass
class NadirPID(NadirType):
    module: NadirModelValue
    thread: NadirModelValue

    _TYPE_NAME = "NADIR_PID"

    def __str__(self) -> str:
        return f"{self.module} || {self.thread}"
    
    def __eq__(self, value: object) -> bool:
        if isinstance(value, NadirPID):
            return (self.module == value.module) and (self.thread == value.thread)
        return False
    
    def __hash__(self) -> int:
        return hash((self.module, self.thread))
    
    def json(self):
        return self._with_type({
            "module": self.module.json(),
            "thread": self.thread.json()
        })
    
    @classmethod
    def from_json(cls, d: Dict):
        return NadirPID(
            NadirModelValue.from_json(d["module"]),
            NadirModelValue.from_json(d["thread"])
        )
    
    @classmethod
    def from_str(cls, pid_as_str: str, all_mvs: NadirModelValueAggregate):
        ls = pid_as_str.split(" || ")
        if len(ls) == 2:
            if all_mvs.is_model_value(ls[0]) and all_mvs.is_model_value(ls[1]):
                return cls(getattr(all_mvs, ls[0]), getattr(all_mvs, ls[1]))
        raise ValueError(f"String {pid_as_str} cannot be a Nadir PID")
    

class NadirUID(NadirType):
    """
    For now, Nadir will not handle UID assignment directly.
    If you have objects with conflicting UIDs, then Nadir gives
    no direct guarantees on the behavior of its execution.
    """

    _TYPE_NAME = "NADIR_UID"

    def __init__(self, id: int, obj: Any = None) -> None:
        # The id MUST be an integer
        assert isinstance(id, int)
        self.id = id
        self.obj = obj

    def __eq__(self, value: object) -> bool:
        if isinstance(value, NadirUID):
            return self.id == value.id
        return False
    
    def __hash__(self) -> int:
        return self.id
    
    def __str__(self) -> str:
        return f"NadirUID[{self.id}, {self.obj}]"
    
    def json(self):
        """
        Serializing the object is pointless, since we'll have to query it
        later!
        """

        return self._with_type({"id": str(self.id)})
    
    @classmethod
    def from_json(cls, d: Dict):
        return NadirUID(
            id=int(d["id"]),
            obj=as_nadir_type(d.get("obj"))
        )


NadirAddress = Optional[List[Union[int, str, NadirUID, FrozenSet]]]


class _NaturalNumbersSet(NadirType):
    _TYPE_NAME = "NADIR_NAT_SET"

    def __contains__(self, item) -> bool:
        return (isinstance(item, int) and item > 0) or (isinstance(item, NadirUID) and item.id > 0)
    
    def json(self):
        return self._with_type({})
    
    @classmethod
    def from_json(cls, d: Dict):
        return NaturalNumbersSet


class _NadirUIDSet(NadirType):
    _TYPE_NAME = "_NADIR_UID_SET"

    def __contains__(self, item) -> bool:
        return (isinstance(item, NadirUID)) and (item.id > 0)
    
    def json(self):
        return self._with_type({})
    
    @classmethod
    def from_json(cls, d: Dict):
        return NadirUIDSet


"""
These dummy set definitions only support `in` tests.
We use them to be able to translate the TLA+ code exactly as is
without much modification.
"""

BooleanSet = {True, False}
NaturalNumbersSet = _NaturalNumbersSet()
NadirUIDSet = _NadirUIDSet()


class HasDomain:
    def __init__(self, domain: Set[Any]) -> None:
        self.domain = domain


class NadirGreedyFunction(HasDomain):
    def __init__(self, dict_object: Dict) -> None:
        super().__init__(set(dict_object.keys()))
        self.dict_object = dict_object

    def __call__(self, key) -> Any:
        return self.dict_object[key]
    
    def __getitem__(self, key) -> Any:
        return self(key)

    
class NadirLazyFunction(HasDomain):
    def __init__(self, domain: Set[Any], expression: Callable) -> None:
        super().__init__(domain)
        self.expression = expression

    def __call__(self, key) -> Any:
        if (key in self.domain):
            return self.expression(key)
        else:
            raise NadirLazyAccessDomainError(f"Item {key} is not a valid domain element")
        
    def __getitem__(self, key) -> Any:
        return self(key)
    

class NadirEternallyGettableStruct:
    def __getitem__(self, key: str):
        return self


def nadir_dataclass(**kwargs):
    def wrap(cls):
        d_class = dataclass(cls, **kwargs) # noqa
        d_class._TYPE_NAME = d_class.__name__
        d_class.domain = set(f.name for f in fields(d_class))
        return d_class
    return wrap


class NadirStructBase(NadirType):
    def __getitem__(self, key: str):
        try:
            return getattr(self, key)
        except AttributeError:
            return NadirEternallyGettableStruct()
    
    def __setitem__(self, key: str, value: Any):
        setattr(self, key, value)

    def update(self, name: str, value: Any):
        """
        Structs will be implemented as frozen dataclass instances to make them
        safely hashable.
        However, this prevents in-place modifications. Nadir will keep an eye for
        modifications to structs and messages, and will create a new instance
        if the algorithm explicitly wants to change the struct/message.
        """
        current_fields = self.__dict__
        current_fields.update({name: value})
        return self.__init__(**current_fields) # noqa
    
    def json(self):
        fs = fields(self) # noqa
        return self._with_type({
            f.name: from_nadir_type(getattr(self, f.name)) for f in fs
        })
    
    @classmethod
    def from_json(cls, d: Dict):
        return cls(**{ # noqa
            key: as_nadir_type(value) for key, value in d.items() if key != "_nadir_type"
        })


def conditional_choose(inp, predicate: Callable):
    """
    The CHOOSE semantics of TLC, does not require the choice
    to be random (even pseudo-random), it translates much more
    to `I do not care, just pick one`.
    
    This is an assertion on behalf of the user, NOT the model
    checker, therefore there is no need to make this code return
    random samples.

    This becomes especially important when we consider that
    the input may not be a set or list, but an iterator or
    generator (on a remote or unbounded set). As such, we
    find it more fitting here to just pick the first element
    that satisfies the condition and return it without
    exhausting the iterator.
    """

    try:
        return next(e for e in inp if predicate(e))
    except StopIteration:
        raise ValueError("EXHAUSTED CHOOSE!")


class NadirUnionType(ABC):
    classes: List[Type] = []

    @classmethod
    def register_union(cls):
        for tpe in cls.classes:
            cls.register(tpe) # noqa

    def __new__(cls, *args, **kwargs):
        for tpe in cls.classes:
            try:
                return tpe(*args, **kwargs)
            except TypeError:
                pass
        raise TypeError
