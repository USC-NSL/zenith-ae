from pynadir.structures import *
from nib.nib_defs import IR

add_external_class(IR)


def test_mv():
    mv = NadirModelValue("test")
    d_mv = from_nadir_type(mv)
    _mv = as_nadir_type(d_mv)
    assert _mv == mv


def test_pid():
    pid = NadirPID(NadirModelValue("ofc0"), NadirModelValue("t0"))
    d_pid = from_nadir_type(pid)
    _pid = as_nadir_type(d_pid)
    assert _pid == pid


def test_object():
    # Make some arbitrary object
    obj = IR("aragif", 10, cookie=20)

    uid = NadirUID(12, obj=obj)
    d_uid = from_nadir_type(uid)
    _uid = as_nadir_type(d_uid)
    assert _uid == uid


def test_struct():
    obj = IR("aragif", 10, cookie=20)
    pid = NadirPID(NadirModelValue("ofc0"), NadirModelValue("t0"))

    @nadir_dataclass(frozen=True)
    class TestStruct(NadirStructBase):
        irs: List[IR]
        nadir_pid: NadirPID

    struct = TestStruct([obj], pid)
    d_struct = from_nadir_type(struct)
    _struct = as_nadir_type(d_struct)
    assert _struct == struct


def test_function():
    mv = NadirModelValue("test")
    obj = IR("aragif", 10, cookie=20)
    uid = NadirUID(12, obj=obj)

    func1 = {uid: mv}
    d_func1 = from_nadir_type(func1)
    _func1 = as_nadir_type(d_func1)
    assert _func1 == func1

    func2 = {
        frozenset(): {
            "v": {NadirUID(1), NadirUID(2)},
            "e": {(NadirUID(1), NadirUID(2))}
        },
        frozenset({mv}): {
            "v": {NadirUID(3)},
            "e": set()
        }
    }

    d_func2 = from_nadir_type(func2)
    print(d_func2)
    _func2 = as_nadir_type(d_func2)
    assert _func2 == func2
