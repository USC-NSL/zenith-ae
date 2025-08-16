from pynadir.zenith_providers.value_provider import *


def test_mongo():
    provider = MongoProvider()
    provider.nuke()

    MODEL_VALUES = NadirModelValueAggregate(["ofc0", "t0", "t1"])

    provider.add_value("SW", {1, 2}, is_function=False)
    provider.add_value("CONTROLLER_THREAD_POOL", {
        MODEL_VALUES.t0, MODEL_VALUES.t1    # noqa
    }, is_function=False)
    provider.add_value("IR2SW", {
        NadirUID(1): 1, NadirUID(2): 2, NadirUID(3): 2
    }, is_function=True)
    provider.add_value("MaxDAGID", 15, is_function=False)
    provider.add_value("MaxNumIRs", 3, is_function=False)
    provider.add_value("TOPO_DAG_MAPPING", {
        frozenset(): {
            "v": {NadirUID(1), NadirUID(2)},
            "e": {(NadirUID(1), NadirUID(2))}
        },
        frozenset({1}): {
            "v": {NadirUID(3)},
            "e": set()
        }
    }, is_function=True)

    print(f'IR2SW:\n{str(provider.get_value("IR2SW"))}\n')
    print(f'IR2SW.{str(NadirUID(1))}:\n{str(provider.get_value("IR2SW", address=[NadirUID(1)]))}\n')
    print(f'DOMAIN IR2SW:\n{str(provider.domain("IR2SW"))}\n')
    print(f'TOPO_DAG_MAPPING:\n{str(provider.get_value("TOPO_DAG_MAPPING"))}\n')
    print(f'TOPO_DAG_MAPPING[{set()}]:\n{str(provider.get_value("TOPO_DAG_MAPPING", address=[frozenset()]))}\n')

    pid = NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.t0) # noqa
    provider.register_pid(pid)
    provider.set_value(pid, "IR2SW", 1, [NadirUID(1)])
    provider.set_value(pid, "TOPO_DAG_MAPPING", 10, [frozenset({1}), "e"])

    print(f"Before: {str(provider.get_value('IR2SW', address=[NadirUID(1)]))}\n")
    print(f"Before: {str(provider.get_value('TOPO_DAG_MAPPING', address=[frozenset({1}), 'e']))}\n")
    provider.commit(pid)
    print(f"After: {str(provider.get_value('IR2SW', address=[NadirUID(1)]))}")
    print(f"After: {str(provider.get_value('TOPO_DAG_MAPPING', address=[frozenset({1}), 'e']))}\n")

    cv = Condition()
    provider.register_cv(pids=frozenset([pid]), cv=cv, index=0)


    def func(glob_provider):
        return glob_provider.get_value('MaxNumIRs') == 10

    print("Will now do the waiting test!")
    while True:
        try:
            provider.wait(pid, cv, func)
            break
        except RepeatLabel:
            pass
    print("Done!")
