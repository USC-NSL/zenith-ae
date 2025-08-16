import argparse
from typing import Optional, Dict
from dataclasses import dataclass
from pynadir.structures import NadirPID, NadirUID
from pynadir.zenith_providers.provider import ZenithProvider
from atomics.common import MODEL_VALUES


"""
This sets up the rest of the input for the ZENITH specification that
it needs to function.
These inputs correspond to TLA+ `CONSTANT` statements. We will keep 
them on the NIB, however, all modules will cache them the moment that
they query them for the first time.

ZENITH gives no guarantees about what happens if these inputs change,
thus module caches MUST be invalidated if inputs change. This logic
is not yet needed to be added to ZENITH since the input can be proactively
scaled when needed.
"""


@dataclass
class NadirSpecConfiguration:
    """
    These correspond to `CONSTANT` statements on
    the ZENITH specification.
    """
    MaxDAGID: int = 3
    MaxNumIRs: int = 15
    TopologySize: int = 3


NADIR_INPUT_PROVIDER: Optional[ZenithProvider] = None
"""
There is only one ZENITH instance for now.
Thus, there shall be only one INPUT provider per process.
The variable above holds that provider.
"""


def make_input_provider():
    """Creates the input provider. This function is NOT idempotent."""
    global NADIR_INPUT_PROVIDER
    assert NADIR_INPUT_PROVIDER is None
    NADIR_INPUT_PROVIDER = ZenithProvider(nib_db_name='nib')


def get_input_provider() -> ZenithProvider:
    """Get the singular instance of ZENITH input provider."""
    assert NADIR_INPUT_PROVIDER is not None
    return NADIR_INPUT_PROVIDER


def clear_nadir_db(provider: ZenithProvider):
    """Clear the NIB and all of its queues"""
    provider.nuke([
        "RCNIBEventQueue",
        "TEEventQueue",
        "DAGEventQueue",
        "DAGQueue",
        "IRQueueNIB",
        "swSeqChangedStatus",
        "controller2Switch",
        "switch2Controller"
    ])


def get_ir2switch(provider: ZenithProvider, max_num_irs: int) -> Dict[NadirUID, NadirUID]:
    """
    Create the `IR2SW` map that the specification wants.
    It accounts for both dual and primal instructions.

    Parameters
    ----------
    provider: ZenithProvider
        The global provider instance
    max_num_irs: int
        The maximum number of IRs that we will _ever_ handle. This dictates
        where the block of dual IRs start.
    
    Returns
    -------
    Dict[NadirUID, NadirUID]
        A dictionary that maps the `NadirUID` of IRs to the `NadirUID` of
        their destination datapath.
    
    Notes
    -----
    This mapping is very frequently accessed and is read-only.
    As such, it is always cached in its entirety in each module.
    """
    dps = provider.nib_read_only_provider.query_document(
        "datapaths", filter={}
    )
    dp_id_to_uid_map = {doc['dp_id']: provider.get_uid("datapaths", doc['_id']) for doc in dps}

    irs = provider.nib_read_only_provider.query_document(
        "irs", filter={}, projection={'_id': True, 'dp_id': True}
    )
    
    maps = {doc['_id']: dp_id_to_uid_map[doc['dp_id']] for doc in irs}
    
    primaries = {provider.get_uid("irs", key): value for key, value in maps.items()}
    duals = {
        provider.int_as_uid('irs', provider.uid_as_int(key) + max_num_irs): value
        for key, value in primaries.items()
    }
    primaries.update(duals)

    return primaries


def do_core_input_setup_with_config(provider: ZenithProvider, params: NadirSpecConfiguration):
    """
    Setup all inputs needed for the `ZENITH` core implementation to operate.
    This process includes:
    - Tracking the collections `irs`, `dags` and `datapaths` on the NIB.
      Doing so means that any `NadirUID` associated with them will resolve
      to their instance on NIB, even when queried from the Nadir database.
    - Set values for all `CONSTANT` objects that the specification declares.
      These values must be either specificed in `params` or a combination of
      them and other constant values.
    - Set the `IR2SW` mapping by querying the datapath IDs in NIB.

    Parameters
    ----------
    provider: ZenithProvider
        The global `ZENITH` provider instance
    params: NadirSpecConfiguration
        Instance of `NadirSpecConfiguration` that defines constant values
    """
    for collection_name in {'irs', 'dags', 'datapaths'}:
        provider.track_collection(collection_name)

    # provider.add_value("CONTROLLER_THREAD_POOL", {MODEL_VALUES.t0, MODEL_VALUES.t1},
    #                                is_function=False, is_constant=True)
    provider.add_value("CONTROLLER_THREAD_POOL", {MODEL_VALUES.t0},
                                   is_function=False, is_constant=True)
    provider.add_value("RCProcSet", {
        NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.CONT_WORKER_SEQ),
        NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.CONT_BOSS_SEQ),
        NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.NIB_EVENT_HANDLER),
        NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.CONT_TE)
    }, is_function=False, is_constant=True)
    provider.add_value("OFCProcSet", {
        NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.t0),
        # NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.t1),
        NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.CONT_EVENT),
        NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.CONT_MONITOR)
    }, is_function=False, is_constant=True)
    provider.add_value("MaxDAGID", params.MaxDAGID, is_function=False, is_constant=True)
    provider.add_value("MaxNumIRs", params.MaxNumIRs, is_function=False, is_constant=True)

    # First, get all tracked objects
    tracked_datapaths = provider.get_all_tracked_uids("datapaths")

    provider.add_value("SW", set(tracked_datapaths), is_function=False, is_constant=True)
    ir2sw = get_ir2switch(provider, params.MaxNumIRs)
    provider.add_value("IR2SW", ir2sw, is_function=True)


def do_core_input_register_with_config(provider: ZenithProvider, params: NadirSpecConfiguration):
    """
    Same as `do_core_input_setup_with_config`, but it will _NOT_ upload any data
    into the database. This is useful for quickly reinitializing failed modules.
    This is safe, since all input data is read-only, it never changes during the
    lifetime of a `ZENITH` instance.

    Parameters
    ----------
    provider: ZenithProvider
        The global `ZENITH` provider instance
    params: NadirSpecConfiguration
        Instance of `NadirSpecConfiguration` that defines constant values
    """
    for collection_name in {'irs', 'dags', 'datapaths', 'DAG_STRUCTS'}:
        provider.track_collection(collection_name)

    provider.register_value("CONTROLLER_THREAD_POOL", value={MODEL_VALUES.t0},
                                   is_function=False, is_constant=True)
    # provider.register_value("CONTROLLER_THREAD_POOL", value={MODEL_VALUES.t0, MODEL_VALUES.t1},
    #                                is_function=False, is_constant=True)
    provider.register_value("RCProcSet", value={
        NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.CONT_WORKER_SEQ),
        NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.CONT_BOSS_SEQ),
        NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.NIB_EVENT_HANDLER),
        NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.CONT_TE)
    }, is_function=False, is_constant=True)
    provider.register_value("OFCProcSet", value={
        NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.t0),
        # NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.t1),
        NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.CONT_EVENT),
        NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.CONT_MONITOR)
    }, is_function=False, is_constant=True)
    provider.register_value("MaxDAGID", value=params.MaxDAGID, is_function=False, is_constant=True)
    provider.register_value("MaxNumIRs", value=params.MaxNumIRs, is_function=False, is_constant=True)

    tracked_datapaths = provider.get_all_tracked_uids("datapaths")
    provider.register_value("SW", value=set(tracked_datapaths), is_function=False, is_constant=True)
    ir2sw = get_ir2switch(provider, params.MaxNumIRs)
    provider.register_value("IR2SW", value=ir2sw, is_function=True, is_constant=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('num_irs', type=int, help='Maximum number of INSTALL instructions')
    parser.add_argument('num_dags', type=int, help='Maximum number of distinct DAGs')
    parser.add_argument('topo_size', type=int, help='Topology size')
    args = parser.parse_args()

    params = NadirSpecConfiguration(MaxDAGID=args.num_dags, MaxNumIRs=args.num_irs, TopologySize=args.topo_size)
    make_input_provider()
    do_core_input_setup_with_config(get_input_provider(), params)
