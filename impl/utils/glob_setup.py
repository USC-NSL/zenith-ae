"""
The `GLOBAL_PROVIDER` is a wrapper around database actions that can read/write global values.
The user must initialize these variables her manually.
"""

import argparse

from pynadir.zenith_providers.provider import ZenithProvider
from utils.input_setup import get_input_provider, NadirSpecConfiguration
from atomics.common import *


"""
This sets up all global variables on the `NADIR` database that
`ZENITH` needs to function.
These correspond to any variable that is defined under the global
`variables` block in the PlusCal specification.
"""


NADIR_GLOBAL_PROVIDER: Optional[ZenithProvider] = None
"""This is the singular instance of global `ZenithProvider` per process"""


def make_global_provider():
    """Creates the global value provider. This function is NOT idempotent."""
    global NADIR_GLOBAL_PROVIDER
    NADIR_GLOBAL_PROVIDER = ZenithProvider()


def get_global_provider() -> ZenithProvider:
    """Get the singular instance of ZENITH global value provider."""
    assert NADIR_GLOBAL_PROVIDER is not None
    return NADIR_GLOBAL_PROVIDER


INTERACTING_PIDS = {
    "RCNIBEventQueue": [
        NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.NIB_EVENT_HANDLER),  # consumer
        NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.t0),                # producer
        # NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.t1),                # producer
        NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.CONT_EVENT),        # producer
        NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.CONT_MONITOR)       # producer
    ],
    "TEEventQueue": [
        NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.NIB_EVENT_HANDLER),  # producer
        # NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.CONT_RECONCILER),    # producer
        NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.CONT_TE)             # consumer
    ],
    "DAGEventQueue": [
        NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.CONT_TE),            # producer
        NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.CONT_BOSS_SEQ)       # consumer
    ],
    "DAGQueue": [
        NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.CONT_BOSS_SEQ),      # producer
        NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.CONT_WORKER_SEQ)     # consumer
    ],
    "IRQueueNIB": [
        NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.CONT_WORKER_SEQ),    # producer
        NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.t0),                # consumer
        # NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.t1)                 # consumer
        NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.CONT_EVENT)         # producer
    ],
    "swSeqChangedStatus": [
        NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.CONT_MONITOR),      # producer
        NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.CONT_EVENT)         # consumer
    ],
    "controller2Switch": [
        NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.t0),                # producer
        # NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.t1),                # producer
        # NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.CONT_RECONCILER)     # producer
    ],
    "switch2Controller": [
        NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.CONT_MONITOR)       # consumer
    ],
    "reconciliationQueue": [
        NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.CONT_EVENT)         # consumer
    ]
}
"""
Each queue is accessed by a known set of processes. It is a violation of
`NADIR`s safety constraints to access a queue in the implementation that is
never accessed in the specification.
Thus, each queue has an `Interacting PID` label that describes the list of
PIDs that can access it (i.e. produce or consume on it).

While `NADIR` knows this from the specification, we re-define it here since
it helps debugging.
"""


def do_queue_setup(provider: ZenithProvider, pids: Optional[List[NadirPID]] = None):
    """
    Set up all queues that connect different modules.

    Parameters
    ----------
    provider: ZenithProvider
        The `ZENITH` global value provider.
    pids: List[NadirPID], optional
        The list of PIDs to set up the queues. If empty, will do it
        for all of them.
    """
    for queue_name, interacting_pids in INTERACTING_PIDS.items():
        if pids is not None:
            this_pids_set = set(pids)
            that_pids_set = set(interacting_pids)
            if this_pids_set.isdisjoint(that_pids_set):
                continue
        provider.add_value(queue_name, [], is_queue=True, interacting_pids=interacting_pids)


def do_queue_register(provider: ZenithProvider, pids: Optional[List[NadirPID]] = None):
    """
    Same as `do_queue_setup`, but will _NOT_ make the queues or otherwise change them.
    It only makes it known to ZENITH that a queue exists.
    """
    for queue_name, interacting_pids in INTERACTING_PIDS.items():
        if pids is not None:
            this_pids_set = set(pids)
            that_pids_set = set(interacting_pids)
            if this_pids_set.isdisjoint(that_pids_set):
                continue

        provider.register_value(queue_name, is_queue=True, interacting_pids=interacting_pids)


def do_ofc_module_setup(provider: ZenithProvider, params: NadirSpecConfiguration, is_module: bool):
    provider.add_value("eventHandlerCheckpoint", False, is_module_level=is_module)
    provider.add_value("eventHandlerTCAMCleared", False, is_module_level=is_module)
    provider.add_value("eventHandlerLastIRToReset", None, is_module_level=is_module)


def do_ofc_module_register(provider: ZenithProvider, is_module: bool):
    provider.register_value("eventHandlerCheckpoint", False, is_module_level=is_module)
    provider.register_value("eventHandlerTCAMCleared", False, is_module_level=is_module)
    provider.register_value("eventHandlerLastIRToReset", None, is_module_level=is_module)


def do_rc_module_setup(provider: ZenithProvider, params: NadirSpecConfiguration, is_module: bool):
    input_provider = get_input_provider()
    provider.add_value("RCIRStatus",
        {
            x: StructIRPair(EnumIRState.IR_NONE, EnumIRState.IR_NONE)
            for x in input_provider.get_uid_iterator('irs', 1, params.MaxNumIRs)
        }, is_function=True, is_module_level=is_module
    )
    provider.add_value("RCSwSuspensionStatus",
        {
            x: EnumSwitchState.SW_RUN
            for x in input_provider.get_uid_iterator('datapaths', 1, params.TopologySize)
        }, is_function=True, is_module_level=is_module
    )
    provider.add_value("DAGState",
        {
            x: EnumDAGState.DAG_NONE
            for x in range(1, params.MaxDAGID+1)
        }, is_function=True, is_module_level=is_module
    )
    provider.add_value("ScheduledIRs",
        {
            x: False
            for x in input_provider.get_uid_iterator('irs', 1, 2 * params.MaxNumIRs)
        }, is_function=True, is_module_level=is_module
    )
    provider.add_value("seqWorkerIsBusy", False, is_module_level=is_module)


def do_rc_module_register(provider: ZenithProvider, is_module: bool):
    provider.register_value("RCIRStatus", is_function=True, is_module_level=is_module)
    provider.register_value("RCSwSuspensionStatus", is_function=True, is_module_level=is_module)
    provider.register_value("DAGState", is_function=True, is_module_level=is_module)
    provider.register_value("seqWorkerIsBusy", is_module_level=is_module)
    provider.register_value("ScheduledIRs", is_function=True, is_module_level=is_module)


def do_global_setup(provider: ZenithProvider,  pids: Optional[List[NadirPID]] = None, 
                    params: Optional[NadirSpecConfiguration] = None, 
                    module_only: bool = False) -> NadirSpecConfiguration:
    """
    Set up all global variables needed for the `ZENITH` core specification to function.
    This _MUST_ be called after all input has already been set up (so a singular input
    provider instance must already exist).

    Parameters
    ----------
    provider: ZenithProvider
        The singular `ZENITH` global value provider instance.
    pids: List[NadirPID], optional
        The list of `NADIR` process IDs, used for queue set up. When
        not provided, it will set up queues for all modules.
    params: NadirSpecConfiguration, optional
        A `NadirSpecConfiguration` instance that defines the value
        of some `CONSTANT`s from the specification.
        If not provided, it _MUST_ be deduced from input values.
    module_only: bool, optional
        If True, skip global variable set up on the module level. For
        our specification, these correspond to checkpoints for Event 
        Handler.
    
    Returns
    -------
    NadirSpecConfiguration
        If `params` was None, this would be the configuration that was deduced
        by looking at the input values. Otherwise, this is just `params`.
    """
    input_provider = get_input_provider()
    if params is None:
        params = NadirSpecConfiguration(
            MaxDAGID=input_provider.get_tracked_collection_document_count('dags'),
            MaxNumIRs=input_provider.get_tracked_collection_document_count('irs'),
            TopologySize=input_provider.get_tracked_collection_document_count('datapaths'),
        )
    provider.add_value("NIBIRStatus",
        {
            x: StructIRPair(EnumIRState.IR_NONE, EnumIRState.IR_NONE)
            for x in input_provider.get_uid_iterator('irs', 1, params.MaxNumIRs)
        }, is_function=True
    )
    provider.add_value("SwSuspensionStatus",
        {
            x: EnumSwitchState.SW_RUN
            for x in input_provider.get_uid_iterator('datapaths', 1, params.TopologySize)
        }, is_function=True
    )

    # if not module_only:
    #     do_ofc_module_setup(provider, params, False)
    #     do_rc_module_setup(provider, params, False)
    do_ofc_module_setup(provider, params, module_only)
    do_rc_module_setup(provider, params, module_only)

    do_queue_setup(provider, pids)

    # We need this for 'int_to_uid' calls
    provider.track_collection('irs')

    return params


def do_global_register(provider: ZenithProvider, pids: Optional[List[NadirPID]] = None, module_only: bool = False):
    """Same as `do_global_setup`, but only declares variables and does not initialize or change them"""
    provider.register_value("NIBIRStatus", is_function=True)
    provider.register_value("SwSuspensionStatus", is_function=True)
    do_ofc_module_register(provider, module_only)
    do_rc_module_register(provider, module_only)
    do_queue_register(provider, pids)
    provider.track_collection('irs')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--num_irs', type=int, help='Maximum number of INSTALL instructions')
    parser.add_argument('--num_dags', type=int, help='Maximum number of distinct DAGs')
    parser.add_argument('--topo_size', type=int, help='Topology size')
    args = parser.parse_args()

    make_global_provider()
    provider = get_global_provider()

    if args.num_irs is not None or args.dag_size is not None or args.topo_size is not None:
        assert args.num_irs is not None and args.dag_size is not None and args.topo_size is not None
        do_global_setup(provider, 
                        params=NadirSpecConfiguration(
                            MaxDAGID=args.num_dags, 
                            MaxNumIRs=args.num_irs, 
                            TopologySize=args.topo_size
                        ))
    else:
        do_global_setup(provider)
