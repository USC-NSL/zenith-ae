import core.sequencer as SEQ
import core.worker_pool as WP
import core.event_handler as EH
import core.monitoring_server as MS
import apps.TE as TE
# import simple_core.sequencer as SimpleSEQ
# import simple_core.worker_pool as SimpleWP
# import simple_core.event_handler as SimpleEH
# import simple_core.monitoring_server as SimpleMS
# import simple_apps.TE as SimpleTE
from runtime_definitions import *
from atomics.patches import *
from atomics.common import MODEL_VALUES, NadirPID, StructRCDAG
from pynadir.utils.logging import TitledLog
from pynadir.zenith_providers.provider import ZenithProvider
from utils.input_setup import NadirSpecConfiguration


def set_to_default_module_assignment():
    module_assignments = get_algorithm_module_assignment_dict()
    assert len(module_assignments) == 0

    TitledLog.info("config", "Using `DEFAULT` module assignment")

    module_assignments["zenith-ofc"] = (
        MODEL_VALUES.ofc0,
        {
            "WorkerPool",
            "EventHandler",
            "MonitoringServer"
        }
    )
    module_assignments["zenith-rc"] = (
        MODEL_VALUES.rc0,
        {
            "NIBEventHandler",
            "ControllerTE",
            "ControllerBoss",
            "ControllerSeq"
        }
    )


def set_to_default_component_configuration(simple: bool = False):
    TitledLog.info("config", "Using `DEFAULT` component configuration")

    if simple:
        # controllerSequencer = get_component(SimpleSEQ, "controllerSequencer")
        # controllerBossSequencer = get_component(SimpleSEQ, "controllerBossSequencer")
        # controllerWorkerThreads = get_component(SimpleWP, "controllerWorkerThreads")
        # controllerEventHandler = get_component(SimpleEH, "controllerEventHandler")
        # controllerMonitoringServer = get_component(SimpleMS, "controllerMonitoringServer")
        # rcNibEventHandler = get_component(SimpleTE, "rcNibEventHandler")
        # controllerTrafficEngineering = get_component(SimpleTE, "controllerTrafficEngineering")
        raise NotImplementedError
    else:
        controllerSequencer = get_component(SEQ, "controllerSequencer")
        controllerBossSequencer = get_component(SEQ, "controllerBossSequencer")
        controllerWorkerThreads = get_component(WP, "controllerWorkerThreads")
        controllerEventHandler = get_component(EH, "controllerEventHandler")
        controllerMonitoringServer = get_component(MS, "controllerMonitoringServer")
        rcNibEventHandler = get_component(TE, "rcNibEventHandler")
        controllerTrafficEngineering = get_component(TE, "controllerTrafficEngineering")

    for cmp in [
        controllerSequencer,
        controllerBossSequencer,
        controllerWorkerThreads,
        controllerEventHandler,
        controllerMonitoringServer,
        rcNibEventHandler,
        controllerTrafficEngineering
    ]:
        TitledLog.debug("config", f"Using component {cmp.__name__}")

    algorithm_process_params = get_algorithm_process_param_dict()
    assert len(algorithm_process_params) == 0

    algorithm_process_params["NIBEventHandler"] = ProcessParams(
        process_specification=NadirProcessSpecification(
            impl=rcNibEventHandler, mv_aggregate=MODEL_VALUES,
            process_name="zenith-nib-eh",
            threads=[NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.NIB_EVENT_HANDLER)],
            local_vars={
                "event": None
            },
            initial_label="RCSNIBEventHndlerProc"
        ),
        operator_patch_list=[
            ("getPrimaryOfIR", getPrimaryOfIR_patched),
            # ("getSwitchForIR", getSwitchForIR_patched)
        ],
        macro_patch_list=[]
    )
    algorithm_process_params["ControllerTE"] = ProcessParams(
        process_specification=NadirProcessSpecification(
            impl=controllerTrafficEngineering, mv_aggregate=MODEL_VALUES,
            process_name="zenith-te",
            threads=[NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.CONT_TE)],
            local_vars={
                "topoChangeEvent": None,
                "currSetDownSw": set(),
                "prev_dag_id": None,
                "init": True,
                "DAGID": None,
                "nxtDAG": None,
                "nxtDAGVertices": set(),
                "setRemovableIRs": set()                
            },
            initial_label="ControllerTEProc"
        ),
        operator_patch_list=[
            ("getSetRemovableIRs", getSetRemovableIRs_patched),
            ("getPrimaryOfIR", getPrimaryOfIR_patched),
            ("getDualOfIR", getDualOfIR_patched),
            # ("getSwitchForIR", getSwitchForIR_patched)
        ],
        macro_patch_list=[
            ("unscheduleDagIRs", unscheduleDagIRs_patched)
        ]
    )
    algorithm_process_params["ControllerBoss"] = ProcessParams(
        process_specification=NadirProcessSpecification(
            impl=controllerBossSequencer, mv_aggregate=MODEL_VALUES,
            process_name="zenith-boss-seq",
            threads=[NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.CONT_BOSS_SEQ)],
            local_vars={
                "seqEvent": None
            },
            initial_label="ControllerBossSeqProc"
        ),
        operator_patch_list=[
            # ("getSwitchForIR", getSwitchForIR_patched)
        ],
        macro_patch_list=[]
    )
    algorithm_process_params["ControllerSeq"] = ProcessParams(
        process_specification=NadirProcessSpecification(
            impl=controllerSequencer, mv_aggregate=MODEL_VALUES,
            process_name="zenith-seq",
            threads=[NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.CONT_WORKER_SEQ)],
            local_vars={
                "toBeScheduledIRs": set(),
                "nextIR": None,
                "currDAG": None,
                "IRDoneSet": set()
            },
            initial_label="ControllerWorkerSeqProc"
        ),
        operator_patch_list=[
            ("getPrimaryOfIR", getPrimaryOfIR_patched),
            ("getDualOfIR", getDualOfIR_patched),
            ("getSetIRsCanBeScheduledNext", getSetIRsCanBeScheduledNext_patched),
            ("AddDeleteDAGIRDoneSet", AddDeleteDAGIRDoneSet_patched),
            ("dagObjectShouldBeProcessed", dagObjectShouldBeProcessed_patched),
        ],
        macro_patch_list=[]
    )
    algorithm_process_params["WorkerPool"] = ProcessParams(
        process_specification=NadirProcessSpecification(
            impl=controllerWorkerThreads, mv_aggregate=MODEL_VALUES,
            process_name="zenith-wp",
            threads=[
                NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.t0),
                # NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.t1),
                # NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.t2)
            ],
            local_vars={
                "nextIRObjectToSend": None,
                "index": 0
            },
            initial_label="ControllerThread"
        ),
        operator_patch_list=[
            # TODO: Check these

            # ("getIRFlow", getIRFlow_patched),
            ("getPrimaryOfIR", getPrimaryOfIR_patched),
            # ("getSwitchForIR", getSwitchForIR_patched)
        ],
        macro_patch_list=[]
    )
    algorithm_process_params["EventHandler"] = ProcessParams(
        process_specification=NadirProcessSpecification(
            impl=controllerEventHandler, mv_aggregate=MODEL_VALUES,
            process_name="zenith-eh",
            threads=[NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.CONT_EVENT)],
            local_vars={
                "monitoringEvent": None,
                "setIRsToReset": set(),
                "resetIR": None
            },
            initial_label="ControllerEventHandlerStateReconciliation"
        ),
        operator_patch_list=[
            ("getIRSetToReset", getIRSetToReset_patched),

            # ("getSwitchForIR", getSwitchForIR_patched)
        ],
        macro_patch_list=[]
    )
    algorithm_process_params["MonitoringServer"] = ProcessParams(
        process_specification=NadirProcessSpecification(
            impl=controllerMonitoringServer, mv_aggregate=MODEL_VALUES,
            process_name="zenith-ms",
            threads=[NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.CONT_MONITOR)],
            local_vars={
                "msg": None,
                "irID": None
            },
            initial_label="ControllerMonitorCheckIfMastr"
        ),
        operator_patch_list=[
            ("getIRIDForFlow", getIRIDForFlow_patched),
            ("getPrimaryOfIR", getPrimaryOfIR_patched),
            ("getDualOfIR", getDualOfIR_patched),
            ("existsMonitoringEventHigherNum", existsMonitoringEventHigherNum_patched)
            # ("getSwitchForIR", getSwitchForIR_patched)
        ],
        macro_patch_list=[],
    )


def get_topo_dag_mapping(provider: ZenithProvider):
    """
    Reads the trigger set associated with each DAG in the `dags` collection of NIB,
    and generates a topology to DAG mapping based on it.
    """
    dags = provider.nib_read_only_provider.query_document("dags", filter={})
    return {
        # frozenset([provider.get_object_uid("datapaths", {"dp_id": dp_id}) for dp_id in doc['trigger_set']]): {
        #     'v': set(provider.get_uid("irs", ir) for ir in doc['nodes']),
        #     'e': set((provider.get_uid("irs", t[0]), provider.get_uid("irs", t[1])) for t in doc['edges'])
        # } for doc in dags
        frozenset([provider.get_object_uid("datapaths", {"dp_id": dp_id}) for dp_id in doc['trigger_set']]):
            StructRCDAG(
                v=set(provider.get_uid("irs", ir) for ir in doc['nodes']),
                e=set((provider.get_uid("irs", t[0]), provider.get_uid("irs", t[1])) for t in doc['edges'])
            )
        for doc in dags
    }


def get_rc_dags(provider: ZenithProvider) -> List[StructRCDAG]:
    """
    Converts the contents of the `dags` collection in NIB (each a `NadirDAG` object),
    into a `StructRCDAG` instance.
    """
    dags = provider.nib_read_only_provider.query_document("dags", filter={})

    return [
        StructRCDAG(
            frozenset(provider.get_uid("irs", ir) for ir in doc['nodes']),
            frozenset((provider.get_uid("irs", t[0]), provider.get_uid("irs", t[1])) for t in doc['edges'])
        ) for doc in dags
    ]


def do_TE_input_setup_with_config(provider: ZenithProvider, params: NadirSpecConfiguration):
    # Now, we need to create the DAG structs and put them in a tracked collection
    dag_structs = get_rc_dags(provider)
    provider.track_collection("DAG_STRUCTS")
    provider.insert_read_only_collection("DAG_STRUCTS", dag_structs)
    topo2dag = get_topo_dag_mapping(provider)
    provider.add_value("TOPO_DAG_MAPPING", topo2dag, is_function=True)


def do_TE_input_register_with_config(provider: ZenithProvider, params: NadirSpecConfiguration):
    topo2dag = get_topo_dag_mapping(provider)
    provider.register_value("TOPO_DAG_MAPPING", value=topo2dag, is_function=True)


def get_runtime_params(simple: bool = False) -> RuntimeParams:
    return RuntimeParams(
        component_setup_callable=lambda: set_to_default_component_configuration(simple=simple),
        module_setup_callable=set_to_default_module_assignment,
        app_input_setup_callables=[do_TE_input_setup_with_config],
        app_input_register_callables=[do_TE_input_register_with_config]
    )
