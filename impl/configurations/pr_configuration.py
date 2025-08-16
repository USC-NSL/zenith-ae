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
import apps.reconciler as PR
import configurations.default_configuration
from runtime_definitions import *
from atomics.patches import *
from atomics.common import MODEL_VALUES, NadirPID
from pynadir.utils.logging import TitledLog


def set_to_pr_module_assignment():
    module_assignments = get_algorithm_module_assignment_dict()
    assert len(module_assignments) == 0

    TitledLog.info("config", "Using `DAG-FLAPPER` module assignment")

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
            "ControllerSeq",
            "PeriodicReconciler"
        }
    )


def set_to_pr_component_configuration(simple: bool = False):
    TitledLog.info("config", "Using `DAG-FLAPPER` component configuration")

    if simple:
        # controllerSequencer = get_component(SimpleSEQ, "controllerSequencer")
        # controllerBossSequencer = get_component(SimpleSEQ, "controllerBossSequencer")
        # controllerWorkerThreads = get_component(SimpleWP, "controllerWorkerThreads")
        # controllerEventHandler = get_component(SimpleEH, "controllerEventHandler")
        # controllerMonitoringServer = get_component(SimpleMS, "controllerMonitoringServer")
        # rcNibEventHandler = get_component(SimpleTE, "rcNibEventHandler")
        # controllerTrafficEngineering = get_component(TE, "controllerTrafficEngineering")
        raise ValueError("This code path is no longer needed")
    else:
        controllerSequencer = get_component(SEQ, "controllerSequencer")
        controllerBossSequencer = get_component(SEQ, "controllerBossSequencer")
        controllerWorkerThreads = get_component(WP, "controllerWorkerThreads")
        controllerEventHandler = get_component(EH, "controllerEventHandler")
        controllerMonitoringServer = get_component(MS, "controllerMonitoringServer")
        rcNibEventHandler = get_component(TE, "rcNibEventHandler")
        controllerTrafficEngineering = get_component(TE, "controllerTrafficEngineering")

    periodicReconciler = get_component(PR, "controllerReconciliationScheduler")

    for cmp in [
        controllerSequencer,
        controllerBossSequencer,
        controllerWorkerThreads,
        controllerEventHandler,
        controllerMonitoringServer,
        rcNibEventHandler,
        controllerTrafficEngineering,
        periodicReconciler
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
                "DAGID": None,
                "nxtDAG": None,
                "deleterID": None,
                "setRemovableIRs": set(),
                "currIR": None,
                "currIRInDAG": None,
                "nxtDAGVertices": set(),
                "setIRsInDAG": set(),
                "prev_dag": None,
                "topoChangeEvent": None,
                "currSetDownSw": set(),
                "prev_dag_id": None,
                "init": 1
            },
            initial_label="ControllerTEProc"
        ),
        operator_patch_list=[
            # ("getSetRemovableIRs", getSetRemovableIRs_patched),
            ("getDualOfIR", getDualOfIR_patched)
            # ("getSwitchForIR", getSwitchForIR_patched)
        ],
        macro_patch_list=[]
    )
    algorithm_process_params["ControllerBoss"] = ProcessParams(
        process_specification=NadirProcessSpecification(
            impl=controllerBossSequencer, mv_aggregate=MODEL_VALUES,
            process_name="zenith-boss-seq",
            threads=[NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.CONT_BOSS_SEQ)],
            local_vars={
                "seqEvent": None,
                "worker": None
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
                "IRSet": set(),
                "IRDoneSet": set()
            },
            initial_label="ControllerSeqStateReconciliation"
        ),
        operator_patch_list=[
            ("getDualOfIR", getDualOfIR_patched),
            # ("allIRsInDAGInstalled", allIRsInDAGInstalled_patched),
            # ("allIRsInDAGAreStable", allIRsInDAGAreStable_patched),
            # ("dagObjectShouldBeProcessed", dagObjectShouldBeProcessed_patched),
            # ("getSwitchForIR", getSwitchForIR_patched)
        ],
        macro_patch_list=[]
    )
    algorithm_process_params["WorkerPool"] = ProcessParams(
        process_specification=NadirProcessSpecification(
            impl=controllerWorkerThreads, mv_aggregate=MODEL_VALUES,
            process_name="zenith-wp",
            threads=[
                NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.t0),
                NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.t1),
                # NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.t2)
            ],
            local_vars={
                "nextIRIDToSend": None,
                "index": None
            },
            initial_label="ControllerThreadStateReconciliation"
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
            # ("getIRSetToReset", getIRSetToReset_patched),
            # ("getSwitchForIR", getSwitchForIR_patched)
        ],
        macro_patch_list=[]
    )
    algorithm_process_params["PeriodicReconciler"] = ProcessParams(
        process_specification=NadirProcessSpecification(
            impl=periodicReconciler, mv_aggregate=MODEL_VALUES,
            process_name="zenith-pr",
            threads=[NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.CONT_RECONCILER)],
            local_vars={
                "RECONCILIATION_PERIOD": 5,
                "switches": None,
                "inflight": 0,
                "coeff": 1.0
            },
            initial_label="ControllerReconciler"
        ),
        operator_patch_list=[],
        macro_patch_list=[]
    )
    algorithm_process_params["MonitoringServer"] = ProcessParams(
        process_specification=NadirProcessSpecification(
            impl=controllerMonitoringServer, mv_aggregate=MODEL_VALUES,
            process_name="zenith-ms",
            threads=[NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.CONT_MONITOR)],
            local_vars={
                "msg": None,
                "irID": None,
                "removedIR": None,
                "shouldBeDones": []
            },
            initial_label="ControllerMonitorCheckIfMastr"
        ),
        operator_patch_list=[
            ("getDualOfIR", getDualOfIR_patched),
            ("getIRIDForFlow", getIRIDForFlow_patched),
            # ("getSwitchForIR", getSwitchForIR_patched)
        ],
        macro_patch_list=[],
    )


def do_pr_input_register_with_config(provider: ZenithProvider, params: NadirSpecConfiguration):
    # import atomics.common
    # atomics.common.MODEL_VALUES.add_mv("CONT_RECONCILER")
    topo2dag = configurations.default_configuration.get_topo_dag_mapping(provider)
    provider.register_value("TOPO_DAG_MAPPING", value=topo2dag, is_function=True)


def get_runtime_params(simple: bool = False) -> RuntimeParams:
    return RuntimeParams(
        component_setup_callable=lambda: set_to_pr_component_configuration(simple=simple),
        module_setup_callable=set_to_pr_module_assignment,
        app_input_setup_callables=[configurations.default_configuration.do_TE_input_setup_with_config],
        app_input_register_callables=[do_pr_input_register_with_config]
    )