import time
import utils
import queue
import signal
import random
import argparse
import threading
import multiprocessing
import runtime_definitions
import configurations.default_configuration
# import configurations.flapper_configuration
# import configurations.pr_configuration
from typing import TextIO, Optional, Dict
from pynadir.utils.logging import TitledLog
from frontend.openflow_frontend import OpenFlowFrontend
from pynadir.nadir import (NadirProcess, NadirModule, NadirModuleSpecification, 
                           NadirProcessSpecification, NadirPID)
from atomics.patches import *
from utils.fake_switch import FakeSwitch
from utils.input_setup import NadirSpecConfiguration, get_input_provider, clear_nadir_db
from utils.glob_setup import do_global_setup, get_global_provider
from utils.input_setup import make_input_provider
from utils.glob_setup import make_global_provider
from utils.ir_setup import NIBSetupParams, NIBSizeParams, setup_big, simple_setup
from runtime_definitions import ProcessParams, ModuleParams, DeathStatusCodes
from runtime_definitions import (
    get_algorithm_module_param_dict, get_algorithm_process_instance_dict,
    get_algorithm_process_param_dict, get_algorithm_module_instance_dict,
    get_app_input_registers
)


"""
HOW THIS WORKS:

The goal here is to spawn a full ZENITH controller. This includes:
- Configuring the NIB with the associated input (like IRs and DAGs)
- Picking up the required ZENITH components and configuring them
- Add applications (some of these may not even be generated from NADIR)
- Spawn the frontend (either the fake one for debugging, or the OpenFlow one)
- Spawn the watchdog that keeps an eye on each ZENITH module and respawns it
  if it dies.
- Finally, wait for user input to stop, then clean up the whole thing and exit.
"""


is_active = True
quit_event = threading.Event()

MAXIMUM_PROCESS_INITIALIZATION_WAIT_TIME = 5.0

FRONTEND: Optional[OpenFlowFrontend] = None

LOG_LEVEL: str = 'info'


def process_provider_initializer(process_specification: NadirProcessSpecification, 
                                 params: NadirSpecConfiguration, wait: Optional[int] = None):
    import utils.input_setup
    import utils.glob_setup

    utils.input_setup.make_input_provider()
    utils.glob_setup.make_global_provider()
    input_provider = utils.input_setup.get_input_provider()
    global_provider = utils.glob_setup.get_global_provider()

    if wait:
        time.sleep(wait)

    utils.input_setup.do_core_input_register_with_config(input_provider, params)
    # TODO: Application input register ...
    utils.glob_setup.do_global_register(global_provider, process_specification.threads, module_only=False)
    process_specification.input_provider = input_provider
    process_specification.global_provider = global_provider


def module_provider_initializer(module_specification: NadirModuleSpecification, 
                                params: NadirSpecConfiguration, wait: Optional[int] = None):
    import utils.input_setup
    import utils.glob_setup

    utils.input_setup.make_input_provider()
    utils.glob_setup.make_global_provider()
    input_provider = utils.input_setup.get_input_provider()
    global_provider = utils.glob_setup.get_global_provider()

    if wait:
        time.sleep(wait)

    utils.input_setup.do_core_input_register_with_config(input_provider, params)
    # TODO: Application input register ...
    pids = []
    for _, thread_ids in module_specification.threads.values():
        pids += [NadirPID(module_specification.module_id, thread_id) for thread_id in thread_ids]
    utils.glob_setup.do_global_register(global_provider, pids, module_only=True)

    # TODO: Fix these hard coded names ...
    if module_specification.module_name == "zenith-ofc":
        utils.glob_setup.do_ofc_module_setup(global_provider, params, is_module=True)
    elif module_specification.module_name == "zenith-rc":
        utils.glob_setup.do_rc_module_setup(global_provider, params, is_module=True)
    else:
        raise ValueError

    module_specification.input_provider = input_provider
    module_specification.global_provider = global_provider


def logging_initializer(provider, start_time: int, level: str, queue: Optional[multiprocessing.Queue] = None):
    set_log_level(level)
    TitledLog.set_start_time(start_time)
    TitledLog.set_out_queue(queue)


def logging_close(queue: Optional[multiprocessing.Queue] = None):
    if queue:
        queue.close()


def gather_logs(_queue: multiprocessing.Queue, output: Optional[TextIO] = None):
    try:
        while is_active:
            try:
                msg = _queue.get_nowait()
                if output:
                    output.write(msg + '\n')
                else:
                    print(msg)
            except queue.Empty:
                if output:
                    output.flush()
                quit_event.wait(3.0)
    finally:
        _queue.close()


def spawn_processes(param_dict: Dict[str, ProcessParams], 
                    nadir_params: NadirSpecConfiguration) -> Dict[str, multiprocessing.Process]:
    processes: Dict[str, multiprocessing.Process] = {
        proc_name: multiprocessing.Process(target=NadirProcess.spawn, args=(
            value.process_specification,
            process_provider_initializer,
            {
                "params": nadir_params,
                "wait": MAXIMUM_PROCESS_INITIALIZATION_WAIT_TIME * random.random()
            },
            value.operator_patch_list,
            value.macro_patch_list,
            # Initialize logging (in particular, the starting timestamp)
            [(logging_initializer,{
                "start_time": TitledLog.get_start_time(),
                "level": LOG_LEVEL,
                "queue": runtime_definitions.get_log_queue()
            })] + 
            # Initialize (register) input providers for applications
            [(
                callable, {
                    "params": nadir_params
                }
            ) for callable in get_app_input_registers()],
            [],
            [(
                logging_close, {
                    "queue": runtime_definitions.get_log_queue()
            })]
        ))
        for proc_name, value in param_dict.items()
    }

    TitledLog.info("boot", f"Will now spawn {len(processes)} processes: {', '.join(processes.keys())}")

    for process in processes.values():
        process.start()

    return processes


def spawn_modules(param_dict: Dict[str, ModuleParams], 
                  nadir_params: NadirSpecConfiguration) -> Dict[str, multiprocessing.Process]:
    modules: Dict[str, multiprocessing.Process] = {
        module_name: multiprocessing.Process(target=NadirModule.spawn, args=(
            value.module_specification,
            module_provider_initializer,
            {
                "params": nadir_params,
                "wait": MAXIMUM_PROCESS_INITIALIZATION_WAIT_TIME * random.random()
            },
            value.operator_patch_list,
            value.macro_patch_list,
            # Initialize logging (in particular, the starting timestamp)
            [(logging_initializer,{
                "start_time": TitledLog.get_start_time(),
                "level": LOG_LEVEL,
                "queue": runtime_definitions.get_log_queue()
            })] + 
            # Initialize (register) input providers for applications
            [(
                callable, {
                    "params": nadir_params
                }
            ) for callable in get_app_input_registers()],
            [],
            [(
                logging_close, {
                    "queue": runtime_definitions.get_log_queue()
            })]
        ))
        for module_name, value in param_dict.items()
    }

    TitledLog.info("boot", f"Will now spawn {len(modules)} modules: {', '.join(modules.keys())}")

    for module in modules.values():
        module.start()

    return modules


def int_handler(_, _frame):
    global is_active, quit_event, FRONTEND

    processes = get_algorithm_process_instance_dict()
    modules = get_algorithm_module_instance_dict()

    if FRONTEND is not None:
        FRONTEND.int_handler()
        FRONTEND.wait_for_exit()
    if processes is not None:
        for proc in processes.values():
            proc.kill()
    if modules is not None:
        for proc in modules.values():
            proc.kill()

    is_active = False
    quit_event.set()


def respawn_component(component_name: str, nadir_params: NadirSpecConfiguration, modular: bool = False):
    if modular:
        TitledLog.info("wathcdog", f"Respawning dead module {component_name}")
        component_params = get_algorithm_module_param_dict()
        component_instances = get_algorithm_module_instance_dict()
    else:
        TitledLog.info("watchdog", f"Respawning dead process {component_name}")
        component_params = get_algorithm_process_param_dict()
        component_instances = get_algorithm_process_instance_dict()
    
    value = component_params[component_name]
    if modular:
        component = multiprocessing.Process(target=NadirModule.spawn, args=(
            value.module_specification,
            module_provider_initializer,
            {
                "params": nadir_params,
                "wait": MAXIMUM_PROCESS_INITIALIZATION_WAIT_TIME * random.random()
            },
            value.operator_patch_list,
            value.macro_patch_list,
            # Initialize logging (in particular, the starting timestamp)
            [(logging_initializer,{
                "level": LOG_LEVEL,
                "start_time": TitledLog.get_start_time()
            })] + 
            # Initialize (register) input providers for applications
            [(
                callable, {
                    "params": nadir_params
                }
            ) for callable in get_app_input_registers()],
            []
        ))
        component.start()
        TitledLog.success("watchdog", f"Module {component_name} forked with PID {component.pid}")
    else:
        component = multiprocessing.Process(target=NadirProcess.spawn, args=(
            value.process_specification,
            process_provider_initializer,
            {
                "params": nadir_params,
                "wait": MAXIMUM_PROCESS_INITIALIZATION_WAIT_TIME * random.random()
            },
            value.operator_patch_list,
            value.macro_patch_list,
            # Initialize logging (in particular, the starting timestamp)
            [(logging_initializer,{
                "level": LOG_LEVEL,
                "start_time": TitledLog.get_start_time()
            })] + 
            # Initialize (register) input providers for applications
            [(
                callable, {
                    "params": nadir_params
                }
            ) for callable in get_app_input_registers()],
            []
        ))
        component.start()
        TitledLog.success("watchdog", f"Process {component_name} forked with PID {component.pid}")

    old_component = component_instances.pop(component_name)
    try:
        old_component.close()
    finally:
        component_instances[component_name] = component


def clear_component(component_name: str, modular: bool = False):
    if modular:
        components = get_algorithm_module_instance_dict()
    else:
        components = get_algorithm_process_instance_dict()
    old_component = components.pop(component_name)
    try:
        old_component.close()
    finally:
        if modular:
            TitledLog.warning("watchdog", f"Module {component_name} has been fully cleaned up, will not respawn.")
        else:
            TitledLog.warning("watchdog", f"Process {component_name} has been fully cleaned up, will not respawn.")


def watchdog(nadir_spec: NadirSpecConfiguration, modular: bool = False):
    global is_active, quit_event

    if modular:
        processes = get_algorithm_module_instance_dict()
    else:
        processes = get_algorithm_process_instance_dict()

    TitledLog.info("watchdog", f"Watchdog will watch for processes: {', '.join(processes.keys())}")

    repeat = False
    while is_active:
        for name, proc in processes.items():
            if proc.exitcode is not None:
                if proc.exitcode == DeathStatusCodes.MUST_COME_BACK:
                    TitledLog.warning("watchdog", f"Process {name} was killed by FO, we will now respawn it.")
                    respawn_component(name, nadir_spec, modular=modular)
                    repeat = True
                    break
                elif proc.exitcode == DeathStatusCodes.NEVER_COME_BACK:
                    TitledLog.warning("watchdog", f"Process {name} has been terminated by FO.")
                    clear_component(name, modular=modular)
                    repeat = True
                    break
                elif proc.exitcode == DeathStatusCodes.OK:
                    TitledLog.info("watchdog", f"Process {name} returned normally.")
                    clear_component(name, modular=modular)
                    repeat = True
                    break
                elif proc.exitcode == -9:
                    if runtime_definitions.RESPAWN_ON_KILL:
                        TitledLog.warning("watchdog", f"Process {name} was killed by the OS. Policy is to RESPAWN.")
                        respawn_component(name, nadir_spec, modular=modular)
                    else:
                        TitledLog.warning("watchdog", f"Process {name} was killed by the OS. Policy is to IGNORE.")
                        clear_component(name, modular=modular)
                    repeat = True
                    break
                else:
                    TitledLog.fail("watchdog", f"Unknown return code {proc.exitcode} received for {name}, aborting")
                    int_handler(None, None)
                    return
        
        if len(processes) == 0:
            TitledLog.success("watchdog", "All components have exited normally.")
            is_active = False
            quit_event.set()
            return
        if repeat:
            repeat = False
            continue
        quit_event.wait(3.0)


def run(nib_size_params: NIBSizeParams = None, nib_params: NIBSetupParams = None,
        topo_size: int = -1, watch: bool = True, modular: bool = False,
        with_fakes: bool = False, with_frontend: bool = False):
    """
    Zenith processes are spawned separately so that they can be killed
    and go through all sort of horrible stuff without anything going
    wrong.

    The OpenFlow frontend we will spawn here, and we won't actually kill
    it, since that would be pointless (note that without the frontend, 
    Zenith won't receive any input, it wouldn't be able to tell that something
    is wrong without the frontend feeding that information to it).
    """

    global FRONTEND

    # Setup IRs
    if nib_params is not None:
        assert nib_size_params is None
        # setup_nib(nib_params, ir_have_id=True, dags_have_id=True)
    elif nib_size_params is not None:
        assert nib_params is None
        nib_params = setup_big(nib_size_params)
    else:
        nib_params = simple_setup(with_datapaths=True)

    # Create nadir params from the nib param
    assert nib_params.datapaths is not None or topo_size > 0
    nadir_params = NadirSpecConfiguration(
        MaxDAGID=len(nib_params.dags),
        MaxNumIRs=len(nib_params.irs),
        TopologySize=topo_size if topo_size > 0 else len(nib_params.datapaths)
    )

    # Handles SIGINT for shutting down
    for sig in ('TERM', 'HUP', 'INT'):
        signal.signal(getattr(signal, 'SIG' + sig), int_handler)

    # Initiate input and global variables if needed (ONLY CALLED ONCE!)
    make_input_provider()
    make_global_provider()
    input_provider = get_input_provider()
    global_provider = get_global_provider()

    # Setup the core of ZENITH
    clear_nadir_db(global_provider)
    utils.input_setup.do_core_input_setup_with_config(input_provider, nadir_params)
    do_global_setup(global_provider, params=nadir_params, module_only=modular)

    # Now, bring up the OpenFlow frontend
    if args.with_frontend:
        assert FRONTEND is None
        FRONTEND = OpenFlowFrontend(topo_size=topo_size, max_num_irs=nadir_params.MaxNumIRs)
        FRONTEND.start()
        TitledLog.info("frontend", f"Waiting for {topo_size} switches to connect")
        FRONTEND.wait_until_topology_is_ready()
        if not is_active:
            return
        TitledLog.special_info("frontend", "Topology size reached!")
        FRONTEND.serve_zenith()

    # Apply all runtime configurations
    runtime_definitions.apply_runtime_configurations(input_provider, nadir_params)

    # Now, we can spawn our processes
    processes = get_algorithm_process_instance_dict()
    modules = get_algorithm_module_instance_dict()
    process_params = get_algorithm_process_param_dict()
    module_params = get_algorithm_module_param_dict()

    assert len(processes) == 0
    assert len(modules) == 0

    TitledLog.set_start_time()

    if not modular:
        TitledLog.info("config", "(NON-MODULAR) Will spawn each Nadir process as separate child")
        processes.update(spawn_processes(process_params, nadir_params))
    else:
        TitledLog.info("config", "(MODULAR) Nadir processes will be bundled into modules when needed")
        modules.update(spawn_modules(module_params, nadir_params))

    # Now, spawn fake-switch if needed
    if with_fakes:
        fake_switch_thread = threading.Thread(target=spawn_fake_switches, args=(nib_size_params.num_switches,))
        fake_switch_thread.start()

    if watch:
        # Respawn dead processes
        watchdog(nadir_params, modular=modular)

        for proc in processes.values():
            proc.join()
        if with_fakes:
            fake_switch_thread.join()
    else:
        if not modular:
            return processes
        else:
            return modules


def teardown_run(procs: Dict[str, multiprocessing.Process]):
    for name, proc in procs.items():
        TitledLog.warning("watchdog", f"Terminating process: {name}")
        proc.terminate()
    for proc in procs.values():
        try:
            proc.join(5.0)
            proc.close()
        except ValueError:
            pass


def spawn_fake_switches(num_switches: int):
    switch = FakeSwitch(num_switches=num_switches, provider=get_input_provider())
    switch.run()


def configure_and_run(args, log_file: Optional[TextIO] = None):
    # Some checks
    assert not (args.with_fake and args.with_frontend), \
        "Can only specify at most one of `--with-frontend` or `--with-fake`"

    # Setup the log
    runtime_definitions.create_log_queue()
    logging_thread = threading.Thread(
        target=gather_logs, 
        args=(runtime_definitions.get_log_queue(), log_file))
    logging_thread.start()
    
    # Set configurations parameters (for now, use the default one)
    config = configurations.default_configuration.get_runtime_params()
    # config = configurations.pr_configuration.get_runtime_params()
    # config = configurations.flapper_configuration.get_runtime_params()
    runtime_definitions.set_runtime_configuration(config)

    if args.num_switches is not None:
        assert args.num_irs is not None and args.dag_size is not None
        size_params = NIBSizeParams(args.num_switches, args.num_irs, args.dag_size)
        run(nib_size_params=size_params, topo_size=args.num_switches, modular=args.modular,
            with_fakes=args.with_fake)
    else:
        assert args.num_irs is None and args.dag_size is None
        run(modular=args.modular, with_fakes=args.with_fake)
    
    logging_thread.join()


def set_log_level(level: str):
    global LOG_LEVEL
    LOG_LEVEL = level
    TitledLog.set_log_level({'trace': 0, 'debug': 1, 'info': 2, 'warn': 3, 'error': 4}[level])


if __name__ == '__main__':
    """
    DB connections are not fork-safe, thus we spawn fresh Python interpreters, sharing
    basically no state with this code, and the configure them manually.
    """
    multiprocessing.set_start_method('spawn')

    parser = argparse.ArgumentParser()

    parser.add_argument('--num-switches', type=int, help='Number of switches')
    parser.add_argument('--num-irs', type=int, help='Number of total IRs to process')
    parser.add_argument('--dag-size', type=int, help='Number of IRs per dag')
    parser.add_argument('--modular', action='store_true', help='Run as modules')
    parser.add_argument('--with-fake', action='store_true', help='Bring up fake switches with the controller')
    parser.add_argument('--with-frontend', action='store_true', help='Bring up the OpenFlow frontend')
    parser.add_argument('--log', action='store_true', help='Output log to a file instead of stdout')
    parser.add_argument('--log-level', choices=['debug', 'info', 'warn', 'error'], default='info', help='PyNadir log level')

    args = parser.parse_args()

    set_log_level(args.log_level)

    if args.log:
        with open(runtime_definitions.LOG_FILE_PATH, "w") as log_file:
            configure_and_run(args, log_file)
    else:
        configure_and_run(args)
