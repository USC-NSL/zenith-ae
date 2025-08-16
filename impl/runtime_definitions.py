import os
import multiprocessing
from dataclasses import dataclass
from typing import List, Dict, Tuple, Set, Callable, Optional
from pynadir.nadir import NadirModuleSpecification, NadirProcessSpecification, NadirModelValue
from pynadir.zenith_providers.provider import ZenithProvider
from pynadir.utils.logging import TitledLog
from atomics.common import MODEL_VALUES
from utils.input_setup import NadirSpecConfiguration


"""
Spawning a full `ZENITH` implementation has a bunch of hoops to go through.
Definitions within this file help give structure to how this is done. This
is the main "glue code" that actually makes the output of `NADIR` executable,
otherwise, some things are just not known to make it work from the specification.
"""


LOG_FILE_PATH = os.path.join(os.path.dirname(os.path.realpath(__file__)), 'zenith.log')
"""Where to output all logging events under `TitledLog`"""


RESPAWN_ON_KILL = True
"""Whether to rspawn processes that are killed by the OS (i.e. return code -9)"""


_LOG_QUEUE: Optional[multiprocessing.Queue] = None
"""Queue to collect logging info from spawned components"""


def create_log_queue():
    global _LOG_QUEUE
    assert _LOG_QUEUE is None
    _LOG_QUEUE = multiprocessing.Queue()
    TitledLog.set_out_queue(value=_LOG_QUEUE)


def get_log_queue() -> Optional[multiprocessing.Queue]:
    return _LOG_QUEUE


class DeathStatusCodes:
    OK = 0
    MUST_COME_BACK = -11
    NEVER_COME_BACK = 5
    KILLED = -9


@dataclass
class ProcessParams:
    """
    Specify each running `NadirProcess` instance.

    Attributes
    ----------
    process_specification: NadirProcessSpecification
        Specification of this process.
    operator_patch_list: List
        A list of operator patches
    macro_patch_list: List
        A list of macro patches
    """
    process_specification: NadirProcessSpecification
    operator_patch_list: List
    macro_patch_list: List


@dataclass
class ModuleParams:
    """
    Specify each running `NadirModule` instance.

    Attributes
    ----------
    module_specification: NadirModuleSpecification
        Specification of this module.
    operator_patch_list: List
        A list of operator patches
    macro_patch_list: List
        A list of macro patches
    
    Notes
    -----
    Operators and Macros are patched on the _module_ level.
    This _should_ be fine with you module composition. If it is 
    not, then either the module must be decomposed further or 
    the composition is not correct at all.
    """
    module_specification: NadirModuleSpecification
    operator_patch_list: List
    macro_patch_list: List


@dataclass
class RuntimeParams:
    """
    Specify runtime configurations.
    """
    component_setup_callable: Callable[[], None]
    module_setup_callable: Callable[[], None]
    app_input_setup_callables: List[Callable[[ZenithProvider, NadirSpecConfiguration], None]]
    app_input_register_callables: List[Callable[[ZenithProvider, NadirSpecConfiguration], None]]


"""Maps process names to their parameters and running instances"""
ProcessParamDict = Dict[str, ProcessParams]
ProcessInstanceDict = Dict[str, multiprocessing.Process]

"""Maps module names to their parameters and running instances"""
ModuleParamDict = Dict[str, ModuleParams]
ModuleInstanceDict = Dict[str, multiprocessing.Process]

"""Shows the configuration of NadirProcess instances within NadirModule instances"""
ModuleAssignmentDict = Dict[str, Tuple[NadirModelValue, Set[str]]]

"""Callable that sets the component and module configurations"""
set_algorithm_components: Callable[[], None]
set_algorithm_process_to_module_assignment: Callable[[], None]

"""These singular instances are used to prevent different runs of the controller from crossing each other"""
_ALGORITHM_PROCESS_PARAMS: ProcessParamDict = dict()
_ALGORITHM_PROCESS_INSTANCES: ProcessInstanceDict = dict()
_ALGORITHM_MODULE_PARAMS: ModuleParamDict = dict()
_ALGORITHM_MODULE_ASSIGNMENT: ModuleAssignmentDict = dict()
_ALGORITHM_MODULE_INSTANCES: ModuleInstanceDict = dict()

"""List of initializers that setup/introduce application inputs to all processes"""
_APP_INPUT_SETUPS: List[Callable[[ZenithProvider, NadirSpecConfiguration], None]] = []
_APP_INPUT_REGISTERS: List[Callable[[ZenithProvider, NadirSpecConfiguration], None]] = []


def get_component(root, component_name):
    return getattr(root, component_name)


def get_algorithm_process_param_dict() -> ProcessParamDict:
    global _ALGORITHM_PROCESS_PARAMS
    return _ALGORITHM_PROCESS_PARAMS
def get_algorithm_process_instance_dict() -> ProcessInstanceDict:
    global _ALGORITHM_PROCESS_INSTANCES
    return _ALGORITHM_PROCESS_INSTANCES
def get_algorithm_module_param_dict() -> ModuleParamDict:
    global _ALGORITHM_MODULE_PARAMS
    return _ALGORITHM_MODULE_PARAMS
def get_algorithm_module_assignment_dict() -> ModuleAssignmentDict:
    global _ALGORITHM_MODULE_ASSIGNMENT
    return _ALGORITHM_MODULE_ASSIGNMENT
def get_algorithm_module_instance_dict() -> ModuleInstanceDict:
    global _ALGORITHM_MODULE_INSTANCES
    return _ALGORITHM_MODULE_INSTANCES


def get_app_input_setups() -> List[Callable[[ZenithProvider, NadirSpecConfiguration], None]]:
    global _APP_INPUT_SETUPS
    return _APP_INPUT_SETUPS
def add_app_input_setup_callable(callable: Callable[[ZenithProvider, NadirSpecConfiguration], None]):
    global _APP_INPUT_SETUPS
    _APP_INPUT_SETUPS.append(callable)

def get_app_input_registers() -> List[Callable[[ZenithProvider, NadirSpecConfiguration], None]]:
    global _APP_INPUT_REGISTERS
    return _APP_INPUT_REGISTERS
def add_app_input_register_callable(callable: Callable[[ZenithProvider, NadirSpecConfiguration], None]):
    global _APP_INPUT_REGISTERS
    _APP_INPUT_REGISTERS.append(callable)


def set_algorithm_module_configuration():
    module_assignments = get_algorithm_module_assignment_dict()
    process_params = get_algorithm_process_param_dict()
    module_params = get_algorithm_module_param_dict()

    for module_name, mv_and_components in module_assignments.items():
        module_mv, module_component_names = mv_and_components
        threads = {
            component_name: (
                process_params[component_name].process_specification.impl,
                [pid.thread for pid in process_params[component_name].process_specification.threads]
            )
            for component_name in module_component_names
        }
        local_vars = {
            component_name: process_params[component_name].process_specification.local_vars
            for component_name in module_component_names
        }
        initial_labels = {
            component_name: process_params[component_name].process_specification.initial_label
            for component_name in module_component_names
        }
        module_spec = NadirModuleSpecification(
            mv_aggregate=MODEL_VALUES,
            module_id=module_mv,
            module_name=module_name,
            threads=threads,
            local_vars=local_vars,
            initial_labels=initial_labels
        )
        operator_patches = []
        macro_patches = []
        for component_name in module_component_names:
            operator_patches += process_params[component_name].operator_patch_list
            macro_patches += process_params[component_name].macro_patch_list

        operator_patch_list = list(set(operator_patches))
        macro_patch_list = list(set(macro_patches))
        module_params[module_name] = ModuleParams(
            module_specification=module_spec,
            operator_patch_list=operator_patch_list,
            macro_patch_list=macro_patch_list
        )


def setup_app_inputs(provider: ZenithProvider, params: NadirSpecConfiguration):
    setups = get_app_input_setups()
    assert len(setups) > 0, "No application input setups? That cannot be!"
    for setup_callable in setups:
        setup_callable(provider, params)


def set_runtime_configuration(config: RuntimeParams):
    global set_algorithm_components
    global set_algorithm_process_to_module_assignment

    set_algorithm_components = config.component_setup_callable
    set_algorithm_process_to_module_assignment = config.module_setup_callable
    if config.app_input_setup_callables:
        for callable in config.app_input_setup_callables:
            add_app_input_setup_callable(callable)
    if config.app_input_register_callables:
        for callable in config.app_input_register_callables:
            add_app_input_register_callable(callable)


def apply_runtime_configurations(input_provider: ZenithProvider, nadir_params: NadirSpecConfiguration):
    set_algorithm_process_to_module_assignment()
    set_algorithm_components()
    set_algorithm_module_configuration()
    setup_app_inputs(input_provider, nadir_params)
