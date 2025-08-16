import copy
import time
import signal
import importlib
import threading
import setproctitle
import multiprocessing
from dataclasses import dataclass
from typing import List, Dict, Any, Tuple, Callable, Type, Optional
from pynadir.params import NadirGlobalParams
from pynadir.exceptions import ExecutionHalted, RepeatLabel, WaitThenRepeat
from pynadir.structures import (
    NadirModelValue, NadirModelValueAggregate, NadirPID
)
from pynadir.providers import AbstractProvider, NadirSimpleProvider
from pynadir.utils.logging import TitledLog


WAIT_TIMEOUT = 5
NADIR_DEFAULT_START_LABEL = "_nadir_start_function"
NADIR_DEFAULT_END_LABEL = "_nadir_end_function"


@dataclass
class NadirProcessSpecification:
    """
    Specifies all the input required to spawn a real instance of a Nadir
    process. With the exception of the providers, attributes need to be 
    completely available and initialized when a Nadir process is being 
    created.
    There is nothing that Nadir can do about making this process easier
    or automatic, users must know the real-world requirements of the
    environment in which they run their application and define this
    structure accordingly.

    Attributes
    ----------
    impl: Type[NadirProcess]
        The (most likely auto-generated) class that implements this Nadir
        process. It MUST subclass `NadirProcess`.
    mv_aggregate: NadirModelValueAggregate
        The Model Value aggregator. This _SHOULD_ be complete, otherwise
        an error will happen at some point most likely.
    process_name: str
        A string for the name of this process. This need not be unique
        among processes, the Nadir PID will handle indexing processes.
        However, if this name is to be used in lieu of the PID to address
        the process (like signaling it), then it should probably be unique.
        The title of the Nadir process (as seen in `top` and `ps -aux` and
        friends) will be set to this value.
    threads: List[NadirPID]
        A _unique_ `NadirPID` instance for each thread that will operate
        under this process. Since a Nadir process implements a PlusCal
        process, all of these threads will execute the same code and
        start from the same initial label.
    local_vars: Dict[str, Any]
        Description of all local variables under this process. Each thread
        under this process will get a clone of this dictionary just for 
        itself.
    initial_label: str
        Initial lable of this process. Each thread will start from there
        as well.
    input_provider: Optional[AbstractProvider] = None
        The input provider abstracts PlusCal `CONSTANT` values. These are
        inputs to the specification and are read-only. These values will
        exist on the Nadir DB, but processes will always cache them so 
        they don't have to bother the DB each time they query these values.
    global_provider: Optional[AbstractProvider] = None
        The global provider abstracts any manipulation of global variables
        among all processes. This global variable belongs _only_ to this
        process, but it interacts with the same DB (namely the Nadir DB).
    with_fo: Optional[bool] = None
        Whether or not to connect this process to an FO instance.
    
    Notes
    -----
    The provider attributes (i.e. `input_provider` and `global_provider`) are
    marked optional since they are most likely _NOT_ available the moment that
    a Nadir process needs to be spawned.
    In such a case, the user _MUST_ provide a method that creates these
    providers, and by the time this specification is used to pass arguments 
    to `NadirProcess.__init__`, _ALL_ of its attributes _MUST_ be fully known.
    """
    impl: Type
    mv_aggregate: NadirModelValueAggregate
    process_name: str
    threads: List[NadirPID]
    local_vars: Dict[str, Any]
    initial_label: str
    input_provider: Optional[AbstractProvider] = None
    global_provider: Optional[AbstractProvider] = None
    with_fo: Optional[bool] = None

    def __post_init__(self):
        assert issubclass(self.impl, NadirProcess)


class NadirProcess:
    """
    This base class implements a typical Nadir process, which usually is just implemented
    as a set of threads.
    
    A process will give a set of PIDs, which will be assigned as names for its threads. The
    process will then also receive a dict of local variables, which will be instantiated and
    passed to each individual thread (no synchronization is thus needed for these variables).
    """

    num_cvs = 0

    WITH_FO = False
    REPORT_CONVERGENCE = False

    LOG_PROC_NAME_LEN = 30
    LOG_LABEL_NAME_LEN = 60

    def __init__(self, mv_aggregate: NadirModelValueAggregate, name: str, thread_names: List[NadirPID],
                 local_vars: Dict[str, Any] = None,
                 initial_label: str = NADIR_DEFAULT_START_LABEL,
                 with_fo: bool = None, module = None) -> None:

        if local_vars is None:
            local_vars = dict()

        self.mv_aggregate = mv_aggregate
        self.name = name
        self.thread_names = thread_names
        self.local_provider = NadirSimpleProvider(local_vars)
        self.initial_label = initial_label
        self.with_fo = with_fo
        self.module = module

        self.is_active: bool = True
        self.quit_event: threading.Event = threading.Event()
        self._cvs = [threading.Condition(threading.Lock()) for i in range(self.num_cvs)]
        self._rmutex: threading.RLock = threading.RLock()
        self.done_barrier: threading.Barrier = threading.Barrier(len(thread_names), timeout=WAIT_TIMEOUT)
        self.thread_exit_code: Dict[NadirPID, Optional[int]] = {pid: None for pid in thread_names}

        self.input_provider: Optional[AbstractProvider] = None
        self.global_provider: Optional[AbstractProvider] = None

        # if self.with_fo is not None:
        #     if self.with_fo:
        #         self.fo_clients = {
        #             pid: FOClient(pid) for pid in self.thread_names
        #         }
        #     else:
        #         self.fo_clients = None
        # else:
        #     if self.WITH_FO:
        #         self.fo_clients = {
        #             pid: FOClient(pid) for pid in self.thread_names
        #         }
        #     else:
        #         self.fo_clients = None

        # Handles SIGINT for shutting down
        for sig in ('TERM', 'HUP', 'INT'):
            signal.signal(getattr(signal, 'SIG' + sig), self.int_handler)

        self.threads = [threading.Thread(target=self.switch) for _ in thread_names]
        for i in range(len(self.threads)):
            self.threads[i].name = thread_names[i]
    
    def is_using_fo(self):
        return self.with_fo or self.WITH_FO
    
    def get_fo_client(self):
        assert self.is_using_fo()
        # return self.fo_clients[self.get_pid()]

    def log_trace(self, msg: str):
        TitledLog.trace("nadir", TitledLog.create_title(
            self.get_thread_name(), padding=self.LOG_PROC_NAME_LEN, 
            with_timestamp=False) + " " + msg)    
    def log_info(self, msg: str):
        TitledLog.info("nadir", TitledLog.create_title(
            self.get_thread_name(), padding=self.LOG_PROC_NAME_LEN, 
            with_timestamp=False) + " " + msg)
    def log_debug(self, msg: str):
        TitledLog.debug("nadir", TitledLog.create_title(
            self.get_thread_name(), padding=self.LOG_PROC_NAME_LEN, 
            with_timestamp=False) + " " + msg)
    def log_warning(self, msg: str):
        TitledLog.warning("nadir", TitledLog.create_title(
            self.get_thread_name(), padding=self.LOG_PROC_NAME_LEN, 
            with_timestamp=False) + " " + msg)
    def log_fail(self, msg: str):
        TitledLog.fail("nadir", TitledLog.create_title(
            self.get_thread_name(), padding=self.LOG_PROC_NAME_LEN, 
            with_timestamp=False) + " " + msg)
    def log_success(self, msg: str):
        TitledLog.success("nadir", TitledLog.create_title(
            self.get_thread_name(), padding=self.LOG_PROC_NAME_LEN, 
            with_timestamp=False) + " " + msg)
    
    @staticmethod
    def spawn(
        specification: NadirProcessSpecification,
        process_provider_initializer: Callable,
        process_provider_initializer_args: Optional[Dict[str, Any]] = None,
        op_patches: Optional[List[Tuple[str, Callable]]] = None,
        macro_patches: Optional[List[Tuple[str, Callable]]] = None,
        initializers: Optional[List[Tuple[Callable, Dict[str, Any]]]] = None,
        finalizers: Optional[List[Tuple[Callable, Dict[str, Any]]]] = None,
        cleaners: Optional[List[Tuple[Callable, Dict[str, Any]]]] = None
    ):
        """
        This method is meant to be called with the multiprocessing
        framework. It will spawn a Nadir process with a given configuration,
        so for example, patches are made sure not to cross each other.
        """

        # First, set the name of the process
        setproctitle.setproctitle(specification.process_name)

        # Now, initialize the providers if needed
        if specification.input_provider is None or specification.global_provider is None:
            if process_provider_initializer_args is None:
                process_provider_initializer_args = dict()
            process_provider_initializer(
                specification,
                **process_provider_initializer_args
            )

        # Make sure the specification is now fully initialized
        assert specification.global_provider is not None
        assert specification.input_provider is not None

        # Now, call the initializers
        if initializers is not None:
            for item in initializers:
                func, args = item
                func(provider=specification.input_provider, **args)

        # Patch operators and macros
        patch_macros_and_operators_for_structured_nadir_code(op_patches, macro_patches)

        try:
            # Create the process
            proc: NadirProcess = specification.impl(
                mv_aggregate=specification.mv_aggregate,
                name=specification.process_name,
                thread_names=specification.threads,
                local_vars=specification.local_vars,
                initial_label=specification.initial_label,
                with_fo=specification.with_fo,
                module=None
            )
            actual_pid = multiprocessing.current_process().pid

            # TODO: Should we register PIDs for input provider as well?

            # Call the finalizers, passing the processes as first argument
            if finalizers is not None:
                for item in finalizers:
                    func, args = item
                    func(proc, **args)

            # Set providers for the process
            proc.set_input_provider(specification.input_provider)
            proc.set_global_provider(specification.global_provider)

            TitledLog.info("nadir", f"Spawning Nadir process {proc.name} with PID {actual_pid}")
            proc.start_and_wait()
        finally:
            if cleaners is not None:
                for item in cleaners:
                    func, args = item
                    func(**args)
    
    @classmethod
    def use_fo(cls):
        assert cls.WITH_FO is False
        cls.WITH_FO = True
    
    @classmethod
    def just_report_cts(cls):
        cls.WITH_FO = True
        cls.REPORT_CONVERGENCE = True

    def int_handler(self, signo=None, _frame=None):
        self.log_warning("Force exit on all threads")
        if NadirGlobalParams.is_active:
            NadirGlobalParams.stop()
        self.is_active = False
        self.quit_event.set()

    def graceful_exit(self):
        self.log_success("All threads are done, will now exit.")
        self.is_active = False
        self.quit_event.set()

    def set_module(self, module: Any):
        assert self.module is None
        self.module = module

    def set_global_provider(self, provider):
        assert self.global_provider is None
        assert issubclass(provider.__class__, AbstractProvider)

        self.global_provider = provider
        for pid in self.thread_names:
            self.global_provider.register_pid(pid)
        
        fz_pid = frozenset(self.thread_names)
        for i in range(len(self._cvs)):
            self.global_provider.register_cv(fz_pid, self._cvs[i], i)

    def set_input_provider(self, provider):
        assert self.input_provider is None
        assert issubclass(provider.__class__, AbstractProvider)
        self.input_provider = provider

    def start(self):
        assert self.global_provider

        # if self.fo_clients and not self.REPORT_CONVERGENCE:
        #     for pid, client in self.fo_clients.items():
        #         if client.register():
        #             # print(f"PID {pid} registered to FO. Proceeding ...")
        #             pass
        #         else:
        #             print(f"PID {pid} was rejected by FO. Terminating ...")
        #             self.cleanup()
        #             return

        for thread in self.threads:
            thread.start()

    def start_and_wait(self):
        self.start()

        while self.is_active and NadirGlobalParams.is_active:
            self.quit_event.wait(WAIT_TIMEOUT)
        
        self.cleanup()

    def get_thread_name(self) -> str:
        return threading.current_thread().name
    def get_pid(self) -> NadirPID:
        return NadirPID.from_str(self.get_thread_name(), self.mv_aggregate)
    def get_mid(self) -> NadirModelValue:
        return self.get_pid().module
    def get_tid(self) -> NadirModelValue:
        return self.get_pid().thread
    
    def _release_locks(self):
        for cv in self._cvs:
            if cv._lock.locked(): # noqa
                """
                This can be replaced by `notify`, but there is no such
                semantic baked into TLA+, so we avoid doing that.
                """
                cv.release()

    def switch(self):
        # print(f"Nadir process {self.name} spawned thread {threading.current_thread().name}")
        
        current_label, current_locals = self.initial_label, copy.deepcopy(self.local_provider)
        current_locals.register_pid(self.get_pid())

        # print(f"Nadir process thread {self.name} :: {threading.current_thread().name} will execute the {current_label} step")

        # if self.fo_clients:
        #     fo_client = self.fo_clients[self.get_pid()]
        # else:
        #     fo_client = None

        while self.is_active:
            label_method = getattr(self, current_label)

            # if fo_client and not self.REPORT_CONVERGENCE:
            #     fo_client.report_current_step(current_step=current_label)

            t_start_with_sleep = time.perf_counter_ns()
            t_start_without_sleep = time.process_time_ns()
            try:
                new_label = label_method(current_locals)
                # print(f"Nadir process thread {self.name} :: {threading.current_thread().name} will execute the {new_label} step")
            except ExecutionHalted:
                self._release_locks()
                current_locals.abort(self.get_pid())
                self.global_provider.abort(self.get_pid())
                break
            except RepeatLabel:
                current_locals.abort(self.get_pid())
                self.global_provider.abort(self.get_pid())
                t_start_without_sleep = time.process_time_ns()
                continue
            except WaitThenRepeat as e:
                current_locals.abort(self.get_pid())
                self.global_provider.abort(self.get_pid())
                time.sleep(e.wait_for)
                continue
            
            # The previous call might have been blocking, check for exit condition
            if not self.is_active or not len(new_label):
                self._release_locks()
                break

            try:
                current_locals.commit(self.get_pid())
                self.global_provider.commit(self.get_pid())
            except WaitThenRepeat as e:
                TitledLog.warning("nadir", f"Transaction failed for label {current_label} ...")
                current_locals.abort(self.get_pid())
                self.global_provider.abort(self.get_pid())
                time.sleep(e.wait_for)
                continue

            # Update label and globals
            old_label = current_label
            current_label = new_label

            # Make changes visible by releasing all acquired locks from the previous step
            self._release_locks()

            self.log_trace(
                TitledLog.create_title(old_label, padding=self.LOG_LABEL_NAME_LEN, 
                                       with_timestamp=False, upper=False) + " "
                f"{str(round((time.perf_counter_ns() - t_start_with_sleep) / 1e6, 1))} ms :: "
                f"{str(round((time.process_time_ns() - t_start_without_sleep) / 1e6, 1))} ms")

        if self.is_active:
            self.log_info(f"Thread {self.get_thread_name()} will now wait for exit.")
            self.wait_for_exit()

    def wait_for_exit(self):
        while self.is_active:
            i = self.done_barrier.wait(5)
            if i is not None:
                if i == 0:
                    self.graceful_exit()
                break

    def _nadir_start_function(self, process_local_vars) -> str:
        self.log_debug("Hello World!")
        return NADIR_DEFAULT_END_LABEL

    def _nadir_end_function(self, process_local_vars) -> str:
        self.log_debug(f"Thread {self.get_thread_name()} is done.")
        return ""

    def cleanup(self):
        if self.is_active:
            self.is_active = False
            self.quit_event.set()
        
        # if self.fo_clients:
        #     for client in self.fo_clients.values():
        #         client.cleanup()
        
        self._cleanup()

    def _cleanup(self):
        if self.module is not None:
            self.module.report_exit(0)
        # if self.fo_clients is not None:
        #     status_codes = list(filter(
        #         lambda code: code != 0, {client.get_death_status_code() for client in self.fo_clients.values()}
        #     ))
        #     if len(status_codes) == 0:
        #         # Normal exit
        #         sys.exit(0)
        #     elif len(status_codes) == 1:
        #         # Exit code set by FO
        #         sys.exit(status_codes[0])
        #     else:
        #         raise ValueError

@dataclass
class NadirModuleSpecification:
    """
    Nadir processes can be combined together to create modules.
    These modules usually share fate, although a correct specification
    will not need such guarantees at all.

    A module will have its own dedicated global value provider that is
    not necessarily hosted on the Nadir database. It can be local DB 
    for example. This can be _very_ useful when some module level 
    variables are being frequently mutated such that having to go through
    the main Nadir DB would be too slow.

    Attributes
    ----------
    mv_aggregate: NadirModelValueAggregate
        The Model Value aggregator. This _SHOULD_ be complete, otherwise
        an error will happen at some point most likely.
    module_id: NadirModelValue
        A Model Value that specifies this module. We usually refer to
        this Model Value as the `mid`. A process within this module would
        be referred to by the pair `(mid, pid)`, and each thread with
        the triplet `(mid, pid, tid)`.
    module_name: str
        The name of this module.
    threads: Dict[str, Tuple[Type, List[NadirModelValue]]]
        The complete description of threads in this module. This
        dictionary describes a mapping from a string that is the
        name of the process that the thread belongs to, to a tuple
        of class and list.
        The class _MUST_ be a subclass of `NadirProcess`, usaully
        the auto-generated code from Nadir, and the list will be the
        thread identifiers (`tid`s) of all threads that operate under
        that process.
    local_vars: Dict[str, Optional[Dict[str, Any]]]
        Description of all local variables under this module. Note that
        this does _NOT_ expose these variables to other processes within
        this module, this is just for housekeeping.
    initial_labels: Dict[str, str]
        Initial lable of each process under this module.
    input_provider: Optional[AbstractProvider] = None
        The module level input provider. All processes under this module
        will use this provider as the input provider.
    global_provider: Optional[AbstractProvider] = None
        The module level global value provider. All processes under this 
        module will use this provider as the global value provider.
    with_fo: Optional[bool] = None
        Whether or not to connect this module to an FO instance.
    """
    mv_aggregate: NadirModelValueAggregate
    module_id: NadirModelValue
    module_name: str
    threads: Dict[str, Tuple[Type, List[NadirModelValue]]]
    local_vars: Dict[str, Optional[Dict[str, Any]]]
    initial_labels: Dict[str, str]
    input_provider: Optional[AbstractProvider] = None
    global_provider: Optional[AbstractProvider] = None
    with_fo: Optional[bool] = None


class NadirModule:
    def __init__(self,
        mv_aggregate: NadirModelValueAggregate, name: str, module_id: NadirModelValue,
        pids: List[NadirPID], threads: List[NadirProcess],
        input_provider: AbstractProvider, global_provider: AbstractProvider) -> None:

        self.is_active = True
        self.quit_event = threading.Event()

        self.mv_aggregate = mv_aggregate
        self.name = name
        self.module_id = module_id
        self.pids = pids
        self.threads = threads
        self.input_provider = input_provider
        self.global_provider = global_provider
        self.thread_set_exit_code: Dict[NadirPID, Optional[int]] = {pid: None for pid in self.pids}

        # Register each of your threads under the global provider you were given
        for thread in self.threads:
            thread.set_input_provider(self.input_provider)
            thread.set_global_provider(self.global_provider)

    def start(self):
        for thread in self.threads:
            thread.start()

    def start_and_wait(self):
        self.start()

        while self.is_active and NadirGlobalParams.is_active:
            self.quit_event.wait(WAIT_TIMEOUT)

        # for thread in self.threads:
        #     thread.graceful_exit()

    @staticmethod
    def spawn(
        specification: NadirModuleSpecification,
        module_provider_initializer: Callable,
        module_provider_initializer_args: Optional[Dict[str, Any]] = None,
        op_patches: Optional[List[Tuple[str, Callable]]] = None,
        macro_patches: Optional[List[Tuple[str, Callable]]] = None,
        initializers: Optional[List[Tuple[Callable, Dict[str, Any]]]] = None,
        finalizers: Optional[List[Tuple[Callable, Dict[str, Any]]]] = None,
        cleaners: Optional[List[Tuple[Callable, Dict[str, Any]]]] = None
    ):
        """
        This method is meant to be called with the multiprocessing
        framework. It will spawn a Nadir Module that has multiple
        NadirProcess instances under it.
        This helps give a hierarchy to global variables, and is the
        recommended way to use Nadir.

        Parameters
        ----------
        specification: NadirModuleSpecification
            A module specification instance.
        module_provider_initializer: Callable
            A callable that makes the global provider and sets up any module-level 
            global variables.
        module_provider_initializer_args: kwargs
            kwargs to give to `module_provider_initializer`.
        op_patches: List[Tuple[str, Callable]]
            List of operator patches, applied to the whole module.
        macro_patches: List[Tuple[str, Callable]]
            List of macro patches, applied to the whole module.
        initializers: List[Tuple[Callable, Dict[str, Any]]]
            List of initializer functions with their arguments to call one after 
            the others, _before_ thread sets are created.
        finalizers: List[Tuple[Callable, Dict[str, Any]]]
            List of finalizer functions with their arguments to call one after 
            the other _after_ thread sets are created.
        cleaners: List[Tuple[Callable, Dict[str, Any]]]
            List of cleanup functions that are to be called when the process exits
            or in the event of any uncaught exceptions.
            These functions must be equipped to handle that.
        """
        # First, set the name of the module
        setproctitle.setproctitle(specification.module_name)

        actual_pid = multiprocessing.current_process().pid

        # Frist, initialize the module-level provider
        if module_provider_initializer_args is None:
            module_provider_initializer_args = dict()
        module_provider_initializer(
            specification,
            **module_provider_initializer_args
        )

        assert specification.global_provider is not None
        assert specification.input_provider is not None

        # Now, call the initializers
        if initializers is not None:
            for item in initializers:
                func, args = item
                func(provider=specification.input_provider, **args)

        # Patch operators and macros
        patch_macros_and_operators_for_structured_nadir_code(op_patches, macro_patches)

        # Create process objects
        thread_sets = list()
        for thread_set_name, thread_set in specification.threads.items():
            TitledLog.info("nadir", f"Creating process object for thread set {thread_set_name}")
            cls, mvs = thread_set

            assert issubclass(cls, NadirProcess)

            pids = [NadirPID(specification.module_id, thread_id) for thread_id in mvs]
            init_args = {
                'mv_aggregate': specification.mv_aggregate,
                'name': thread_set_name,
                'thread_names': pids,
                'local_vars': specification.local_vars[thread_set_name],
                'initial_label': specification.initial_labels[thread_set_name],
                'with_fo': specification.with_fo
            }
            thread_sets.append(cls(**init_args))

        # Call the finalizers, passing the processes as first argument
        if finalizers is not None:
            for item in finalizers:
                for thread_set in thread_sets:
                    func, args = item
                    func(thread_set, **args)

        # Now, create the module instance
        pids = []
        for _, thread_ids in specification.threads.values():
            pids += [NadirPID(specification.module_id, thread_id) for thread_id in thread_ids]
        
        try:
            module = NadirModule(
                mv_aggregate=specification.mv_aggregate,
                name=specification.module_name,
                module_id=specification.module_id,
                pids=pids,
                threads=thread_sets,
                input_provider=specification.input_provider,
                global_provider=specification.global_provider
            )

            # Set module for all the thread sets created
            for thread_set in thread_sets:
                thread_set.set_module(thread_set)

            TitledLog.info("nadir", f"Spawning module {specification.module_name} with PID {actual_pid}")
            thread_set_names = [thread_set.name for thread_set in thread_sets]
            TitledLog.info("nadir", f"Processes under this module include: {', '.join(thread_set_names)}")
            # TODO: Maybe makes this a property?
            TitledLog.info("nadir", f"Module-level global values: {', '.join(specification.global_provider._module_level_values)}")
            module.start_and_wait()
        finally:
            if cleaners is not None:
                for item in cleaners:
                    func, args = item
                    func(**args)


def patch_macros_and_operators_for_structured_nadir_code(
        op_patches: Optional[List[Tuple[str, Callable]]] = None,
        macro_patches: Optional[List[Tuple[str, Callable]]] = None
    ):
    """
    Patch all macros and operators given in the input list.
    This assumes that the code being patched obeys the structure
    that is expected from it, meaning that operators are found
    under `atomics.operators` and macros under `atomics.macros`.
    """
    # Import atomics
    atomics = importlib.import_module('atomics')

    # Patch macros and operators
    if op_patches is not None:
        for op_name, op in op_patches:
            patch_operator(atomics, op_name, op)
    if macro_patches is not None:
        for macro_name, macro in macro_patches:
            patch_macro(atomics, macro_name, macro)

def patch_macro(atomics, macro_name: str, patch: Callable):
    setattr(atomics.macros, macro_name, patch)

def patch_operator(atomics, op_name: str, patch: Callable):
    setattr(atomics.operators, op_name, patch)
