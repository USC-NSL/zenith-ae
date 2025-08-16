import sys
import time
import queue
import random
import signal
import socket
import argparse
import selectors
from threading import Event, Thread
from atomics.common import *
from utils.convergence_verifier import ConvergenceVerifier
from utils.input_setup import get_input_provider, make_input_provider, ZenithProvider
from pynadir.zenith_providers.queue_provider import RabbitProvider
from pynadir.exceptions import RepeatLabel
from pynadir.utils.logging import TitledLog


MODEL_VALUES.add_mv("FAKE_SW")
MODEL_VALUES.add_mv("FAKE_GET")
MODEL_VALUES.add_mv("FAKE_SEND")


LISTEN_ADDRESS = ("127.0.0.1", 11000)


class FakeSwitch:
    """
    This is a utility that lets one test ZENITH without having to use
    OpenFlow. It imlpements both a frontend and simulates a simple switch.
    It also allows one to interact with the switch, and manipulate the TCAM
    to see how/if ZENITH handles it.

    To use this utility, the following Model Values must be available 
    globally in the ZENITH instance:

    - `FAKE_SW`: Module identifier of fake switch
    - `FAKE_GET`: Thread identifier of switch operation queue consumer
    - `FAKE_SEND`: Thread identifier of switch ACK queue producer
    
    Together, these define 2 threads within this switch that handle operations.

    The fake switch also knows the complete ground truth of dataplane at any 
    moment. Since DAGs are constant, it can safely and accurately decide upon
    dataplane convergence and report it.
    True convergence would thus mean: (1) This module report that we have
    converged to the correct DAG (2) The controller has stopped working on
    said DAG and is now idle.

    In case convergence is not yet achieved, the module can:

    - Report _missing_ IRs: IRs that are supposed to be installed in a switch
    but cannot be found.
    - Report _offending_ IRs: IRs that should have been removed from the switches
    upon DAG switch but are still there.
    """

    PID_GET = NadirPID(MODEL_VALUES.FAKE_SW, MODEL_VALUES.FAKE_GET)
    PID_SEND = NadirPID(MODEL_VALUES.FAKE_SW, MODEL_VALUES.FAKE_SEND)

    def __init__(self, num_switches: int, provider: Optional[ZenithProvider] = None):
        self.is_active = True
        self.quit_event = Event()

        self.is_tracking = False
        self.num_switches = num_switches
        self.tcam = {i: set() for i in range(1, num_switches+1)}
        self.is_up = {i: True for i in range(1, num_switches+1)}
        self.rabbit = RabbitProvider()
        self.rabbit.register_pid(self.PID_GET)
        self.rabbit.register_pid(self.PID_SEND)
        self.rabbit.add_value(name="controller2Switch", value=[], interacting_pids=[self.PID_GET])
        self.rabbit.add_value(name="switch2Controller", value=[], interacting_pids=[self.PID_SEND])
        self.receiver_thread = None
        self.sender_thread = None
        self.command_thread = None
        self.flapper_thread = None
        self.messages_to_send = queue.Queue()

        TitledLog.set_log_level(2)

        if provider is not None:
            self.input_provider = provider
            # We _ASSUME_ the relevant collections are already being tracked
            self.is_tracking = True
        else:
            make_input_provider()
            self.input_provider = get_input_provider()
        
        self.verifier = ConvergenceVerifier(self.input_provider)

        self.socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.socket.bind(LISTEN_ADDRESS)
        self.socket.listen(1)
    
    @property
    def down_set(self) -> Set[int]:
        return set([dp_id for dp_id, up in self.is_up.items() if not up])
    
    def attach_signal_handlers(self):
        for sig in ('TERM', 'HUP', 'INT'):
            signal.signal(getattr(signal, 'SIG' + sig), self.int_handler)

    def int_handler(self, _, _frame=None):
        self.is_active = False
        self.quit_event.set()
        try:
            self.socket.shutdown(socket.SHUT_RDWR)
        except:
            pass

    def serve_zenith_requests(self):
        try:
            flapper_socket, flapper_addr = self.socket.accept()
        except OSError:
            TitledLog.warning("fake-sw", "Aborted")
            self.socket.close()
            return

        TitledLog.success("fake-sw", f"Flapper connected at {flapper_addr}")

        try:
            while self.is_active:
                msg: str = flapper_socket.recv(2048).decode()
                if msg is None or len(msg) == 0:
                    break

                if msg.startswith("FLAPPER_VERIFY"):
                    dag_number = int(msg.split("FLAPPER_VERIFY ")[-1])
                    TitledLog.special_info("fake-sw", f"Flapper says it finished {dag_number}")
                    self.verify_flapper(dag_number)
                elif msg.startswith("TOPO_VERIFY"):
                    TitledLog.special_info("fake-sw", "ZENITH thinks the topology has converged")
                    self.verify()
                else:
                    raise ValueError
        finally:
            self.socket.close()

    def reconcile_all(self):
        stats = {i: self.tcam[i] for i, up in self.is_up.items() if up}
        self.rabbit.fifo_put(self.PID_SEND, "reconciliationQueue", stats)
        self.rabbit.commit(self.PID_SEND)

    def reconcile(self, dp_id: int):
        if self.is_up[dp_id]:
            stats = {dp_id: self.tcam[dp_id]}
            self.rabbit.fifo_put(self.PID_SEND, "reconciliationQueue", stats)
            self.rabbit.commit(self.PID_SEND)

    # def verify_flapper(self, dag_number: int):
    #     converged = True
    #     self._set_ir_to_dp_mapping()
    #     if self.flapper_map is None:
    #         # Get the dags ...
    #         dag_docs = list(self.input_provider.nib_read_only_provider.query_document(
    #             'dags', filter={}
    #         ))
    #         self.flapper_map = dict()
    #         for i, dag_doc in enumerate(dag_docs):
    #             nodes = frozenset(int.from_bytes(oid.binary, 'big') for oid in dag_doc['nodes'])
    #             edges = frozenset((
    #                                   int.from_bytes(edge[0].binary, 'big'),
    #                                   int.from_bytes(edge[1].binary, 'big')
    #                               ) for edge in dag_doc['edges'])
    #             trigger_set = frozenset(dag_doc['trigger_set'])
    #             assert len(trigger_set) == 0
    #             self.flapper_map[i + 1] = (nodes, edges)

    #     nodes, _ = self.flapper_map[dag_number]

    #     # All IRs for the current DAG, should be in the associated switch
    #     for ir in nodes:
    #         dp_id = self.ir_to_dp_mapping[ir]
    #         if ir not in self.tcam[dp_id]:
    #             TitledLog.warning("fake-sw", f"IR {ir} should be in the TCAM of {dp_id}, but is not!", both=True)
    #             converged = False

    #     # No switch associated with this DAG should contain an IR that does NOT belong to this DAG
    #     for dp_id, tcam in self.tcam.items():
    #         offending_irs = tcam.difference(nodes)
    #         if len(offending_irs) > 0:
    #             TitledLog.warning("fake-sw", f"DP {dp_id} has the following offending IRs in the TCAM: {offending_irs}", both=True)
    #             converged = False

    #     if converged:
    #         TitledLog.success("fake-sw", "The network converged to the correct DAG!", both=True)

    def short_id(self, uid: NadirUID) -> str:
        uid_str = hex(self.input_provider.uid_as_int(uid))
        return uid_str.replace('0x', '  ').replace('x', ' ')[-3:]

    def serve(self):
        while self.is_active:
            try:
                msg = self.rabbit.fifo_get(self.PID_GET, "controller2Switch")
                self.rabbit.commit(self.PID_GET)
            except RepeatLabel:
                if not self.is_active:
                    break
                self.rabbit.send_keepalive(self.PID_GET)
                continue
            destination = msg['$destination']
            of_cmd = msg['$message']
            assert isinstance(of_cmd, MessageOpenFlowCMD)
            assert destination == of_cmd.to

            if not self.is_tracking:
                # Wait until we know a controller exists before we track datapaths!
                self.input_provider.track_collection("datapaths")
                self.input_provider.track_collection("dags")
                self.input_provider.track_collection("irs")
                self.verifier.initiate()
                self.is_tracking = True

            dp_id = self.input_provider.get_int_from_uid(destination)
            if not self.is_up[dp_id]:
                continue

            if of_cmd.type == EnumOpenFlowCMD.INSTALL_FLOW:
                flow = self.input_provider.uid_as_int(of_cmd.flow)
                self.tcam[dp_id].add(flow)
                TitledLog.debug("fake-sw", f"Installed flow {self.short_id(of_cmd.flow)} on {dp_id}: TCAM = {self.tcam[dp_id]}")
                self.messages_to_send.put(MessageOpenFlowACK(
                    to=MODEL_VALUES.ofc0, type=EnumOpenFlowACK.INSTALLED_SUCCESSFULLY,
                    source=destination, flow=of_cmd.flow
                ))
            elif of_cmd.type == EnumOpenFlowCMD.DELETE_FLOW:
                target = self.tcam[dp_id]
                ir = self.input_provider.uid_as_int(of_cmd.flow)
                if ir in target:
                    target.remove(ir)
                TitledLog.debug("fake-sw", f"Removed flow {self.short_id(of_cmd.flow)} on {dp_id}: TCAM = {self.tcam[dp_id]}")
                self.messages_to_send.put(MessageOpenFlowACK(
                    to=MODEL_VALUES.ofc0, type=EnumOpenFlowACK.DELETED_SUCCESSFULLY,
                    source=destination, flow=of_cmd.flow
                ))
            elif of_cmd.type == EnumOpenFlowCMD.CLEAR_TCAM:
                self.tcam[dp_id].clear()
                TitledLog.debug("fake-sw", f"Cleared TCAM on {dp_id}")
                self.messages_to_send.put(MessageSwitchKeepalive(
                    swID=self.input_provider.int_as_uid('datapaths', dp_id),
                    num=(time.time_ns() // 1000), type=MODEL_VALUES.CLEARED_TCAM_SUCCESSFULLY,
                    installerStatus=EnumInstallerStatus.INSTALLER_UP
                ))
            # elif of_cmd.type == EnumOpenFlowCMD.FLOW_STAT_REQUEST:
            #     if not self.is_tracking:
            #         # Wait until we know a controller exists before we track datapaths!
            #         self.input_provider.track_collection("datapaths")
            #         self.input_provider.track_collection("dags")
            #         self.input_provider.track_collection("irs")
            #         self.is_tracking = True
            #     current_tcam = set([
            #         self.input_provider.int_as_uid('irs', num) for num in self.tcam[dp_id].copy()
            #     ])
            #     self.messages_to_send.put(MessageReconciliationResponse(
            #         to=MODEL_VALUES.ofc0, type=EnumReconciliationResponse.ENTRY_FOUND,
            #         source=destination, flows=current_tcam
            #     ))
            else:
                raise ValueError(f"Unexpected type {of_cmd.type}")

    def change_state(self, dp_id: int):
        if self.is_up[dp_id]:
            num_installed_irs = len(self.tcam[dp_id])
            if num_installed_irs > 0:
                num_irs_to_keep = int(random.random() * num_installed_irs)
                self.tcam[dp_id] = set(random.sample(list(self.tcam[dp_id]), num_irs_to_keep))
                TitledLog.info("fake-sw", f"Going DOWN for {dp_id} [Loss: {round((1 - (num_irs_to_keep/num_installed_irs))*100, 2)}%]", both=True)
            else:
                TitledLog.info("fake-sw", f"Going DOWN for {dp_id}", both=True)
            self.is_up[dp_id] = False
            self.messages_to_send.put(MessageSwitchTimeout(
                swID=self.input_provider.int_as_uid('datapaths', dp_id),
                type=MODEL_VALUES.NIC_ASIC_DOWN, num=(time.time_ns() // 1000)
            ))
        else:
            TitledLog.info("fake-sw", f"Going UP for {dp_id}", both=True)
            # TODO: Fix this!!!
            self.tcam[dp_id].clear()
            self.is_up[dp_id] = True
            self.messages_to_send.put(MessageSwitchKeepalive(
                swID=self.input_provider.int_as_uid('datapaths', dp_id),
                num=(time.time_ns() // 1000), type=MODEL_VALUES.KEEP_ALIVE,
                installerStatus=EnumInstallerStatus.INSTALLER_UP
            ))

    def send_messages(self):
        while self.is_active:
            try:
                msg = self.messages_to_send.get(timeout=2)
            except queue.Empty:
                msg = None

            if not self.is_active:
                break
            else:
                if msg is None:
                    self.rabbit.send_keepalive(self.PID_SEND)
                    continue
                # if isinstance(msg, (MessageOpenFlowACK, MessageReconciliationResponse)):
                #     self.rabbit.fifo_put(self.PID_SEND, "switch2Controller", msg)
                # else:
                #     self.rabbit.fifo_put(self.PID_SEND, "swSeqChangedStatus", msg)
                self.rabbit.fifo_put(self.PID_SEND, "switch2Controller", msg)
                self.rabbit.commit(self.PID_SEND)

    def show_tcam(self, dp_id: int) -> str:
        tcam = self.tcam[dp_id]
        return f'[ {", ".join(str(uid) for uid in tcam)} ]'

    def get_cmd(self):
        sel = selectors.DefaultSelector()
        sel.register(sys.stdin, selectors.EVENT_READ)
        prompted = False
        while self.is_active:
            if not prompted:
                print(">> ", end="")
                prompted = True
            sys.stdout.flush()
            event = sel.select(timeout=2.0)
            if event is None:
                continue
            cmd: str = sys.stdin.readline().strip()
            prompted = False
            if not self.is_tracking:
                # Wait until we know a controller exists before we track datapaths!
                self.input_provider.track_collection("datapaths")
                self.input_provider.track_collection("dags")
                self.input_provider.track_collection("irs")
                self.is_tracking = True
            if len(cmd) == 0:
                continue
            elif cmd.startswith('down '):
                dp_id = int(cmd.split('down ', maxsplit=1)[-1])
                if dp_id not in self.is_up:
                    print(f"DP {dp_id} does not exist")
                    continue
                if not self.is_tracking:
                    print("No controller is up yet! Wait until we get at least a single message.")
                    continue
                if self.is_up[dp_id]:
                    self.change_state(dp_id)
                else:
                    print(f"DP {dp_id} is already down")
            elif cmd.startswith('up '):
                dp_id = int(cmd.split('up ', maxsplit=1)[-1])
                if dp_id not in self.is_up:
                    print(f"DP {dp_id} does not exist")
                    continue
                if not self.is_tracking:
                    print("No controller is up yet! Wait until we get at least a single message.")
                    continue
                if not self.is_up[dp_id]:
                    self.change_state(dp_id)
                else:
                    print(f"DP {dp_id} is already up")
            elif cmd == "exit":
                self.is_active = False
                self.quit_event.set()
                break
            elif cmd == "show":
                for dp_id in self.tcam.keys():
                    if self.is_up[dp_id]:
                        print(f"\t{dp_id}: {self.show_tcam(dp_id)}")
                    else:
                        print(f"\t{dp_id}: < DOWN >")
            elif cmd == "verify":
                self.verifier.verify_and_report(self.tcam, self.down_set)
            elif cmd.startswith("pop "):
                dp_id, ir = tuple(int(arg.strip()) for arg in cmd.split("pop ")[-1].split())
                if dp_id not in self.tcam:
                    print(f"DP {dp_id} does not exist")
                    continue
                if ir not in self.tcam[dp_id]:
                    print(f"IR {ir} no in the TCAM of {dp_id}")
                    continue
                self.tcam[dp_id].remove(ir)
                print(f"Removed IR {ir} from TCAM of {dp_id}")
            elif cmd == "help":
                print(
                    "List of commands:"
                    "`down <dpid>`       : Disconnect a datapath from the frontend\n"
                    "`up <dpid>`         : Reconnect a datapath to the frontend\n"
                    "`show`              : Show the state of the TCAM on all switches\n"
                    "`verify`            : Verify that the current TCAM matches with the active DAG\n"
                    "`pop <dpid> <irid>` : Remove an IR with ID `irid` from the TCAM on datapath `dpid`"
                )
            else:
                continue

    def run(self):
        self.sender_thread = Thread(target=self.send_messages)
        self.receiver_thread = Thread(target=self.serve)
        self.command_thread = Thread(target=self.get_cmd)
        self.flapper_thread = Thread(target=self.serve_zenith_requests)

        self.sender_thread.start()
        self.receiver_thread.start()
        self.command_thread.start()
        self.flapper_thread.start()

        while self.is_active:
            self.quit_event.wait(2.0)

        self.is_active = False
        self.quit_event.set()

        try:
            self.socket.shutdown(socket.SHUT_RDWR)
        except:
            pass

        self.flapper_thread.join()
        self.command_thread.join()
        self.receiver_thread.join()
        self.sender_thread.join()


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Utility for creating fake switches of arbitrary numbers')
    parser.add_argument('--num-switches', type=int, default=2, help='Number of switches')
    args = parser.parse_args()

    switch = FakeSwitch(args.num_switches)
    switch.attach_signal_handlers()
    switch.run()
