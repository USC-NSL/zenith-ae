import queue
import signal
import socket
import threading
import frontend.frontend_defs as frontend_defs
from bson import ObjectId
from pynadir.zenith_providers.queue_provider import RabbitProvider
from pynadir.exceptions import RepeatLabel, WaitThenRepeat, ExecutionHalted
from frontend.datapath import Datapath
from frontend.frontend_defs import (MSEvent, SWITCH_TO_CONTROLLER_TYPES, SwitchStatusChangeEvent,
                                    OFC_EVENT_TYPES, ABSENT_SWITCH_WAIT_TIME)
from frontend.openflow_event_handler import OpenFlowEventHandlers
from utils.input_setup import get_input_provider
from atomics.common import *

# We need some OpenFlow definitions as well
import openflow.ryulib.common_defs as common_defs
from nib.nib_direct import NIBDirect
from pynadir.utils.logging import TitledLog
from frontend.ir_command_parser import IRCommandParser, IR, IR_TYPE


MODEL_VALUES.add_mv("FRONTEND")
MODEL_VALUES.add_mv("FRONTEND_GET")
MODEL_VALUES.add_mv("FRONTEND_SEND")
MODEL_VALUES.add_mv("FRONTEND_STAT")


class OpenFlowFrontend:
    PID_GET = NadirPID(MODEL_VALUES.FRONTEND, MODEL_VALUES.FRONTEND_GET)
    PID_SEND = NadirPID(MODEL_VALUES.FRONTEND, MODEL_VALUES.FRONTEND_SEND)
    PID_STAT = NadirPID(MODEL_VALUES.FRONTEND, MODEL_VALUES.FRONTEND_STAT)

    def __init__(self, topo_size: int, max_num_irs: int) -> None:
        # TODO: Why is `MaxNumIRs` even required to be known here?
        self.is_active = True
        self.quit_event = threading.Event()
        self.max_num_irs = max_num_irs

        # Server for switches
        self.ofp_tcp_listen_port = common_defs.OFP_TCP_PORT
        self.switch_server = None

        # Queue of messages received from the OpenFlow event handler
        self.of_events_queue = queue.Queue(frontend_defs.MAXIMUM_QUEUED_OPENFLOW_EVENTS)

        # Queue of switch status events received from the OpenFlow event handler
        self.switch_events_queue = queue.Queue(frontend_defs.MAXIMUM_QUEUED_SWITCH_EVENTS)

        # Thread that consumes OF events and passes them to ms_publisher
        self.of_event_thread = None
        # Thread that consumes switch events and passes them to eh_publisher
        self.switch_event_thread = None

        """
        To prepare for topology set up, we pass the expected number of switches in
        the topology. The frontend will unblock, only when the appropriate number
        of switches have joined the network.
        """

        self.topology_size_latch = frontend_defs.CountdownLatch(topo_size)

        """Queues that go to our Nadir processes. Each one has its own thread/connection"""

        self.rabbit = RabbitProvider()
        self.rabbit.register_pid(self.PID_GET)
        self.rabbit.register_pid(self.PID_SEND)
        self.rabbit.add_value(name="controller2Switch", value=[], interacting_pids=[self.PID_GET])
        self.rabbit.add_value(name="switch2Controller", value=[], interacting_pids=[self.PID_SEND])
        self.rabbit.add_value(name="swSeqChangedStatus", value=[], interacting_pids=[self.PID_SEND])
        self.rabbit.add_value(name="reconciliationQueue", value=[], interacting_pids=[self.PID_STAT])

        # We'll have to register the joined datapaths
        self.nib_direct = NIBDirect()

        # Our handler threads
        self.openflow_event_handler_thread = None
        self.switch_server_thread = None
        self.zenith_handler_thread = None

        # Cache ALL the IRs for now
        self.ir_cache: Optional[Dict[int, Tuple[bytes, bytes]]] = None

        # This packet is shared among all datapaths
        self.flow_stat_req_packet = IRCommandParser.get_flow_stats()

        # We need this to get UIDs!
        # make_input_provider()
        self.input_provider = get_input_provider()
        # self.input_provider.track_collection("datapaths")
        # self.input_provider.track_collection("irs")

        self.connected_dps = set()
    
    def attach_signal_handlers(self):
        for sig in ('TERM', 'HUP', 'INT'):
            signal.signal(getattr(signal, 'SIG' + sig), self.int_handler)
    
    def int_handler(self, signo=None, _frame=None):
        TitledLog.warning("frontend", "Frontend was interrupted, will terminate soon.")
        if NadirGlobalParams.is_active:
            NadirGlobalParams.stop()
        self.is_active = False
        self.quit_event.set()
        self.topology_size_latch.break_lock()

    def _get_ir_packets(self, ir_doc: Dict) -> Tuple[bytes, bytes]:
        installer = IRCommandParser.parse(IR(
            command=ir_doc['command'],
            dp_id=ir_doc['dp_id'],
            type=IR_TYPE.INSTALL_FLOW,
            cookie=ir_doc['cookie']
        ))
        deleter = IRCommandParser.parse(IR(
            command=ir_doc['command'],
            dp_id=ir_doc['dp_id'],
            type=IR_TYPE.DELETE_FLOW,
            cookie=ir_doc['cookie']
        ))
        installer.serialize()
        deleter.serialize()

        return installer.buf, deleter.buf
    
    def _get_clear_tcam(self) -> bytes:
        deleter = IRCommandParser.get_clear_table(table_id=0)
        deleter.serialize()
        return deleter.buf

    def set_ir_cache(self):
        assert self.ir_cache is None
        ir_docs = self.nib_direct.query_document('irs', filter={})
        self.ir_cache = {
            ir_doc['cookie']: self._get_ir_packets(ir_doc)
            for ir_doc in ir_docs
        }
        TitledLog.info("frontend", f"Filled IR cache with {len(self.ir_cache)} cookies!")

    def add_switch_to_nib(self, dp_id: int) -> bool:
        dp_doc = {'dp_id': dp_id, '_id': ObjectId((dp_id).to_bytes(12, 'big'))}
        self.nib_direct.update_document("datapaths", dp_doc, update={
            '$set': dp_doc
        }, upsert=True)
        if dp_id not in self.connected_dps:
            self.connected_dps.add(dp_id)
            return True
        return False

    def _register_datapath(self, dp_id, datapath):
        Datapath.DP_DICT[dp_id] = datapath
        if self.add_switch_to_nib(dp_id):
            self.topology_size_latch.down()
        else:
            self.switch_events_queue.put(SwitchStatusChangeEvent(dp_id, OFC_EVENT_TYPES.DATAPATH_RETURNED))
    
    def of_event_loop(self):
        while self.is_active:
            msg = self.of_events_queue.get()

            if msg is None or not self.is_active:
                break

            assert isinstance(msg, MSEvent)

            source = self.input_provider.int_as_uid('datapaths', msg.dp_id)

            if msg.type == SWITCH_TO_CONTROLLER_TYPES.INSTALLED_SUCCESSFULLY:
                ack = MessageOpenFlowACK(
                    to=MODEL_VALUES.ofc0, type=EnumOpenFlowACK.INSTALLED_SUCCESSFULLY,
                    source=source, flow=self.input_provider.int_as_uid('irs', msg.msg['cookie'])
                )
                TitledLog.debug("frontend", f"DP {msg.dp_id} ACKED INSTALL {msg.msg['cookie']}")
            elif msg.type == SWITCH_TO_CONTROLLER_TYPES.DELETED_SUCCESSFULLY:
                ack = MessageOpenFlowACK(
                    to=MODEL_VALUES.ofc0, type=EnumOpenFlowACK.DELETED_SUCCESSFULLY,
                    source=source, flow=self.input_provider.int_as_uid('irs', msg.msg['cookie'])
                )
                TitledLog.debug("frontend", f"DP {msg.dp_id} ACKED DELETE {msg.msg['cookie']}")
            elif msg.type == SWITCH_TO_CONTROLLER_TYPES.CLEARED_TCAM_SUCCESSFULLY:
                ack = MessageSwitchKeepalive(
                    swID=source,
                    num=msg.msg['timestamp'],
                    type=MODEL_VALUES.CLEARED_TCAM_SUCCESSFULLY,
                    installerStatus=EnumInstallerStatus.INSTALLER_UP
                )
                TitledLog.debug("frontend", f"DP {msg.dp_id} ACKED CLEAR_TCAM")
            elif msg.type == SWITCH_TO_CONTROLLER_TYPES.FLOW_STAT_REPLY:
                ack = MessageReconciliationResponse(
                    to=MODEL_VALUES.ofc0, type=EnumReconciliationResponse.ENTRY_FOUND,
                    source=source, flows=msg.msg['cookies']
                )
                TitledLog.debug("frontend", f"DP {msg.dp_id} ACKED FLOW STAT")
            else:
                raise ValueError(f"Unknown message type: {msg}")

            self.rabbit.fifo_put(self.PID_SEND, "switch2Controller", ack)
            self.rabbit.commit(self.PID_SEND)
    
    def switch_event_loop(self):
        while self.is_active:
            status_change_event = self.switch_events_queue.get()

            if status_change_event is None or not self.is_active:
                break

            assert isinstance(status_change_event, SwitchStatusChangeEvent)

            swID = self.input_provider.int_as_uid('datapaths', status_change_event.dp_id)

            if status_change_event.reason in {OFC_EVENT_TYPES.TCP_TIMEOUT, OFC_EVENT_TYPES.ECHO_TIMEOUT}:
                event = MessageSwitchTimeout(
                    swID=swID,
                    type=MODEL_VALUES.NIC_ASIC_DOWN,
                    num=status_change_event.timestamp
                )
                TitledLog.warning("frontend", f"DP {status_change_event.dp_id} DOWN")
            elif status_change_event.reason in {OFC_EVENT_TYPES.DATAPATH_RETURNED}:
                event = MessageSwitchKeepalive(
                    swID=swID,
                    num=status_change_event.timestamp,
                    type=MODEL_VALUES.KEEP_ALIVE,
                    installerStatus=EnumInstallerStatus.INSTALLER_UP
                )
                TitledLog.info("frontend", f"DP {status_change_event.dp_id} UP")
            elif status_change_event.reason in {OFC_EVENT_TYPES.DATAPATH_POLITE_LEAVE}:
                TitledLog.special_info("frontend", f"DP {status_change_event.dp_id} LEFT THE TOPOLOGY")
                continue
            else:
                raise ValueError(f"Unexpected event message: {status_change_event}")

            self.rabbit.fifo_put(self.PID_SEND, "swSeqChangedStatus", event)
            self.rabbit.commit(self.PID_SEND)

    def zenith_event_loop(self):
        while self.is_active:
            try:
                msg = self.rabbit.fifo_get(self.PID_GET, "controller2Switch")
            except RepeatLabel:
                if not self.is_active:
                    break
                self.rabbit.send_keepalive(self.PID_GET)
                continue
            except ExecutionHalted:
                break

            destination = msg['$destination']
            of_cmd = msg['$message']
            assert isinstance(of_cmd, MessageOpenFlowCMD)
            assert destination == of_cmd.to

            dp_id = self.input_provider.get_int_from_uid(destination)
            dp: Datapath = Datapath.DP_DICT.get(dp_id)

            if not dp:
                # Never seen switch, ignore
                TitledLog.warning("frontend", f"The switch {dp_id} is garbage!")
                self.rabbit.commit(self.PID_GET)
                return
            if dp == -1:
                # Absent switch, wait
                raise WaitThenRepeat(ABSENT_SWITCH_WAIT_TIME)

            try:
                if of_cmd.type == EnumOpenFlowCMD.INSTALL_FLOW or of_cmd.type == EnumOpenFlowCMD.DELETE_FLOW:
                    cookie = self.input_provider.uid_as_int(of_cmd.flow)
                    packet_install, packet_delete = self.ir_cache[cookie]
                    if of_cmd.type == EnumOpenFlowCMD.INSTALL_FLOW:
                        TitledLog.debug("frontend", f"INSTALL ON {dp_id} | COOKIE = {cookie}")
                        dp.send_with_barrier(packet_install, cookie, delete=False)
                    else:
                        TitledLog.debug("frontend", f"DELETE ON {dp_id} | COOKIE = {cookie}")
                        dp.send_with_barrier(packet_delete, cookie, delete=True)
                elif of_cmd.type == EnumOpenFlowCMD.CLEAR_TCAM:
                    cookie = of_cmd.flow
                    assert cookie == 0
                    packet = self._get_clear_tcam()
                    TitledLog.debug("frontend", f"CLEAR TCAM ON {dp_id}")
                    dp.send_with_barrier(packet, cookie, delete=True)
                # elif of_cmd.type == EnumOpenFlowCMD.FLOW_STAT_REQUEST:
                #     packet = self.flow_stat_req_packet
                #     TitledLog.debug("frontend", f"FLOW STAT REQUEST FOR {dp_id}")
                #     dp.send(packet)
                else:
                    raise ValueError(f"Unexpected type {of_cmd.type}")
            except ConnectionError:
                TitledLog.warning("frontend", f"Could not send packet to dp_id {dp_id}")
            finally:
                self.rabbit.commit(self.PID_GET)

    def _init_classes(self):
        # When OF_EH sees a new datapath, it needs to call _register_datapath to update NIB
        OpenFlowEventHandlers.set_datapath_on_connection_method(self._register_datapath)

        # of_events_queue will collect OpenFlow ACKs for IRs
        OpenFlowEventHandlers.set_ms_queue(self.of_events_queue)

        # switch_events_queue will collect timeouts, joins and leave events
        OpenFlowEventHandlers.set_sw_change_queue(self.switch_events_queue)
        Datapath.set_switch_status_change_queue(self.switch_events_queue)
    
    def start(self):
        # Initiate classes
        self._init_classes()

        # Fill the cache
        self.set_ir_cache()

        # Setup OpenFlow event handler
        assert OpenFlowEventHandlers.handler_is_ready(), "OpenFlow Handler is not initialized!"
        self.openflow_event_handler_thread = threading.Thread(target=OpenFlowEventHandlers.generic_handler)

        # Now, setup switch server
        self.switch_server = StreamServer(
            (frontend_defs.OFC_MONITORING_SERVER_IP, self.ofp_tcp_listen_port),
            Datapath.create
        )
        self.switch_server_thread = threading.Thread(target=self.switch_server.serve_forever)

        self.openflow_event_handler_thread.start()
        self.switch_server_thread.start()

    def serve_zenith(self):
        # Start the loops
        self.of_event_thread = threading.Thread(target=self.of_event_loop)
        self.switch_event_thread = threading.Thread(target=self.switch_event_loop)
        self.zenith_handler_thread = threading.Thread(target=self.zenith_event_loop)

        self.of_event_thread.start()
        self.switch_event_thread.start()
        self.zenith_handler_thread.start()

    def wait_until_topology_is_ready(self):
        # Now, wait until the topology size is reached
        self.topology_size_latch.wait(5)
    
    def wait_for_exit(self):
        # Wait until the user tells you to exit
        while self.is_active and NadirGlobalParams.is_active:
            self.quit_event.wait(5)
        
        self.cleanup()

    def cleanup(self):
        OpenFlowEventHandlers.finish()
        Datapath.finish()

        self.switch_server.close()

        OpenFlowEventHandlers.put_event("aragif") # noqa

        # Wakeup anyone that might be sleeping
        self.of_events_queue.put(None)
        self.switch_events_queue.put(None)

        # Wait for a graceful exit
        for t in [
            self.of_event_thread,
            self.switch_event_thread,
            self.openflow_event_handler_thread,
            self.switch_server_thread,
            self.zenith_handler_thread
        ]:
            if t is not None:
                t.join()


class StreamServer:
    def __init__(self, listen_info, handle=None):
        self.listen_info = listen_info
        self.server = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.server.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.server.bind(listen_info)
        self.server.listen(1)
        self.handle = handle
        self.stop = False

    def serve_forever(self):
        with self.server:
            while not self.stop:
                sock, addr = self.server.accept()
                if self.stop:
                    break
                threading.Thread(target=self.handle, args=(sock, addr)).start()
    
    def close(self):
        if not self.stop:
            self.stop = True
            try:
                socket.create_connection(self.listen_info)
            finally:
                pass


if __name__ == '__main__':
    frontend = OpenFlowFrontend(10, 11)
    frontend.attach_signal_handlers()
    frontend.start()
    print("[ FRONTEND ] Waiting for topology to materialize ...")
    frontend.wait_until_topology_is_ready()
    if frontend.is_active:
        print("[ FRONTEND ] Topology size reached!")
        frontend.serve_zenith()
        frontend.wait_for_exit()
