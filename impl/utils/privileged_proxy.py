import os
import re
import sys
import grpc
import select
import signal
import socket
import argparse
import threading
import subprocess
import setproctitle
from typing import List, Tuple, Optional, Dict, Set
from concurrent.futures import ThreadPoolExecutor
from pynadir.utils.logging import TitledLog
from utils.convergence_verifier import ConvergenceVerifier
import openflow.ryulib.openflow_parser as openflow_parser
import openflow.ryulib.openflow_v13_parser as openflow_v13_parser
from openflow.ryulib.openflow_v13_defs import OFPT_FEATURES_REPLY, OFP_HEADER_SIZE
import utils.protos.proxy_pb2 as rpc_messages
from utils.protos.proxy_pb2_grpc import PrivilegedProxyServiceServicer, add_PrivilegedProxyServiceServicer_to_server
from google.protobuf.empty_pb2 import Empty


# Where we listen for switches and pretend to be the controller
DEFAULT_BIND_ADDRESS = ('127.0.0.1', 8080)

# Where the actual main controller is
DEFAULT_TARGET_ADDRESS = ('127.0.0.2', 6653)

DEFAULT_MAX_BACKLOG = 5
TCP_RECV_BUFFER_SIZE = 4096
DEFAULT_ECHO_INTERVAL = 3
DEFAULT_POLL_TIMEOUT = 3

IS_ROOT = False

OpenFlowHeader = Tuple[int, int, int, int]


def only_root(f):
    def wrapper(*args, **kwargs):
        if not IS_ROOT:
            TitledLog.fail("proxy", "I am not root! I cannot interact with OVS!")
        else:
            return f(*args, **kwargs)
    return wrapper

class ActiveConnection:
    def __init__(self, switch_socket: socket.socket, controller_socket: socket.socket):
        self.switch_socket = switch_socket
        self.controller_socket = controller_socket
        
        self._poll = select.epoll()
        self._poll.register(self.switch_socket, select.POLLIN | select.POLLPRI | select.POLLNVAL)
        self._poll.register(self.controller_socket, select.POLLIN | select.POLLPRI | select.POLLNVAL)

        self._dp_id: Optional[int] = None
        self._switch_to_controller_running_buffer: bytes = b''
        self._local_xid = 1
    
    @property
    def dp_id(self) -> Optional[int]:
        return self._dp_id
    
    @property
    def switch_address(self) -> Tuple[str, int]:
        return self.switch_socket.getsockname()
    @property
    def controller_address(self) -> Tuple[str, int]:
        return self.controller_socket.getsockname()
    
    @staticmethod
    def _send_on_socket(s: socket.socket, buf: bytes) -> Optional[int]:
        try:
            return s.send(buf)
        except IOError:
            pass

    def send_to_switch(self, buf: bytes) -> Optional[int]:
        return ActiveConnection._send_on_socket(self.switch_socket, buf)
    def send_to_controller(self, buf: bytes) -> Optional[int]:
        return ActiveConnection._send_on_socket(self.controller_socket, buf)

    @staticmethod
    def _receive_from_socket(s: socket.socket, buffer_size: int = TCP_RECV_BUFFER_SIZE) -> bytes:
        buf = b''
        while True:
            try:
                chunk = s.recv(buffer_size)
            except IOError:
                return b''
            buf += chunk
            if len(chunk) < buffer_size:
                break
        return buf

    def receive_from_switch(self) -> bytes:
        return self._receive_from_socket(self.switch_socket)    
    def receive_from_controller(self) -> bytes:
        return self._receive_from_socket(self.controller_socket)

    @staticmethod
    def parse_for_openflow_packet(buffer: bytes) -> Optional[Tuple[OpenFlowHeader, bytes, bytes]]:
        if len(buffer) < OFP_HEADER_SIZE:
            return None

        (version, msg_type, msg_len, xid) = openflow_parser.unpack_header(buffer)
        if len(buffer) >= msg_len:
            return (version, msg_type, msg_len, xid), buffer[:msg_len], buffer[msg_len:]
        else:
            return None
    
    def poll(self, timeout: Optional[float] = DEFAULT_POLL_TIMEOUT) -> List[Tuple[bool, int]]:
        return [(fd == self.controller_socket.fileno(), ev) for fd, ev in self._poll.poll(timeout)]

    @staticmethod
    def _relay(from_socket: socket.socket, to_socket: socket.socket) -> Optional[int]:
        try:
            buf = ActiveConnection._receive_from_socket(from_socket)
            if len(buf) > 0:
                return to_socket.send(buf)
        except IOError:
            return None
    
    def relay_from_controller_to_switch(self) -> Optional[int]:
        return self._relay(self.controller_socket, self.switch_socket)
    def relay_from_switch_to_controller(self) -> Optional[int]:
        if len(self._switch_to_controller_running_buffer) > 0:
            self.send_to_controller(self._switch_to_controller_running_buffer)
            self._switch_to_controller_running_buffer = b''
        return self._relay(self.switch_socket, self.controller_socket)

    def relay(self) -> bool:
        # Return `True` when a timeout happens, indicating the relay is not yet finished ...
        for from_controller, ev in self.poll():
            if ev & select.POLLNVAL:
                return False
            result = \
                self.relay_from_controller_to_switch() if from_controller \
                else self.relay_from_switch_to_controller()
            if result is None:
                return False
        return True

    def _sniff_for_dp_id(self) -> Optional[int]:
        res = self._receive_from_socket(self.switch_socket)
        if res is None or len(res) == 0:
            return None
        
        self._switch_to_controller_running_buffer += res
        item = ActiveConnection.parse_for_openflow_packet(self._switch_to_controller_running_buffer)
        if item is None:
            return 0
        
        header, packet, rem = item
        _, msg_type, _, _ = header
        if msg_type == OFPT_FEATURES_REPLY:
            version, msg_type, msg_len, xid = header
            msg = openflow_parser.msg(None, version, msg_type, msg_len, xid, packet)
            self._dp_id = msg.datapath_id
        
        self._switch_to_controller_running_buffer = rem
        return self.send_to_controller(packet)
    
    def sniff_for_dp_id(self) -> Optional[int]:
        for from_controller, ev in self.poll():
            if ev & select.POLLNVAL:
                return None
            if from_controller:
                return self.relay_from_controller_to_switch()
            else:
                return self._sniff_for_dp_id()
    
    def send_echo_request(self) -> Optional[int]:
        echo_req = openflow_v13_parser.OFPEchoRequest(None)
        echo_req.set_xid(self._local_xid)
        echo_req.serialize()
        self._local_xid += 1
        sent = self.send_to_switch(echo_req.buf)
        return sent

    def _make_controller_give_up(self, give_up_event: Optional[threading.Event]):
        # Receive everything from the controller without answering, until you get a FIN
        # Then close the target socket
        while True:
            if len(self._receive_from_socket(self.controller_socket)) == 0:
                try:
                    self.controller_socket.close()
                finally:
                    if give_up_event:
                        give_up_event.set()
                    break
    
    def make_controller_give_up(self, give_up_event: Optional[threading.Event]):
        t = threading.Thread(target=self._make_controller_give_up, daemon=True, args=(give_up_event,))
        t.start()

    def close(self):
        try:
            self.switch_socket.close()
        finally:
            pass
        try:
            self.controller_socket.close()
        finally:
            pass


class TCPProxy:
    def __init__(self, listen_address = DEFAULT_BIND_ADDRESS, 
                 target_address = DEFAULT_TARGET_ADDRESS,
                 max_backlog = DEFAULT_MAX_BACKLOG):
        self.listen_address = listen_address
        self.target_address = target_address
        self.max_backlog = max_backlog

        # This socket will listen for incoming switch connections
        self.listen_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.listen_socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.listen_socket.bind(self.listen_address)
        self.listen_socket.listen(self.max_backlog)

        self.is_active = True
        self.quit_event = threading.Event()

        self._active_connections: Dict[int, ActiveConnection] = dict()
        """Map DP ID to a pair of to_switch, to_controller sockets"""
        self.blocked: Dict[int, bool] = dict()
        """Map DP ID to True/False based on whether we blocked the switch"""
        self.handlers: List[threading.Thread] = []
        """All client threads"""
        self.unblock_event: Dict[int, threading.Event] = {}
        """Map DP ID to a threading event that is set when a switch is unblocked"""

        self.block_finished_event: Dict[int, threading.Event] = {}
        self.unblock_finished_event: Dict[int, threading.Event] = {}
        """
        Map DP ID to a threading event that is signaled when a block/unblock is _finished_
        with the following definitions:
        - A switch block is fininshed when the controller terminates the specific switch
          connection.
        - A switch unblock is finished when the new TCP connection for the switch is established.
        """

        self.reconnecting_switches: Set[int] = set()
        """Set of DP IDs for switches that we are waiting to reconnect"""

        self.cmd_thread: Optional[threading.Thread] = None
        self.server_thread: Optional[threading.Thread] = None

        """List of bridges that this proxy instance created ..."""
        self.ovs_bridges: List[str] = list()

        self.verifier: Optional[ConvergenceVerifier] = None
    
    def stop(self):
        self.is_active = False
        self.quit_event.set()
    
    def int_handler(self, *args):
        self.stop()
    
    def attach_signal_handler(self):
        for sig in ('TERM', 'HUP', 'INT'):
            signal.signal(getattr(signal, 'SIG' + sig), self.int_handler)

    def get_active_connection(self, dp_id: int) -> ActiveConnection:
        return self._active_connections[dp_id]

    def set_active_connection(self, dp_id: int, connection: ActiveConnection):
        self._active_connections[dp_id] = connection

    def pop_active_connection(self, dp_id: int, safe=False):
        if not safe:
            self._active_connections.pop(dp_id)
        else:
            self._active_connections.pop(dp_id, None)

    def is_dp_id_in_topology(self, dp_id: int) -> bool:
        return dp_id in self._active_connections

    def is_dp_blocked(self, dp_id: int) -> bool:
        if self.is_dp_id_in_topology(dp_id):
            return self.blocked[dp_id]
        return False

    def set_blocked(self, dp_id: int, blocked: bool):
        self.blocked[dp_id] = blocked

    def pop_blocked(self, dp_id: int):
        self.blocked.pop(dp_id)

    @staticmethod
    def _receive_from_socket(s: socket.socket) -> bytes:
        buf = b''
        while True:
            try:
                chunk = s.recv(TCP_RECV_BUFFER_SIZE)
            except ConnectionResetError:
                return b''
            buf += chunk
            if len(chunk) < TCP_RECV_BUFFER_SIZE:
                break
        return buf

    @staticmethod
    def _parse_for_packet(buffer: bytes) -> Optional[Tuple[OpenFlowHeader, bytes, bytes]]:
        if len(buffer) < OFP_HEADER_SIZE:
            return None

        # Parse header and see what type of packet we have
        (version, msg_type, msg_len, xid) = openflow_parser.unpack_header(buffer)
        if len(buffer) >= msg_len:
            # We have the whole packet, cut it out from buffer
            return (version, msg_type, msg_len, xid), buffer[:msg_len], buffer[msg_len:]
        else:
            # We don't have the whole packet, keep receiving
            return None

    @classmethod
    def safe_send(cls, send_socket, buf):
        try:
            send_socket.sendall(buf)
        except IOError:
            return -1
    
    def create_active_connection(self, client_socket: socket.socket, 
                                 client_address: Tuple[str, int]) -> Optional[ActiveConnection]:
        try:
            target_socket = socket.socket(socket.AF_INET, socket.SOL_SOCKET)
            target_socket.connect(self.target_address)
        except ConnectionRefusedError:
            client_socket.close()
            return None

        connection = ActiveConnection(client_socket, target_socket)
        TitledLog.info("proxy", f"Established new connection {client_address} --- {self.target_address}")
        return connection

    def record_dp_id(self, connection: ActiveConnection) -> int:
        assert connection.dp_id is not None

        self.set_active_connection(connection.dp_id, connection)
        self.set_blocked(connection.dp_id, False)
        self.unblock_event[connection.dp_id] = threading.Event()

        return connection.dp_id
    
    def signal_reconnect(self, dp_id: int):
        if dp_id in self.reconnecting_switches:
            self.reconnecting_switches.remove(dp_id)
            event = self.unblock_finished_event.get(dp_id)
            if event is not None:
                event.set()

    def handle_new_connection(self, switch_socket: socket.socket, switch_address: Tuple[str, int]):
        # Create a connection object
        connection = self.create_active_connection(switch_socket, switch_address)
        if not connection:
            return
        
        def _handle():
            # We have a connection, sniff for DP ID
            while self.is_active:
                if connection.sniff_for_dp_id() is None:
                    return
                if connection.dp_id is not None:
                    break
            if not self.is_active:
                return

            # If we are here, we have the DP ID
            dp_id = self.record_dp_id(connection)
            self.signal_reconnect(dp_id)
            while self.is_active:
                if self.is_dp_blocked(dp_id):
                    # Blocked!
                    TitledLog.warning("proxy", f"Connection from {switch_address} has been blocked ...")
                    connection.make_controller_give_up(self.block_finished_event.get(dp_id))

                    while self.is_active:
                        # Here, just exchange keep alives with the switch to keep it occupied
                        # NOTE: I don't expect echo timeouts here!!
                        if connection.send_echo_request() is None:
                            return
                        
                        # Now wait for either the connection/proxy to close or next echo
                        self.unblock_event[dp_id].wait(DEFAULT_ECHO_INTERVAL)
                        if not self.is_active or not self.is_dp_blocked(dp_id):
                            # Unblocked!
                            return
                else:
                    # Not blocked, continue as usual
                    if not connection.relay():
                        return
        
        try:
            _handle()
        except IOError:
            pass
        finally:
            self.cleanup_connection(connection)

    def cleanup_connection(self, connection: ActiveConnection):
        connection.close()
        dp_id = connection.dp_id
        if dp_id is not None:
            self.pop_active_connection(dp_id)
            self.pop_blocked(dp_id)
            self.unblock_event.pop(dp_id, None)
        
    def serve(self):
        listen_socket = self.listen_socket

        while self.is_active:
            (client_socket, client_address) = listen_socket.accept()
            if not self.is_active:
                break

            client_thread = threading.Thread(target=self.handle_new_connection, args=(client_socket, client_address))
            client_thread.start()
            
            self.handlers.append(client_thread)

        for client_thread in self.handlers:
            client_thread.join()
    
    @staticmethod
    def int_to_mac(macint) -> str:
        return ":".join(re.findall("..", f"{macint:012x}"))

    @staticmethod
    @only_root
    def wipeout_datapath_tcam(dp_id):
        os.system(f'sudo ovs-ofctl -O OpenFlow13 del-flows s{dp_id}')
    
    @staticmethod
    @only_root
    def pop_cookie_from_tcam(dp_id, cookie):
        os.system(f'sudo ovs-ofctl -O OpenFlow13 del-flows s{dp_id} table=0,cookie={cookie}/4294967295')
    
    @staticmethod
    @only_root
    def query_datapath_tcam(dp_id) -> Optional[List[int]]:
        cookies = []
        output = subprocess.check_output(
            f'sudo ovs-ofctl -O OpenFlow13 dump-flows s{dp_id}'.split(),
            text=True).strip()
        flows = [line.strip() for line in output.split('\n')[1:]]
        for flow in flows:
            for field in flow.split(", "):
                k, v = field.split("=")
                if k == 'cookie':
                    cookies.append(int(v, 16))
                    break
        return cookies
    
    @staticmethod
    @only_root
    def is_datapath_on_this_machine(dp_id) -> Optional[bool]:
        return os.system(f"sudo ovs-vsctl br-exists s{dp_id}") == 0

    @staticmethod
    @only_root
    def list_all_bridge_dp_ids() -> Optional[List[int]]:
        bridge_names = subprocess.check_output(
            "sudo ovs-vsctl list-br".split(), text=True
        ).strip().split()
        return [int(name.replace("s", "")) for name in bridge_names]
    
    @staticmethod
    @only_root
    def query_all() -> Optional[Dict[int, List[int]]]:
        return {
            dp_id: TCPProxy.query_datapath_tcam(dp_id) 
                for dp_id in TCPProxy.list_all_bridge_dp_ids()
        }
    
    @only_root
    def create_datapath(self, dp_id: int):
        assert dp_id > 0
        assert not self.is_datapath_on_this_machine(dp_id)
        # Create a new bridge
        os.system(f"sudo ovs-vsctl add-br s{dp_id}")
        # Set the protocol to OpenFlow13 and the MAC/DP_ID
        mac = self.int_to_mac(dp_id)
        os.system(f"sudo ovs-vsctl set bridge s{dp_id} protocols=OpenFlow13 other_config:hwaddr={mac} other_config:dp_id={dp_id}")
        # Now connect it to the controller
        ip, port = self.listen_address
        addr = f"tcp:{ip}:{port}"
        os.system(f"sudo ovs-vsctl set-controller s{dp_id} {addr}")
        self.ovs_bridges.append(f's{dp_id}')
    
    @only_root
    def delete_all_datapaths(self):
        os.system("mn -c")
        self.ovs_bridges.clear()

    @only_root
    def verify(self):
        tcam = {dp_id: set(ls) for dp_id, ls in self.query_all().items()}
        down_set = set(dp_id for dp_id, blocked in self.blocked.items() if blocked)
        if self.verifier is None:
            self.verifier = ConvergenceVerifier()
            self.verifier.initiate()
        self.verifier.verify_and_report(tcam, down_set)
    
    def wait_for_exit(self):
        while self.is_active:
            self.quit_event.wait(10)

    def cleanup(self):
        try:
            s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            s.connect(self.listen_address)
            s.close()
        finally:
            if self.server_thread is not None:
                self.server_thread.join()
            if self.listen_socket is not None:
                self.listen_socket.close()

    def run(self):
        if self.server_thread is not None:
            return

        self.server_thread = threading.Thread(target=self.serve)
        self.server_thread.start()


class ProxyCMD:
    HELP_FORMAT = "{:<20} {:<80}"
    
    def __init__(self, proxy: TCPProxy):
        self._proxy = proxy
    
    @property
    def proxy(self) -> TCPProxy:
        return self._proxy

    def int_handler(self, *args):
        raise EOFError
    
    def attach_signal_handler(self):
        for sig in ('TERM', 'HUP', 'INT'):
            signal.signal(getattr(signal, 'SIG' + sig), self.int_handler)

    def _do_exit(self):
        self.proxy.stop()
        sys.exit(0)

    def _do_list(self):
        for dp_id in self.proxy._active_connections:
            if not self.proxy.is_dp_blocked(dp_id):
                connection = self.proxy.get_active_connection(dp_id)
                print(f"\tDP ID {dp_id}: S -- {connection.switch_address} -- {connection.controller_address} -- C")
            else:
                print(f"\tDP ID {dp_id}: ---------------------- BLOCKED ----------------------")

    def _do_block(self, cmd: str, set_event: bool = True) -> Optional[int]:
        cmd_split = cmd.split()
        if len(cmd_split) != 2 or (cmd_split[0] != "block" and cmd_split[0] != "wait-block"):
            print("Usage: block <dp_id>")
            return

        try:
            dp_id = int(cmd_split[1])
        except ValueError:
            print(f"{cmd_split[1]} is not a valid DP ID")
            return

        if not self.proxy.is_dp_id_in_topology(dp_id):
            print(f"DP ID {dp_id} is not in the topology")
            return

        if self.proxy.is_dp_blocked(dp_id):
            print(f"DP ID {dp_id} is already blocked")
            return
        
        if set_event:
            self.proxy.set_blocked(dp_id, True)
        return dp_id

    def _do_unblock(self, cmd: str, set_event: bool = True) -> Optional[int]:
        cmd_split = cmd.split()
        if len(cmd_split) != 2 or (cmd_split[0] != "unblock" and cmd_split[0] != "wait-unblock"):
            print("Usage: unblock <dp_id>")
            return

        try:
            dp_id = int(cmd_split[1])
        except ValueError:
            print(f"{cmd_split[1]} is not a valid DP ID")
            return

        if not self.proxy.is_dp_id_in_topology(dp_id):
            print(f"DP ID {dp_id} is not in the topology")
            return

        if not self.proxy.is_dp_blocked(dp_id):
            print(f"DP ID {dp_id} is not blocked")
            return

        self.proxy.reconnecting_switches.add(dp_id)
        if set_event:
            self.proxy.set_blocked(dp_id, False)
            self.proxy.unblock_event[dp_id].set()
        return dp_id

    def _do_block_and_wait(self, cmd: str):
        dp_id = self._do_block(cmd, set_event=False)
        if dp_id is not None:
            self.proxy.block_finished_event[dp_id] = threading.Event()
            self.proxy.set_blocked(dp_id, True)
            while self.proxy.is_active:
                if self.proxy.block_finished_event[dp_id].wait(DEFAULT_ECHO_INTERVAL):
                    break

    def _do_unblock_and_wait(self, cmd: str):
        """
        We MUST prevent the unblock event from being set _before_ we create the
        finishing event. If we don't, then it is possible that the switch is
        unblocked first, immediately reconnects and goes through before we setup
        the finishing event.
        """
        dp_id = self._do_unblock(cmd, set_event=False)
        if dp_id is not None:
            self.proxy.unblock_finished_event[dp_id] = threading.Event()
            self.proxy.set_blocked(dp_id, False)
            self.proxy.unblock_event[dp_id].set()
            while self.proxy.is_active:
                if self.proxy.unblock_finished_event[dp_id].wait(DEFAULT_ECHO_INTERVAL):
                    break

    def _do_wipe(self, cmd: str):
        cmd_split = cmd.split()
        if len(cmd_split) != 2 or cmd_split[0] != "wipe":
            print("Usage: wipe <dp_id>")
            return

        try:
            dp_id = int(cmd_split[1])
        except ValueError:
            print(f"{cmd_split[1]} is not a valid DP ID")
            return

        if not self.proxy.is_datapath_on_this_machine(dp_id):
            print(f"No OVS bridge with DP ID {dp_id} found on this machine")
            return

        self.proxy.wipeout_datapath_tcam(dp_id)

    def _do_pop(self, cmd: str):
        cmd_split = cmd.split()
        if len(cmd_split) != 3 or cmd_split[0] != "pop":
            print("Usage: pop <dp_id> <cookie>")
            return

        try:
            dp_id = int(cmd_split[1])
        except ValueError:
            print(f"{cmd_split[1]} is not a valid DP ID")
            return

        try:
            cookie = int(cmd_split[2])
        except ValueError:
            print(f"{cmd_split[2]} is not a cookie number")
            return

        res = self.proxy.is_datapath_on_this_machine(dp_id)
        if res is not None:
            if not res:
                print(f"No OVS bridge with DP ID {dp_id} found on this machine")
                return
            self.proxy.pop_cookie_from_tcam(dp_id, cookie)
    
    def _do_query(self, cmd: str):
        cmd_split = cmd.strip().split()
        if len(cmd_split) == 1:
            self._do_query_all()
        elif len(cmd_split) == 2:
            try:
                dp_id = int(cmd_split[1])
                self._do_query_one(dp_id)
            except ValueError:
                print(f'{dp_id} is not a valid DP ID')
    
    def _do_query_all(self):
        cookie_dict = self.proxy.query_all()
        if cookie_dict is not None:
            line_format = "{:<4} : {:<80}"
            for dp_id, cookie_list in cookie_dict.items():
                print(line_format.format(dp_id, ", ".join(map(lambda item: str(item), sorted(cookie_list)))))
    
    def _do_query_one(self, dp_id: int):
        res = self.proxy.is_datapath_on_this_machine(dp_id)
        if res is not None:
            if not res:
                print(f"No OVS bridge with DP ID {dp_id} found on this machine")
                return
        cookie_list = self.proxy.query_datapath_tcam(dp_id)
        if cookie_list is None:
            print(f"No OVS bridge with DP ID {dp_id} found on this machine")
        print(", ".join(map(lambda item: str(item), sorted(cookie_list))))
    
    def _do_verify(self):
        self.proxy.verify()

    def _do_makemany(self, cmd: str):
        cmd_split = cmd.strip().split()
        if len(cmd_split) != 2 or cmd_split[0] != "makemany":
            print("Usage: makemany <num>")
            return
        
        try:
            num = int(cmd_split[1])
            for dp_id in range(1, num+1):
                res = self.proxy.is_datapath_on_this_machine(dp_id)
                if res is not None:
                    if res:
                        print(f"An OVS bridge with DP ID {dp_id} already exists on this machine!")
                        return
                    self.proxy.create_datapath(dp_id)
        except ValueError:
            print(f'{cmd_split[1]} is not a valid number')

    def _do_make(self, cmd: str):
        cmd_split = cmd.strip().split()
        if len(cmd_split) != 2 or cmd_split[0] != "make":
            print("Usage: make <dp_id>")
            return
        
        try:
            dp_id = int(cmd_split[1])
            res = self.proxy.is_datapath_on_this_machine(dp_id)
            if res is not None:
                if res:
                    print(f"An OVS bridge with DP ID {dp_id} already exists on this machine!")
                    return
                self.proxy.create_datapath(dp_id)
        except ValueError:
            print(f'{dp_id} is not a valid DP ID')
    
    def _do_deleteall(self):
        self.proxy.delete_all_datapaths()

    def cmd(self):
        while self.proxy.is_active:
            try:
                cmd = input("tcpproxy>> ").strip()
            except EOFError:
                self._do_exit()

            if cmd == 'exit':
                self._do_exit()
            elif cmd == 'list':
                self._do_list()
            elif cmd.startswith("block"):
                self._do_block(cmd)
            elif cmd.startswith("unblock"):
                self._do_unblock(cmd)
            elif cmd.startswith("wait-block"):
                self._do_block_and_wait(cmd)
            elif cmd.startswith("wait-unblock"):
                self._do_unblock_and_wait(cmd)
            elif cmd.startswith("wipe"):
                self._do_wipe(cmd)
            elif cmd.startswith("pop"):
                self._do_pop(cmd)
            elif cmd.startswith("query"):
                self._do_query(cmd)
            elif cmd.startswith("verify"):
                self._do_verify()
            elif cmd.startswith("deleteall"):
                self._do_deleteall()
            elif cmd.startswith("makemany"):
                self._do_makemany(cmd)
            elif cmd.startswith("make"):
                self._do_make(cmd)
            elif len(cmd) == 0:
                continue
            else:
                print("Usage:")
                print(self.HELP_FORMAT.format("exit", "Quit"))
                print(self.HELP_FORMAT.format("list", "List all connections"))
                print(self.HELP_FORMAT.format("block <dp_id>", "Block connection with DP ID <dp_id>"))
                print(self.HELP_FORMAT.format("unblock <dp_id>", "Unblock connection with DP ID <dp_id>"))
                print(self.HELP_FORMAT.format("wait-block <dp_id>", "Blocking version of `block`"))
                print(self.HELP_FORMAT.format("wait-unblock <dp_id>", "Blocking version of `unblock`"))
                print(self.HELP_FORMAT.format("wipe <dp_id>", "(Only Root) Clear the flow table of DP with ID <dp_id>"))
                print(self.HELP_FORMAT.format("pop <dp_id> <cookie>", "(Only Root) Remove IR with cookie <cookie> from the table on DP with ID <dp_id>"))
                print(self.HELP_FORMAT.format("query ?<dp_id>", "(Only Root) Query all IR cookies installed for all or one DP"))
                print(self.HELP_FORMAT.format("verify", "Verify that we converged to the correct DAG"))
                print(self.HELP_FORMAT.format("make <dp_id>", "Create a dapath with a given DP ID"))
                print(self.HELP_FORMAT.format("makemany <num>", "Make <num> datapaths with DP IDs 1 to num"))
                print(self.HELP_FORMAT.format("deleteall", "Remove all OVS datapaths on this machine"))

    def cleanup(self):
        self.proxy.stop()
        self.proxy.cleanup()
        if len(self.proxy.ovs_bridges):
            self._do_deleteall()

    def run(self):
        if IS_ROOT:
            print("Running with root privileges. Datapath operations are available.")
        else:
            print("Running without root privileges. Datapath operations are not available.")
        try:
            self.cmd()
        except Exception as e:
            if isinstance(e, EOFError):
                pass
            else:
                TitledLog.fail("proxy", f"Exception while executing the command line handler: {e}")
        finally:
            self.cleanup()


class ProxyRPC:
    IP = socket.gethostbyname(socket.gethostname())
    PORT = 10000

    def __init__(self, proxy: TCPProxy):
        self._proxy = proxy
        self._server = grpc.server(thread_pool=ThreadPoolExecutor(max_workers=1))
        self._listener = ProxyRPCStub(self)
        add_PrivilegedProxyServiceServicer_to_server(self._listener, self._server)
        self._server.add_insecure_port(":".join([self.IP, str(self.PORT)]))

    def int_handler(self, *args):
        self._server.stop(grace=1.0)
        self._proxy.stop()
        self._proxy.cleanup()
        if len(self._proxy.ovs_bridges):
            self._proxy.delete_all_datapaths()
    
    def attach_signal_handler(self):
        for sig in ('TERM', 'HUP', 'INT'):
            signal.signal(getattr(signal, 'SIG' + sig), self.int_handler)
    
    def start(self):
        self._server.start()
    
    def wait(self):
        self._server.wait_for_termination()
    
    def run(self):
        self.start()
        self.wait()


class ProxyRPCStub(PrivilegedProxyServiceServicer):
    def __init__(self, proxy: TCPProxy):
        super().__init__()
        self.proxy = proxy
    
    def MakeDatapath(self, request: rpc_messages.DPIDMessage, context):
        self.proxy.create_datapath(request.dp_id)
        return Empty()
    
    def AsyncBlockDatapath(self, request: rpc_messages.DPIDMessage, context):
        self.proxy.set_blocked(request.dp_id, True)
        return Empty()
    
    def AsyncUnblockDatapath(self, request: rpc_messages.DPIDMessage, context):
        self.proxy.reconnecting_switches.add(request.dp_id)
        self.proxy.set_blocked(request.dp_id, False)
        self.proxy.unblock_event[request.dp_id].set()
        return Empty()
    
    def AsyncWipeoutDatapath(self, request: rpc_messages.DPIDMessage, context):
        self.proxy.wipeout_datapath_tcam(request.dp_id)
        return Empty()
    
    def SyncBlockDatapath(self, request: rpc_messages.DPIDMessage, context):
        self.proxy.block_finished_event[request.dp_id] = threading.Event()
        self.proxy.set_blocked(request.dp_id, True)
        while self.proxy.is_active:
            if self.proxy.block_finished_event[request.dp_id].wait(DEFAULT_ECHO_INTERVAL):
                break
        return Empty()

    def SyncUnblockDatapath(self, request: rpc_messages.DPIDMessage, context):
        self.proxy.reconnecting_switches.add(request.dp_id)
        self.proxy.unblock_finished_event[request.dp_id] = threading.Event()
        self.proxy.set_blocked(request.dp_id, False)
        self.proxy.unblock_event[request.dp_id].set()
        while self.proxy.is_active:
            if self.proxy.unblock_finished_event[request.dp_id].wait(DEFAULT_ECHO_INTERVAL):
                break
        return Empty()

    def SyncWipeoutDatapath(self, request: rpc_messages.DPIDMessage, context):
        raise NotImplementedError
    
    def QueryDatapath(self, request: rpc_messages.DPIDMessage, context) -> rpc_messages.QueryDatapathResponse:
        res = self.proxy.is_datapath_on_this_machine(request.dp_id)
        assert res is True
        cookie_list = self.proxy.query_datapath_tcam(request.dp_id)
        assert cookie_list is not None
        return rpc_messages.QueryDatapathResponse(cookies=cookie_list)
    
    def QueryAll(self, request, context) -> rpc_messages.QueryAllResponse:
        cookie_dict = self.proxy.query_all()
        assert cookie_dict is not None
        return rpc_messages.QueryAllResponse({k: rpc_messages.QueryDatapathResponse(v) for k, v in cookie_dict.items()})


if __name__ == '__main__':
    setproctitle.setproctitle("priv-prox")

    parser = argparse.ArgumentParser(
        description="A TCP proxy. When run as root, it can also manipulate OpenFlow switches")
    
    IS_ROOT = (os.geteuid() == 0)

    parser.add_argument('-li', dest='listen_ip', default=DEFAULT_BIND_ADDRESS[0],
                        help="IP on which to listen for switch connections")
    parser.add_argument('-lp', dest='listen_port', default=DEFAULT_BIND_ADDRESS[1], type=int,
                        help="Port on which to listen for switch connections")
    parser.add_argument('-ti', dest='target_ip', default=DEFAULT_TARGET_ADDRESS[0],
                        help="MASTER controller IP address")
    parser.add_argument('-tp', dest='target_port', default=DEFAULT_TARGET_ADDRESS[1], type=int,
                        help="MASTER controller port")
    
    parser.add_argument('--with', choices=['cli', 'rpc'], dest='up_with',
                        help="Attach either a CLI or a gRPC server to this instance (NOT BOTH!)")

    args=parser.parse_args()
    
    proxy = TCPProxy(
        listen_address=(args.listen_ip, args.listen_port), 
        target_address=(args.target_ip, args.target_port),
    )
    proxy.run()

    if args.up_with == 'cli':
        cmd = ProxyCMD(proxy)
        cmd.attach_signal_handler()
        cmd.run()
    elif args.up_with == 'rpc':
        rpc = ProxyRPC(proxy)
        rpc.attach_signal_handler()
        rpc.run()
    else:
        proxy.attach_signal_handler()
        proxy.wait_for_exit()
        proxy.cleanup()
