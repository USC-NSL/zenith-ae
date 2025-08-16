import queue
import random
import socket
import contextlib
import openflow.ryulib.common_defs as of_common
import openflow.ryulib.openflow_parser as openflow_parser
import openflow.ryulib.openflow_v13_parser as openflow_v13_parser
from openflow.zenith_defs import OpenFlowEvent
from frontend.frontend_defs import *
from frontend.openflow_event_handler import OpenFlowEventHandlers
from socket import IPPROTO_TCP, TCP_NODELAY, SHUT_WR
from socket import timeout as socket_timeout


class Datapath:
    DP_DICT = {}

    switch_status_change_queue = None

    @classmethod
    def finish(cls):
        for dp in cls.DP_DICT.values():
            if isinstance(dp, Datapath):
                dp.is_active = False

    def __init__(self, socket: socket.socket, address, **kwargs):
        self.socket = socket
        self.socket.setsockopt(IPPROTO_TCP, TCP_NODELAY, 1)
        self.socket.settimeout(DEFAULT_SOCKET_TIMEOUT)
        self.address = address
        self.is_active = True
        
        if not kwargs:
            self.dp_id = None
            self.send_q = queue.Queue(MAXIMUM_QUEUED_DATAPATH_SEND_MESSAGES)
            self.xid = random.randint(0, of_common.MAX_XID)
        else:
            self.dp_id = kwargs['dp_id']
            self.send_q = kwargs['send_q']
            self.xid = kwargs['xid']


        self.unreplied_echo_requests = []
        self.max_unreplied_echo_requests = MAXIMUM_UNREPLIED_ECHO_REQUESTS
        self.echo_request_interval = ECHO_REQUEST_INTERVAL
        self.no_write = False

        self.barrier_map = {}
        self.flow_rem_map = {}

    def __str__(self):
        return f"Endpoint: {self.address} || Active: {self.is_active}\n" + \
               f"ID: {self.dp_id}"

    @classmethod
    def report(cls):
        print("\n")
        for dp in cls.DP_DICT.values():
            print(dp)
        print("\n")

    @classmethod
    def set_switch_status_change_queue(cls, queue):
        cls.switch_status_change_queue = queue

    def _put_sw_change_event(self, reason):
        Datapath.switch_status_change_queue.put(SwitchStatusChangeEvent(self.dp_id, reason))

    def _close_write(self):
        try:
            self.socket.shutdown(SHUT_WR)
            self.no_write = True
        except (EOFError, IOError):
            pass
        
    def close(self):
        self._close_write()

    def _recv_loop(self):
        buf = bytearray()
        empty = True
        min_read_len = remaining_read_len = of_common.OFP_HEADER_SIZE
        try:
            while self.is_active:
                try:
                    read_len = min_read_len
                    if remaining_read_len > min_read_len:
                        read_len = remaining_read_len
                    ret = self.socket.recv(read_len)
                except socket_timeout:
                    continue
                except (EOFError, IOError) as e:
                    if self.dp_id:
                        self._put_sw_change_event(OFC_EVENT_TYPES.UNKNOWN)
                    break

                if not ret:
                    if self.no_write:
                        break

                    if self.dp_id:
                        Datapath.DP_DICT.pop(self.dp_id)
                        self._put_sw_change_event(OFC_EVENT_TYPES.DATAPATH_POLITE_LEAVE)
                    break

                buf += ret
                buf_len = len(buf)
                while buf_len >= min_read_len:
                    (version, msg_type, msg_len, xid) = openflow_parser.unpack_header(buf)

                    if msg_type == 3 and empty:
                        break

                    if empty:
                        empty = False

                    if msg_len < min_read_len:
                        # Weird message! Just close the connection
                        break

                    if buf_len < msg_len:
                        remaining_read_len = (msg_len - buf_len)
                        break

                    msg = openflow_parser.msg(self, version, msg_type, msg_len, xid, buf[:msg_len])
                    # LOG.debug(f"{msg.__class__} on datapath {self.address}")
                    if msg:
                        # LOG.debug(f'Parsed message type {msg.__class__}')
                        event = OpenFlowEvent(self, msg)
                        if OpenFlowEventHandlers.datapath_on_connection_method is None:
                            raise ValueError("Class methods are uninitialized")
                        OpenFlowEventHandlers.put_event(event)

                    buf = buf[msg_len:]
                    buf_len = len(buf)
                    remaining_read_len = min_read_len
        finally:
            try:
                self.socket.close()
            except IOError:
                pass

    def _send_loop(self):
        try:
            while self.is_active:
                buf, close_socket = self.send_q.get()

                if buf is None:
                    break

                self.socket.sendall(buf)

                if close_socket:
                    break
        except socket_timeout:
            if self.dp_id:
                self._put_sw_change_event(OFC_EVENT_TYPES.TCP_TIMEOUT)
        except IOError:
            if self.dp_id:
                self._put_sw_change_event(OFC_EVENT_TYPES.UNKNOWN)
        finally:
            q = self.send_q
            self.send_q = None
            try:
                while q.get(block=False):
                    continue
            except queue.Empty:
                pass
            self._close_write()

    def send(self, buf, close_socket=False):
        msg_enqueued = False
        if self.send_q:
            self.send_q.put((buf, close_socket))
            msg_enqueued = True
        return msg_enqueued

    def send_with_barrier(self, buf, cookie, close_socket=False, delete=False):
        msg_enqueued = False
        
        if self.send_q:
            # Generate a barrier and send it to the switch to make sure everything
            # is done for the buffer content
            barrier_message = openflow_v13_parser.OFPBarrierRequest(self)
            self.set_xid(barrier_message)

            barrier_message.serialize()
            barrier_buf = buf + barrier_message.buf
            
            self.send_q.put((barrier_buf, close_socket))
            
            # update barrier_map
            if not delete:
                assert self.barrier_map.get(barrier_message.xid) is None, "XID problem!"
                self.barrier_map[barrier_message.xid] = cookie
            else:
                assert self.flow_rem_map.get(barrier_message.xid) is None, "XID problem!"
                self.flow_rem_map[barrier_message.xid] = cookie

            msg_enqueued = True
        
        return msg_enqueued

    def set_xid(self, msg):
        self.xid += 1
        self.xid &= of_common.MAX_XID
        msg.set_xid(self.xid)
        return self.xid

    def set_buf_xid(self, buf):
        self.xid += 1
        self.xid &= of_common.MAX_XID
        buf[6:10] = struct.pack('!I', self.xid)
        return self.xid

    def send_msg(self, msg, close_socket=False, barrier=False, cookie=None):
        if msg.xid is None:
            self.set_xid(msg)
        msg.serialize()
        if barrier:
            return self.send_with_barrier(msg.buf, cookie=cookie, close_socket=close_socket)
        return self.send(msg.buf, close_socket=close_socket)

    def _echo_request_loop(self):
        while (self.send_q and self.is_active and
               (len(self.unreplied_echo_requests) <= self.max_unreplied_echo_requests)):
            echo_req = openflow_v13_parser.OFPEchoRequest(self)
            self.unreplied_echo_requests.append(self.set_xid(echo_req))
            self.send_msg(echo_req)
            time.sleep(self.echo_request_interval)

        if not self.is_active:
            return

        if self.send_q and self.dp_id:
            self._put_sw_change_event(OFC_EVENT_TYPES.ECHO_TIMEOUT)

        self.close()

    def acknowledge_echo_reply(self, xid):
        try:
            self.unreplied_echo_requests.remove(xid)
        except ValueError:
            pass

    def serve(self):
        send_thr = threading.Thread(target=self._send_loop)
        send_thr.start()

        if self.no_write:
            self.no_write = False

        # send hello message immediately
        hello = openflow_parser.get_hello(self)
        self.send_msg(hello)

        echo_thr = threading.Thread(target=self._echo_request_loop)
        echo_thr.start()

        try:
            self._recv_loop()
        finally:
            # Synchronously tell the send threads to exit
            if self.send_q:
                self.send_q.put((None, True))
            self.is_active = False

            for t in [send_thr, echo_thr]:
                t.join()
            
            # print(f"Done serving {self.address}")

    @classmethod
    def create(cls, dp_socket, dp_address):
        # print(f"Connection from {address}")
        with contextlib.closing(cls(dp_socket, dp_address)) as datapath:
            try:
                datapath.serve()
            except Exception as e:
                raise e
