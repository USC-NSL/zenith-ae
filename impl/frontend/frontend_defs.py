import enum
import time
import struct
import threading
from typing import Tuple, Dict
from pynadir.params import NadirGlobalParams


MAXIMUM_QUEUED_SEND_MESSAGES = 1024
MAXIMUM_QUEUED_OPENFLOW_EVENTS = 1024
MAXIMUM_QUEUED_SWITCH_EVENTS = 128

MAXIMUM_QUEUED_MS_EVENTS = 128
MAXIMUM_QUEUED_EH_EVENTS = 64

MAXIMUM_QUEUED_SWITCH_STAT_REPLIES = 64

ABSENT_SWITCH_WAIT_TIME = 3

OFC_MONITORING_SERVER_IP = '127.0.0.2'

DEFAULT_SOCKET_TIMEOUT = 1
MAXIMUM_QUEUED_DATAPATH_SEND_MESSAGES = 64

ECHO_REQUEST_INTERVAL = 3
MAXIMUM_UNREPLIED_ECHO_REQUESTS = 1


"""
(Specific to Nadir)
For Nadir, IR UID is handled by the framework, so we do not need to
track the UID ourselves.
In the specification, each IR has a `flow` field, which is just an integer
that gets incremented for each flow. This can be mapped directly to the 
cookie field, and its main function would be to track the ID.

Install/Delete IRs that mirror each other must have the same ID. As
such, all we need for this is a much simpler message type:

- The Datapath ID for where the IR should go                         ( 8 bytes)
- The cookie of the IR (or zero if N/A)                              ( 8 bytes)
- Flags (used only to set barrier)                                   ( 1 byte )
- The IR in bytes                                                    (variable)

So the message format from worker pool to frontend would be:

    +-----------------+------------------+----------------+
    | DP ID (8 bytes) | Cookie (8 bytes) | Flags (1 byte) |
    +-----------------+------------------+----------------+
    |                                                     |
    .                      FlowMod                        .
    .                                                     .
    +-----------------------------------------------------+

Similarly, we also do something similar for reconciliation messages,
except the cookie field is kept empty.
"""

NADIR_WORKER_POOL_MESSAGE_FORMAT_STR = "!QQB"
NADIR_WORKER_POOL_MESSAGE_HEADER_LENGTH = 17

assert struct.calcsize(NADIR_WORKER_POOL_MESSAGE_FORMAT_STR) == NADIR_WORKER_POOL_MESSAGE_HEADER_LENGTH

NADIR_RECONCILIATION_MESSAGE_FORMAT_STR = "!QB"
NADIR_RECONCILIATION_MESSAGE_HEADER_LENGTH = 9

assert struct.calcsize(NADIR_RECONCILIATION_MESSAGE_FORMAT_STR) == NADIR_RECONCILIATION_MESSAGE_HEADER_LENGTH


class NADIR_WORKER_POOL_MESSAGE_FLAGS:
    BARRIERED = 0x1
    DELETE = 0x2
    FLOW_STAT_REQ = 0x4


def make_worker_pool_message(dp_id: int, flags: int, packet: bytes, cookie: int) -> bytes:
    header_bytes = bytearray(NADIR_WORKER_POOL_MESSAGE_HEADER_LENGTH)
    struct.pack_into(NADIR_WORKER_POOL_MESSAGE_FORMAT_STR, header_bytes, 0, dp_id, cookie, flags)
    return header_bytes + packet

def unpack_worker_pool_message(packet: bytes) -> Tuple[int, int, int, bytes]:
    if len(packet) < NADIR_WORKER_POOL_MESSAGE_HEADER_LENGTH:
        raise ValueError
    (dp_id, cookie, flags) = struct.unpack_from(NADIR_WORKER_POOL_MESSAGE_FORMAT_STR, packet, 0)
    return dp_id, cookie, flags, packet[NADIR_WORKER_POOL_MESSAGE_HEADER_LENGTH:]


class CountdownLatch:
    def __init__(self, until: int) -> None:
        self.count = until
        self.cv = threading.Condition()
    
    def down(self):
        with self.cv:
            if not self.count:
                return
            
            self.count -= 1
            if not self.count:
                self.cv.notify_all()
    
    def break_lock(self):
        if NadirGlobalParams.is_active:
            NadirGlobalParams.stop()
        with self.cv:
            self.cv.notify_all()
    
    def wait(self, timeout=None):
        with self.cv:
            while NadirGlobalParams.is_active:
                if not self.count:
                    return
                self.cv.wait(timeout)


class NadirDatapath:
    def __init__(self, dp_id: int) -> None:
        self.dp_id = dp_id
    
    def as_dict(self):
        return {
            "dp_id": self.dp_id
        }

    @classmethod
    def from_dict(cls, _dict: Dict):
        return cls(dp_id=_dict["dp_id"])


class OFC_EVENT_TYPES(enum.Enum):
    TCP_TIMEOUT = 0                 # TCP timeout on the socket connected to the datapath
    ECHO_TIMEOUT = 1                # Datapath failed to respond to too many echo requests
    DATAPATH_JOINED = 2             # A new datapath has joined the network
    DATAPATH_RETURNED = 3           # A disconnected datapath recovered
    DATAPATH_POLITE_LEAVE = 4       # A datapath has removed all flows and requested a clean disconnect.
                                    # Usually, this means that they are not coming back!
    UNKNOWN = 5                     # Some weird IO error killed the connection

    def __str__(self):
        return self.name

    def __eq__(self, other):
        if isinstance(other, int):
            return self.value == other
        elif isinstance(other, str):
            return self.name == other
        return id(self) == id(other)

    def __hash__(self):
        return hash(self.value)


class SwitchStatusChangeEvent:
    def __init__(self, dp_id, reason):
        self.dp_id = dp_id
        self.reason = reason
        self.timestamp = int(time.time())

    def __str__(self):
        return f"{self.dp_id}: {self.reason.name}"


class SWITCH_TO_CONTROLLER_TYPES(enum.Enum):
    INSTALLED_SUCCESSFULLY = 0
    DELETED_SUCCESSFULLY = 1
    CLEARED_TCAM_SUCCESSFULLY = 2
    FLOW_STAT_REPLY = 3
    GROUP_STAT_REPLY = 4
    ROLE_REPLY = 5
    STALE_ROLE_REQUEST = 6

    def __str__(self):
        return self.name

    def __eq__(self, other):
        if isinstance(other, int):
            return self.value == other
        elif isinstance(other, str):
            return self.name == other
        return id(self) == id(other)

    def __hash__(self):
        return hash(self.value)


class MSEvent:
    def __init__(self, type, dp_id, msg):
        self.type = type
        self.dp_id = dp_id
        self.msg = msg
        self.timestamp = int(time.time())
