import enum
import struct
import time
from bson.objectid import ObjectId
from nib.nib_defs import CONTROLLER_MODULES, OFC_ROLE
from openflow.ryulib.openflow_v13_parser import OFPRoleRequest, MsgBase


class SWITCH_TO_CONTROLLER_TYPES:
    INSTALLED_SUCCESSFULLY = "INSTALLED_SUCCESSFULLY"
    DELETED_SUCCESSFULLY = "DELETED_SUCCESSFULLY"
    CLEARED_TCAM_SUCCESSFULLY = "CLEARED_TCAM_SUCCESSFULLY"
    FLOW_STAT_REPLY = "FLOW_STAT_REPLY"
    GROUP_STAT_REPLY = "GROUP_STAT_REPLY"
    ROLE_REPLY = "ROLE_REPLY"
    STALE_ROLE_REQUEST = "STALE_ROLE_REQUEST"


"""
The Worker Pool can send messages to Monitoring Server in a
burst, and as such, we need to put the length of the message
in the header so that MS can parse it correctly.

The data that we send is:
- The Datapath ID for where the IR should go                         ( 8 bytes)
- The length of the whole packet (header + FlowMod message in bytes) ( 4 bytes)
- The ID of the IR in the NIB so that MS can update its state        (12 bytes)
- The IR in bytes                                                    (variable)

The packet now is of the form:

    +-------------+-------------+
    |    DP ID    |    Length   |
    +-------------+-------------+
    |          IR UID           |
    +---------------------------+
    |                           |
    .          FlowMod          .
    .                           .
    +---------------------------+

Python does not have 12 byte fields for structs, so we don't include the
UID in the header (not that it matters anyway ...)

Update 1:
    To prevent sending barrier messages when none is needed,
    we add 1 byte to header for flagging messages that do not
    need barriers.
    If 0, no barrier is needed, if 1, send with barrier.

Update 2:
    Since we need to update the state of the flows that we remove,
    we need to also send the ID of the IR that we want to delete.
    We call this "Target UID".

    So now the packet looks like this:

    +-----------+----------- +---------------+
    | DP ID (8) | Length (4) | Barriered (1) |
    +------------------+-----+---------------+
    |   IR UID (12)    |   Target UID (12)   |
    +----------------------------------------+
    |                                        |
    .                FlowMod                 .
    .                                        .
    +----------------------------------------+
"""

# Length of IR UIDs
IR_UID_LENGTH = 12

# With barrier flag
RAW_IR_HEADER_FORMAT_STR = "!QIB"
RAW_IR_HEADER_LENGTH = 13


"""
The Monitoring Server can send messages to the Event Handler in much the
same was as the Worker Pool to Monitoring Server.

The data that we send is:
- The Datapath ID for the event                              ( 8 bytes)
- The event type, for now just 1 byte                        ( 1 byte )

The packet now is of the form:

    +-------------+----------+
    |    DP ID    |   Type   |
    +-------------+----------+

The (admittedly ill-named) OFC_EVENT_TYPES holds the possible values for
event types.

This is where we need to make a logical relation between the ones that we
can detect in the Monitoring Server, and the ones defined in the spec.
The thing is, unlike as in the spec, we can't hope that the switches are
courteous and actually tell us what module is failing. As the experts
say "It really isn't realistic to assume a software can detect what part
of it is failing, as if that _is_ the case, they usually try to do something
about it, and it they can't, they most likely won't survive to tell you
about it either".
"""

EVENT_FORMAT_STR = "!QB"
EVENT_PACKET_LENGTH = 9


class OFC_EVENT_TYPES(enum.Enum):
    TCP_TIMEOUT = 0                 # TCP timeout on the socket connected to the datapath
    ECHO_TIMEOUT = 1                # Datapath failed to respond to too many echo requests
    DATAPATH_JOINED = 2             # A new datapath has joined the network
    DATAPATH_RETURNED = 3           # A disconnected datapath recovered
    DATAPATH_POLITE_LEAVE = 4       # A datapath has removed all flows and requested a clean disconnect.
                                    # Usually, this means that they are not coming back!
    UNKNOWN = 5                     # Some weird IO error killed the connection
    ROLE_ACK = 6                    # The switch has recognized this controllers role

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
        self.buf = None

    def serialize(self):
        self.buf = bytearray(EVENT_PACKET_LENGTH)
        struct.pack_into(EVENT_FORMAT_STR, self.buf, 0, self.dp_id, self.reason.value)

    @classmethod
    def parse(cls, buf):
        (dp_id, reason) = struct.unpack_from(EVENT_FORMAT_STR, buf)
        return cls(dp_id, OFC_EVENT_TYPES(reason))

    def __str__(self):
        return f"{self.dp_id}: {self.reason.name}"


"""
NOTE:
    We need some UID for this IR. Until now, everything was handled
    by Mongo itself, but we can't actually put flow stat req. IRs up
    in the IR collection, so we have to generate an ID here.

    What we need, in order for this to work is at least:
    - The ID should be unique among the set of currently scheduled IRs
    - The ID should be unique among the set of switches currently being
      reconciled.

    Mongo uses 12 byte UIDs, where the first 4 bytes are UNIX time in
    seconds, so by using an old timestamp, we can guarantee that we do
    not conflict with the scheduled IRs. In order to not conflict with
    other switches, since every switch can have at most _one_ reconciliation
    request at each time, the simplest solution is to use the datapath ID
    of the switch, which just clocks at exactly 8 bytes!

    So our object ID for these IRs would be like this:

        +---------------+-------+
        | Old Timestamp | DP ID |
        +---------------+-------+

    For the timestamp, I just use some old fool's birthday (no points
    for guessing who that is ...).
"""


# This will be the first 4 bytes of each reconciliation IR UID
FLOW_STAT_UID_TIMESTAMP = 926035200

# UPDATE: This is like above, but for group stat reconciliation messages
GROUP_STAT_UID_TIMESTAMP = 996035200


# The format of the UID for reconciliation IRs
FLOW_STAT_FORMAT_STR = ">iQ"
FLOW_STAT_FORMAT_LENGTH = 12


# This returns the UID itself, not the byte array
def get_flow_stat_req_uid(dp_id):
    b = bytearray(FLOW_STAT_FORMAT_LENGTH)
    struct.pack_into(FLOW_STAT_FORMAT_STR, b, 0, FLOW_STAT_UID_TIMESTAMP, dp_id)

    return ObjectId(bytes(b))


# UPDATE: This is like above, but for group stat reconciliation messages
def get_group_stat_req_uid(dp_id):
    b = bytearray(FLOW_STAT_FORMAT_LENGTH)
    struct.pack_into(FLOW_STAT_FORMAT_STR, b, 0, GROUP_STAT_UID_TIMESTAMP, dp_id)

    return ObjectId(bytes(b))


"""
Before any OFC module is allowed to resume process, they must synchronize with each other
by contacting the Failover Handler (FH).

The handler will give them a GO signal and set their role.

Each failover message will have the following form:
- The message type                                  ( 1 byte )
- The module name of the sender                     ( 1 byte )
- Total message length                              ( 2 bytes)

The payload will be variable.
- ROLE_SET messages return both an ID and the role of the controller.
  The role is 1 byte, while the id is at most 24 characters in length.
- ROLE_ACK and SW_FAIL messages return a datapath id which is 8 bytes.
"""

MAXIMUM_IDENTITY_STRING_LENGTH = 24
FAILOVER_MESSAGE_HEADER_SIZE = 4

FAILOVER_MESSAGE_HEADER_FORMAT_STR = "!BBH"
ROLE_SET_MESSAGE_FORMAT_STR = ">B{max_len}s".format(max_len=MAXIMUM_IDENTITY_STRING_LENGTH)
DP_ID_MESSAGE_FORMAT_STR = "!Q"

FAILOVER_MESSAGE_ROLE_SET_SIZE = MAXIMUM_IDENTITY_STRING_LENGTH + 1
FAILOVER_MESSAGE_DP_ID_SIZE = 8


class OFC_FAILOVER_EVENT_TYPE(enum.Enum):
    HELLO = 0
    ROLE_SET = 1
    CLEAR = 2
    INIIT = 3
    TERMINATE_START = 4
    TERMINATE_FINISH = 5
    TERMINATE_ASYNC = 6
    STOP_PRODUCTION = 7
    STOPPED_PRODUCTION = 8
    START_EVENT_RECONCILIATION = 9
    FINISHED_EVENT_RECONCILIATION = 10
    RESUME_PRODUCTION = 11
    ROLE_ACKED = 12
    SW_FAIL = 13
    SW_BACK = 14

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


class OFC_FAILOVER_ENABLED_MODULE_STATE(enum.Enum):
    WAIT_FOR_CLEAR = 0        # Module is healthy, but block until FH gives the go signal
    CLEARED = 1               # Module is cleared to proceed. Normal operation
    MUST_TERMINATE = 2        # FH requested for graceful termination of this module
    TERMINATED = 3            # Module was gracefully terminated
    ASYNC_TERMINATE = 4       # Module asynchronously ceased communication (e.g. a user interrupt)
                              # we do not consider this a failure.
    FAILED = 5                # Module unexpectedly ceased communication. We assume the worst and
                              # call this case a failure.

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


class OFCFailoverMessage:
    def __init__(self, type: OFC_FAILOVER_EVENT_TYPE, module_name: CONTROLLER_MODULES,
                 identity: str = None, role: OFC_ROLE = None, dp_id = None):
        if identity:
            assert len(identity) <= MAXIMUM_IDENTITY_STRING_LENGTH

        self.type = type
        self.module_name = module_name
        self.identity = identity
        self.role = role
        self.dp_id = dp_id
        self.buf = None

    def __str__(self):
        return f"FailoverMessage: {self.type} FROM {self.module_name}"

    def serialize(self):
        l = FAILOVER_MESSAGE_HEADER_SIZE
        if self.type == OFC_FAILOVER_EVENT_TYPE.ROLE_SET:
            l += FAILOVER_MESSAGE_ROLE_SET_SIZE

        elif self.type == OFC_FAILOVER_EVENT_TYPE.ROLE_ACKED or \
                self.type == OFC_FAILOVER_EVENT_TYPE.SW_FAIL or \
                self.type == OFC_FAILOVER_EVENT_TYPE.SW_BACK:
            l += FAILOVER_MESSAGE_DP_ID_SIZE

        self.buf = bytearray(l)
        struct.pack_into(FAILOVER_MESSAGE_HEADER_FORMAT_STR, self.buf, 0,
                         self.type.value, self.module_name.value, l)

        if self.type == OFC_FAILOVER_EVENT_TYPE.ROLE_SET:
            struct.pack_into(ROLE_SET_MESSAGE_FORMAT_STR, self.buf, FAILOVER_MESSAGE_HEADER_SIZE,
                             self.role.value, self.identity.encode())

        elif self.type == OFC_FAILOVER_EVENT_TYPE.ROLE_ACKED or \
                self.type == OFC_FAILOVER_EVENT_TYPE.SW_FAIL or \
                self.type == OFC_FAILOVER_EVENT_TYPE.SW_BACK:
            struct.pack_into(DP_ID_MESSAGE_FORMAT_STR, self.buf, FAILOVER_MESSAGE_HEADER_SIZE,
                             self.dp_id)

    @classmethod
    def parse(cls, buf):
        (msg_type, module_name, length) = struct.unpack_from(FAILOVER_MESSAGE_HEADER_FORMAT_STR, buf)
        if msg_type == OFC_FAILOVER_EVENT_TYPE.ROLE_SET:
            (role, identity) = struct.unpack_from(ROLE_SET_MESSAGE_FORMAT_STR, buf, FAILOVER_MESSAGE_HEADER_SIZE)
            return cls(
                type = OFC_FAILOVER_EVENT_TYPE(msg_type),
                module_name = CONTROLLER_MODULES(module_name),
                identity = identity.rstrip(b'\x00').decode(),
                role = OFC_ROLE(role)
            )

        elif msg_type == OFC_FAILOVER_EVENT_TYPE.ROLE_ACKED or \
                msg_type == OFC_FAILOVER_EVENT_TYPE.SW_FAIL or \
                msg_type == OFC_FAILOVER_EVENT_TYPE.SW_BACK:
            dp_id = struct.unpack_from(DP_ID_MESSAGE_FORMAT_STR, buf, FAILOVER_MESSAGE_HEADER_SIZE)[0]
            return cls(
                type = OFC_FAILOVER_EVENT_TYPE(msg_type),
                module_name = CONTROLLER_MODULES(module_name),
                dp_id = dp_id
            )

        return cls(
            type=OFC_FAILOVER_EVENT_TYPE(msg_type),
            module_name=CONTROLLER_MODULES(module_name)
        )

    @staticmethod
    def unpack_header(buf):
        return struct.unpack_from(FAILOVER_MESSAGE_HEADER_FORMAT_STR, buf)

# For ROLE_REQ generation IDs, we just use current time in microseconds
get_gen_id = lambda: time.time_ns() // 1000

# For MS, used only when needed
def get_wildcard_role_req(role, datapath):
    role_req = OFPRoleRequest(
        datapath=datapath,
        role=role.value,
        generation_id=get_gen_id()
    )

    return role_req

is_of_message = lambda instance: isinstance(instance, MsgBase)


# TODO: Check this with Pooria!

"""
The initiation protocol for a controller joining a failover session is not part of
the TLA+ script. As such, we create a very simple and safe protocol to handle this phase.

When an OFC instance is created, it spawns 4 processes.
    The WorkerPool, EventHandler, MonitoringServer and FailoverHandler.

The first 3 modules synchronize with FailoverHandler, they will contact it and then block
until it gives a go signal to them.
This signal is given if and only if:
    - The initial role of the controller is published in NIB
    - Whether or not a failover process is underway is noted in the NIB

If a Failover process is not underway (normal operation), then a single contorller will assume
the role of master, and any other controller will become slave.
We are not interested in having multiple controllers outside of failover, so any slave contorller
under this scenario will immediately terminate and cleanup any data that it put on the NIB.

In case of a failover process, then the SLAVE and MASTER controller will cooperate to finish it:
    - First, SLAVE will be given the go signal by FailoverHandler and it will then block until every
      switch in NIB has acknowledged its role as a SLAVE controller by connecting to it.
    - Second, it will issue a role request of EQUAL to all of the switches and blocks until all
      of them respond. During this time, the controller is not allowed to perform any write operations
      on any switch and on NIB.
      This guarantees that if a switch failure happens, then corresponding events are only generated
      and processed by the MASTER controller.
    - Third, once it has a role of equal, it is allowed to handle IRs, but it is still not allowed to
      process topology events. During this process, it will also subscribe to the IR queue and receive
      messages from RC.
      The NIBQueue implementation will handle passing messages to MASTER and EQAUL without duplication.

During this transient state, the two controllers have write access to the switches. Only MASTER has
write access to topology events and can decide what to do with them.

Once we are in this state, the FailoverHandler(s) will both block. The network will function normally
if this state of operation was arbitrarily prolonged. In fact, this state is quick, since it essentially
means there are 2 worker pools working at the same time, which is safe.
For now, the FailoverHandler of EQUAL will block until it becomes MASTER.

At some point, the NIB failover state of the MASTER is changed to FAILOVER_TERMINATE, and this means that
the controller will start to gracefully terminate.
    - First, MASTER will unsubscribe from IR queue. This directs all IRs to the EQUAL.
    - Second, MASTER ....
"""