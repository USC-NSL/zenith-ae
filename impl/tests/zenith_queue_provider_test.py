from typing import Union
from pynadir.zenith_providers.queue_provider import *
from pynadir.structures import NadirModelValue, NadirModelValueAggregate

provider = RabbitProvider()

pid = NadirPID(NadirModelValue("mod"), NadirModelValue("thread"))

provider.register_pid(pid)
provider.nuke()

provider.add_value("RCNIBEventQueue", [], interacting_pids=[pid])
provider.add_value("TEEventQueue", [], interacting_pids=[pid])
provider.add_value("DAGEventQueue", [], interacting_pids=[pid])
provider.add_value("DAGQueue", [], interacting_pids=[pid])

from typing import Set
from pynadir.structures import nadir_dataclass, NadirUID, NadirStructBase, NadirUnionType

MODEL_VALUES = NadirModelValueAggregate([
    "SW_RECONCILE",
    "CONT_BOSS_SEQ",
    "CONT_RC_MONITOR",
    "CONT_WORKER_SEQ",
    "t1",
    "CONT_EVENT",
    "CONT_OFC_MONITOR",
    "rc0",
    "NIB_EVENT_HANDLER",
    "ALL_FLOW",
    "FLOW_STAT_REQ",
    "NO_ENTRY",
    "CONT_TE",
    "t0",
    "ofc0",
    "FLOW_STAT_REPLY",
    "ENTRY_FOUND"
])

NADIR_PID_SET = [
    NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.t1),  # noqa
    NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.CONT_WORKER_SEQ),  # noqa
    NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.CONT_TE),  # noqa
    NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.t0),  # noqa
    NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.CONT_BOSS_SEQ),  # noqa
    NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.CONT_EVENT),  # noqa
    NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.NIB_EVENT_HANDLER),  # noqa
    NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.CONT_RC_MONITOR),  # noqa
    NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.CONT_OFC_MONITOR)  # noqa
]


class EnumDAGState:
    DAG_SUBMIT = "DAG_SUBMIT"
    DAG_NONE = "DAG_NONE"
    DAG_STALE = "DAG_STALE"
    DAG_NEW = "DAG_NEW"


class EnumOpenFlowACK:
    INSTALLED_SUCCESSFULLY = "INSTALLED_SUCCESSFULLY"
    DELETED_SUCCESSFULLY = "DELETED_SUCCESSFULLY"
    KEEP_ALIVE = "KEEP_ALIVE"


class EnumRCShcedulerInternalState:
    STATUS_START_SCHEDULING = "STATUS_START_SCHEDULING"


class EnumOFCEventHandlerInternalState:
    START_RESET_IR = "START_RESET_IR"


class EnumIRState:
    IR_NONE = "IR_NONE"
    IR_SENT = "IR_SENT"
    IR_DONE = "IR_DONE"


class EnumOFCWorkerPoolInternalState:
    STATUS_LOCKING = "STATUS_LOCKING"
    STATUS_SENT_DONE = "STATUS_SENT_DONE"


class EnumRCTEEventType:
    TOPO_MOD = "TOPO_MOD"
    IR_MOD = "IR_MOD"


class EnumInstallerStatus:
    INSTALLER_DOWN = "INSTALLER_DOWN"
    INSTALLER_UP = "INSTALLER_UP"


class EnumSwitchModuleFailureStatus:
    NIC_ASIC_DOWN = "NIC_ASIC_DOWN"
    OFA_DOWN = "OFA_DOWN"


class EnumSwitchState:
    SW_SUSPEND = "SW_SUSPEND"
    SW_RUN = "SW_RUN"


class EnumOpenFlowCMD:
    INSTALL_FLOW = "INSTALL_FLOW"
    DELETE_FLOW = "DELETE_FLOW"


@nadir_dataclass(frozen=True)
class StructRCDAG(NadirStructBase):
    v: Set[NadirUID]
    e: Set[Tuple[NadirUID, NadirUID]]


@nadir_dataclass(frozen=True)
class StructDAGObject(NadirStructBase):
    id: NadirUID
    dag: StructRCDAG


@nadir_dataclass(frozen=True)
class StructRCSchedulerInternalState(NadirStructBase):
    type: EnumRCShcedulerInternalState
    next: NadirUID


@nadir_dataclass(frozen=True)
class StructRCInternalState(NadirStructBase):
    type: EnumRCShcedulerInternalState
    next: NadirUID


@nadir_dataclass(frozen=True)
class StructOFCWorkerPoolInternalState(NadirStructBase):
    type: EnumOFCWorkerPoolInternalState
    next: NadirUID


@nadir_dataclass(frozen=True)
class StructOFCEventHandlerInternalState(NadirStructBase):
    type: EnumOFCEventHandlerInternalState
    sw: NadirModelValue


class StructOFCInternalState(NadirUnionType):
    classes = [StructOFCWorkerPoolInternalState, StructOFCEventHandlerInternalState]


@nadir_dataclass(frozen=True)
class MessageSwitchTimeout(NadirStructBase):
    swID: NadirModelValue
    num: int
    type: EnumSwitchModuleFailureStatus


@nadir_dataclass(frozen=True)
class MessageSwitchKeepalive(NadirStructBase):
    swID: NadirModelValue
    num: int
    type: EnumOpenFlowACK
    status: Dict[str, Union[EnumInstallerStatus]]


class MessageSwitchStatus(NadirUnionType):
    classes = [MessageSwitchTimeout, MessageSwitchKeepalive]


@nadir_dataclass(frozen=True)
class MessageOpenFlowCMD(NadirStructBase):
    type: EnumOpenFlowCMD
    to: NadirModelValue
    flow: int


@nadir_dataclass(frozen=True)
class MessageOpenFlowACK(NadirStructBase):
    type: EnumOpenFlowACK
    fromSw: NadirModelValue
    flow: int


@nadir_dataclass(frozen=True)
class MessageSwitchEvent(NadirStructBase):
    type: EnumRCTEEventType
    sw: NadirModelValue
    state: EnumSwitchState


@nadir_dataclass(frozen=True)
class MessageIREvent(NadirStructBase):
    type: EnumRCTEEventType
    state: EnumIRState
    IR: NadirUID


class MessageTEEvent(NadirUnionType):
    classes = [MessageIREvent, MessageSwitchEvent]


@nadir_dataclass(frozen=True)
class MessageStaleNotif(NadirStructBase):
    type: EnumDAGState
    id: NadirUID


@nadir_dataclass(frozen=True)
class MessageNewDAG(NadirStructBase):
    type: EnumDAGState
    dag_obj: StructDAGObject


class MessageDAGEvent(NadirUnionType):
    classes = [MessageStaleNotif, MessageNewDAG]


@nadir_dataclass(frozen=True)
class MessageNIBTaggedIR(NadirStructBase):
    IR: NadirUID
    tag: NadirPID


StructOFCInternalState.register_union()
MessageSwitchStatus.register_union()
MessageTEEvent.register_union()
MessageDAGEvent.register_union()


def test_1():
    dag = StructRCDAG({NadirUID(1), NadirUID(2)}, {(NadirUID(1), NadirUID(2))})
    obj = StructDAGObject(NadirUID(10), dag)

    provider.put_message(pid, "DAGQueue", obj)
    provider.commit(pid)

    _obj = provider.peek_message(pid, "DAGQueue")
    assert obj == _obj
    provider.pop_message(pid, "DAGQueue")

    provider.commit(pid)
