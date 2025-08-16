from typing import Tuple, Union
from pynadir.structures import *
import networkx as nx # NO_GEN


"""
Contains the definitions for constants and symbols that all processes need.
Things like Model Values, Enums, Structs and Messages.
If new processes are introduced by choice of the user, they must be given PIDs here.
"""

MODEL_VALUES = NadirModelValueAggregate([
    "rc0",
    "TOPO_MOD",
    "NIB_EVENT_HANDLER",
    "CONT_BOSS_SEQ",
    "IR_MOD",
    "CONT_MONITOR",
    "CONT_TE",
    "CONT_EVENT",
    "DAG_NEW",
    "CONT_WORKER_SEQ",
    "NIC_ASIC_DOWN",
    "OFA_DOWN",
    "IR_FAILED",
    "t0",
    "ofc0",
    "KEEP_ALIVE",
    "CLEARED_TCAM_SUCCESSFULLY"
])

NADIR_PID_SET = [
    NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.CONT_WORKER_SEQ),
    NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.CONT_MONITOR),
    NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.CONT_TE),
    NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.t0),
    NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.CONT_BOSS_SEQ),
    NadirPID(MODEL_VALUES.ofc0, MODEL_VALUES.CONT_EVENT),
    NadirPID(MODEL_VALUES.rc0, MODEL_VALUES.NIB_EVENT_HANDLER)
]

class EnumOpenFlowCMD:
    INSTALL_FLOW = "INSTALL_FLOW"
    DELETE_FLOW = "DELETE_FLOW"
    CLEAR_TCAM = "CLEAR_TCAM"
    
    
class EnumInstallerStatus:
    INSTALLER_DOWN = "INSTALLER_DOWN"
    INSTALLER_UP = "INSTALLER_UP"
    
    
class EnumDAGState:
    DAG_SUBMIT = "DAG_SUBMIT"
    DAG_NONE = "DAG_NONE"
    DAG_STALE = "DAG_STALE"
    
    
class EnumSwitchState:
    SW_SUSPEND = "SW_SUSPEND"
    SW_RUN = "SW_RUN"
    
    
class EnumOpenFlowACK:
    INSTALLED_SUCCESSFULLY = "INSTALLED_SUCCESSFULLY"
    DELETED_SUCCESSFULLY = "DELETED_SUCCESSFULLY"
    
    
class EnumIRState:
    IR_NONE = "IR_NONE"
    IR_SENT = "IR_SENT"
    IR_DONE = "IR_DONE"
    
    
# @nadir_dataclass(frozen=True)
@nadir_dataclass() # NO_GEN
class StructRCDAG(NadirStructBase):
    v: Set[NadirUID]
    e: Set[Tuple[NadirUID, NadirUID]]

    # NO_GEN BEGIN
    def make_graph(self):
        graph = nx.DiGraph(self.e)
        self.graph = graph

    def get_ancestors(self, uid: NadirUID):
        return nx.ancestors(self.graph, uid)
    # NO_GEN END
    
    
@nadir_dataclass(frozen=True)
class StructDAGObject(NadirStructBase):
    id: NadirUID
    dag: StructRCDAG
    
    
@nadir_dataclass(frozen=True)
class StructIR(NadirStructBase):
    IR: NadirUID
    sw: int
    
    
@nadir_dataclass(frozen=True)
class StructIRPair(NadirStructBase):
    primary: EnumIRState
    dual: EnumIRState
    
    
@nadir_dataclass(frozen=True)
class StructNIBTaggedIR(NadirStructBase):
    data: StructIR
    tag: NadirPID
    
    
@nadir_dataclass(frozen=True)
class MessageSwitchTimeout(NadirStructBase):
    swID: int
    num: int
    type: NadirModelValue
    
    
@nadir_dataclass(frozen=True)
class MessageSwitchKeepalive(NadirStructBase):
    swID: int
    num: int
    type: NadirModelValue
    installerStatus: EnumInstallerStatus
    
    
@nadir_dataclass(frozen=True)
class MessageOpenFlowCMD(NadirStructBase):
    source: NadirModelValue
    type: EnumOpenFlowCMD
    to: int
    flow: int
    
    
@nadir_dataclass(frozen=True)
class MessageOpenFlowACK(NadirStructBase):
    to: NadirModelValue
    type: EnumOpenFlowACK
    source: int
    flow: int
    
    
class MessageSwitchEvent(NadirUnionType):
    classes = [MessageOpenFlowACK, MessageSwitchTimeout, MessageSwitchKeepalive]
    
    
@nadir_dataclass(frozen=True)
class MessageTopoMod(NadirStructBase):
    type: NadirModelValue
    sw: int
    state: EnumSwitchState
    
    
@nadir_dataclass(frozen=True)
class MessageIRMod(NadirStructBase):
    type: NadirModelValue
    state: EnumIRState
    IR: NadirUID
    
    
@nadir_dataclass(frozen=True)
class MessageIRFail(NadirStructBase):
    type: NadirModelValue
    state: EnumIRState
    IR: NadirUID
    
    
class MessageTEEvent(NadirUnionType):
    classes = [MessageIRMod, MessageTopoMod, MessageIRFail]
    
    
@nadir_dataclass(frozen=True)
class MessageDAGStaleNotif(NadirStructBase):
    type: EnumDAGState
    id: NadirUID
    
    
@nadir_dataclass(frozen=True)
class MessageDAGNewNotif(NadirStructBase):
    type: NadirModelValue
    dag_obj: StructDAGObject
    
    
class MessageDAGEvent(NadirUnionType):
    classes = [MessageDAGStaleNotif, MessageDAGNewNotif]
    
    

MessageSwitchEvent.register_union()
MessageTEEvent.register_union()
MessageDAGEvent.register_union()


# NO_GEN_BEGIN
MODEL_VALUES.add_mv("CONT_RECONCILER")


class EnumReconciliationResponse:
    ENTRY_FOUND = "ENTRY_FOUND"
    NO_ENTRIES = "NO_ENTRIES"


@nadir_dataclass(frozen=True)
class MessageReconciliationResponse(NadirStructBase):
    to: NadirModelValue
    type: EnumOpenFlowACK
    source: int
    flows: Set[int]
# NO_GEN_END