from collections import deque
from pynadir.nadir import NadirProcess
from atomics.common import *
import atomics.operators as operators
import atomics.macros as macros


class controllerMonitoringServer(NadirProcess):
    num_cvs = 0
    SW2IR = None
    
    def MonitoringServerRemoveFromQueue(self, local_provider):
        self.global_provider.fifo_pop(self.get_pid(), "switch2Controller")
        return "ControllerMonitorCheckIfMastr"
    
    def ControllerProcessIRMod(self, local_provider):
        local_provider.set_value(
            self.get_pid(),
            "irID",
            operators.getIRIDForFlow(self, local_provider.get_value("msg", self.get_pid(), ["flow"]), local_provider.get_value("msg", self.get_pid(), ["type"]))
        )
        macros.setNIBIRState(self, local_provider, local_provider.get_value("irID", self.get_pid()), EnumIRState.IR_DONE)
        self.global_provider.fifo_put(self.get_pid(), "RCNIBEventQueue", MessageTEEvent(
            type=MODEL_VALUES.IR_MOD,
            IR=local_provider.get_value("irID", self.get_pid()),
            state=EnumIRState.IR_DONE
        ))
        return "MonitoringServerRemoveFromQueue"
    
    def ForwardToEH(self, local_provider):
        self.global_provider.fifo_put(self.get_pid(), "swSeqChangedStatus", local_provider.get_value("msg", self.get_pid()))
        return "MonitoringServerRemoveFromQueue"
    
    def ControllerMonitorCheckIfMastr(self, local_provider):
        if self.SW2IR is None:
            SW2IR = dict()
            IR2SW = self.input_provider.get_value("IR2SW", self.get_pid())
            for ir in self.global_provider.get_uid_iterator('irs', 1, self.input_provider.get_value("MaxNumIRs", self.get_pid())):
                sw = IR2SW[ir]
                if sw not in SW2IR:
                    SW2IR[sw] = set()
                SW2IR[sw].add(ir)
            self.SW2IR = SW2IR
        
        local_provider.set_value(
            self.get_pid(),
            "msg",
            self.global_provider.fifo_peek(self.get_pid(), "switch2Controller")   
        )

        if (local_provider.get_value("msg", self.get_pid(), ["type"]) == EnumReconciliationResponse.ENTRY_FOUND):
            return "ControllerHandleReconciliation"
        elif (local_provider.get_value("msg", self.get_pid(), ["type"]) in {EnumOpenFlowACK.DELETED_SUCCESSFULLY, EnumOpenFlowACK.INSTALLED_SUCCESSFULLY}):
            return "ControllerProcessIRMod"
        else:
            return "ForwardToEH"
        
    
    def ControllerHandleReconciliation(self, local_provider):
        message = local_provider.get_value("msg", self.get_pid())
        source = message.source
        flows: Set = message.flows
        dp_id = self.input_provider.get_int_from_uid(source)
        dones, nones = operators.getDonesAndNones(self, self.SW2IR[source])
        should_be_dones = deque(nones.intersection(flows))
        should_be_nones = deque(dones.difference(flows))

        if len(should_be_dones) > 0:
            print(f"[ RECONCILIATION ]: For DP ID {dp_id}, {len(should_be_dones)} should be DONE, but or not")
            local_provider.set_value(self.get_pid(), "shouldBeDones", should_be_dones)
        if len(should_be_nones) > 0:
            print(f"[ RECONCILIATION ]: For DP ID {dp_id}, {len(should_be_nones)} should be NONE, but or not")
            local_provider.set_value(self.get_pid(), "shouldBeNones", should_be_nones)

        if len(should_be_dones) == 0 and len(should_be_nones) == 0:
            return "MonitoringServerRemoveFromQueue"
        else:
            return "ControllerCommitReconciliation"

    def ControllerCommitReconciliation(self, local_provider):
        should_be_dones = local_provider.get_value("shouldBeDones", self.get_pid())
        should_be_nones = local_provider.get_value("shouldBeNones", self.get_pid())
        done = True
        if len(should_be_dones) > 0:
            current = should_be_dones.popleft()
        elif len(should_be_nones) > 0:
            done = False
            current = should_be_nones.popleft()
        else:
            return "MonitoringServerRemoveFromQueue"

        if done:
            self.global_provider.set_value(
                self.get_pid(),
                "NIBIRStatus",
                EnumIRState.IR_DONE,
                [current]
            )
            self.global_provider.fifo_put(self.get_pid(), "RCNIBEventQueue", MessageTEEvent(
                type=MODEL_VALUES.IR_MOD,
                IR=current,
                state=EnumIRState.IR_DONE
            ))
        else:
            self.global_provider.set_value(
                self.get_pid(),
                "NIBIRStatus",
                EnumIRState.IR_NONE,
                [current]
            )
            self.global_provider.fifo_put(self.get_pid(), "RCNIBEventQueue", MessageTEEvent(
                type=MODEL_VALUES.IR_MOD,
                IR=current,
                state=EnumIRState.IR_NONE
            ))
        return "ControllerCommitReconciliation"
