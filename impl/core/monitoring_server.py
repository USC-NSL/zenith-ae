from pynadir.nadir import NadirProcess
from atomics.common import *
import atomics.operators as operators
import atomics.macros as macros


class controllerMonitoringServer(NadirProcess):
    num_cvs = 0
    
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
        local_provider.set_value(
            self.get_pid(),
            "msg",
            self.global_provider.fifo_peek(self.get_pid(), "switch2Controller")
            
        )
        if (local_provider.get_value("msg", self.get_pid(), ["type"]) in {EnumOpenFlowACK.DELETED_SUCCESSFULLY, EnumOpenFlowACK.INSTALLED_SUCCESSFULLY}):
            return "ControllerProcessIRMod"
        else:
            return "ForwardToEH"
        
    

