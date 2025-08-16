from pynadir.nadir import NadirProcess
from atomics.common import *
import atomics.operators as operators
import atomics.macros as macros


class controllerEventHandler(NadirProcess):
    num_cvs = 0
    
    def ControllerEventHandlerProc(self, local_provider):
        local_provider.set_value(
            self.get_pid(),
            "monitoringEvent",
            self.global_provider.fifo_peek(self.get_pid(), "swSeqChangedStatus")
            
        )
        if (operators.shouldSuspendRunningSw(self, local_provider.get_value("monitoringEvent", self.get_pid()))):
            return "ControllerSuspendSW"
        elif (operators.shouldClearSuspendedSw(self, local_provider.get_value("monitoringEvent", self.get_pid()))):
            return "ControllerRequestTCAMClear"
        elif (operators.shouldFreeSuspendedSw(self, local_provider.get_value("monitoringEvent", self.get_pid()))):
            return "ControllerCheckIfThisIsLastEvent"
        return "ControllerEvenHanlderRemoveEventFromQueue"
    
    def ControllerEventHandlerStateReconciliation(self, local_provider):
        _lastIR8 = self.global_provider.get_value("eventHandlerLastIRToReset", self.get_pid())
        
        if (_lastIR8 != None):
            macros.setNIBIRState(self, local_provider, _lastIR8, EnumIRState.IR_NONE)
            self.global_provider.fifo_put(self.get_pid(), "RCNIBEventQueue", MessageTEEvent(
                type=MODEL_VALUES.IR_MOD,
                IR=_lastIR8,
                state=EnumIRState.IR_NONE
            ))
            
        
        return "ControllerEventHandlerProc"
    
    def ControllerSuspendSW(self, local_provider):
        self.global_provider.set_value(
            self.get_pid(),
            "eventHandlerCheckpoint",
            True
        )
        self.global_provider.set_value(
            self.get_pid(),
            "SwSuspensionStatus",
            EnumSwitchState.SW_SUSPEND,
            [local_provider.get_value("monitoringEvent", self.get_pid(), ["swID"])]
        )
        self.global_provider.fifo_put(self.get_pid(), "RCNIBEventQueue", MessageTEEvent(
            type=MODEL_VALUES.TOPO_MOD,
            sw=local_provider.get_value("monitoringEvent", self.get_pid(), ["swID"]),
            state=EnumSwitchState.SW_SUSPEND
        ))
        return "ControllerEvenHanlderRemoveEventFromQueue"
    
    def getIRsToBeChecked(self, local_provider):
        local_provider.set_value(
            self.get_pid(),
            "setIRsToReset",
            operators.getIRSetToReset(self, local_provider.get_value("monitoringEvent", self.get_pid(), ["swID"]))
        )
        if ((len(local_provider.get_value("setIRsToReset", self.get_pid())) == 0)):
            return "ControllerFreeSuspendedSW"
        return "ResetAllIRs"
    
    def ResetAllIRs(self, local_provider):
        local_provider.set_value(
            self.get_pid(),
            "resetIR",
            conditional_choose(iter(local_provider.get_value("setIRsToReset", self.get_pid())), lambda x: True)
        )
        local_provider.set_value(
            self.get_pid(),
            "setIRsToReset",
            local_provider.get_value("setIRsToReset", self.get_pid()).difference({local_provider.get_value("resetIR", self.get_pid())})
        )
        self.global_provider.set_value(
            self.get_pid(),
            "eventHandlerLastIRToReset",
            local_provider.get_value("resetIR", self.get_pid())
        )
        macros.setNIBIRState(self, local_provider, local_provider.get_value("resetIR", self.get_pid()), EnumIRState.IR_NONE)
        self.global_provider.fifo_put(self.get_pid(), "RCNIBEventQueue", MessageTEEvent(
            type=MODEL_VALUES.IR_MOD,
            IR=local_provider.get_value("resetIR", self.get_pid()),
            state=EnumIRState.IR_NONE
        ))
        if (len(local_provider.get_value("setIRsToReset", self.get_pid())) == 0):
            return "ControllerFreeSuspendedSW"
        return "ResetAllIRs"
    
    def ControllerEvenHanlderRemoveEventFromQueue(self, local_provider):
        self.global_provider.set_value(
            self.get_pid(),
            "eventHandlerCheckpoint",
            False
        )
        self.global_provider.set_value(
            self.get_pid(),
            "eventHandlerTCAMCleared",
            False
        )
        self.global_provider.set_value(
            self.get_pid(),
            "eventHandlerLastIRToReset",
            None
        )
        self.global_provider.fifo_pop(self.get_pid(), "swSeqChangedStatus")
        return "ControllerEventHandlerProc"
    
    def ControllerFreeSuspendedSW(self, local_provider):
        self.global_provider.set_value(
            self.get_pid(),
            "eventHandlerCheckpoint",
            True
        )
        self.global_provider.set_value(
            self.get_pid(),
            "eventHandlerLastIRToReset",
            None
        )
        self.global_provider.set_value(
            self.get_pid(),
            "SwSuspensionStatus",
            EnumSwitchState.SW_RUN,
            [local_provider.get_value("monitoringEvent", self.get_pid(), ["swID"])]
        )
        self.global_provider.set_value(
            self.get_pid(),
            "eventHandlerTCAMCleared",
            True
        )
        self.global_provider.fifo_put(self.get_pid(), "RCNIBEventQueue", MessageTEEvent(
            type=MODEL_VALUES.TOPO_MOD,
            sw=local_provider.get_value("monitoringEvent", self.get_pid(), ["swID"]),
            state=EnumSwitchState.SW_RUN
        ))
        return "ControllerEvenHanlderRemoveEventFromQueue"
    
    def ControllerRequestTCAMClear(self, local_provider):
        if (not operators.existsMonitoringEventHigherNum(self, local_provider.get_value("monitoringEvent", self.get_pid()))):
            self.global_provider.ack_queue_put(self.get_pid(), "IRQueueNIB", StructIR(
                IR=NadirUID(0),
                sw=local_provider.get_value("monitoringEvent", self.get_pid(), ["swID"])
            ))
            return "ControllerEvenHanlderRemoveEventFromQueue"
        return "ControllerEvenHanlderRemoveEventFromQueue"
    
    def ControllerCheckIfThisIsLastEvent(self, local_provider):
        if (not operators.existsMonitoringEventHigherNum(self, local_provider.get_value("monitoringEvent", self.get_pid())) and \
        not self.global_provider.get_value("eventHandlerTCAMCleared", self.get_pid())):
            return "getIRsToBeChecked"
        return "ControllerFreeSuspendedSW"
    

