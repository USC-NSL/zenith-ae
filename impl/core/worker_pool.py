from pynadir.nadir import NadirProcess
from atomics.common import *
import atomics.operators as operators
import atomics.macros as macros


class controllerWorkerThreads(NadirProcess):
    num_cvs = 0
    
    def ControllerThreadSendIR(self, local_provider):
        if (operators.isClearIR(self, local_provider.get_value("nextIRObjectToSend", self.get_pid(), ["IR"]))):
            if (operators.isSwitchSuspended(self, local_provider.get_value("nextIRObjectToSend", self.get_pid(), ["sw"]))):
                macros.controllerSendIR(self, local_provider, local_provider.get_value("nextIRObjectToSend", self.get_pid()))
                return "ControllerThreadRemoveIRFromQueue"
            return "ControllerThreadRemoveIRFromQueue"
        elif (operators.getNIBIRState(self, local_provider.get_value("nextIRObjectToSend", self.get_pid(), ["IR"])) in {EnumIRState.IR_NONE, EnumIRState.IR_SENT}):
            if (operators.isSwitchSuspended(self, local_provider.get_value("nextIRObjectToSend", self.get_pid(), ["sw"]))):
                self.global_provider.fifo_put(self.get_pid(), "RCNIBEventQueue", MessageTEEvent(
                    type=MODEL_VALUES.IR_FAILED,
                    IR=local_provider.get_value("nextIRObjectToSend", self.get_pid(), ["IR"]),
                    state=EnumIRState.IR_NONE
                ))
                return "ControllerThreadRemoveIRFromQueue"
            else:
                macros.setNIBIRState(self, local_provider, local_provider.get_value("nextIRObjectToSend", self.get_pid(), ["IR"]), EnumIRState.IR_SENT)
                self.global_provider.fifo_put(self.get_pid(), "RCNIBEventQueue", MessageTEEvent(
                    type=MODEL_VALUES.IR_MOD,
                    IR=local_provider.get_value("nextIRObjectToSend", self.get_pid(), ["IR"]),
                    state=EnumIRState.IR_SENT
                ))
                return "ControllerThreadForwardIR"
        else:
            # NO_GEN
            self.global_provider.fifo_put(self.get_pid(), "RCNIBEventQueue", MessageTEEvent(
                type=MODEL_VALUES.IR_FAILED,
                IR=local_provider.get_value("nextIRObjectToSend", self.get_pid(), ["IR"]),
                state=EnumIRState.IR_DONE
            ))
            # NO_GEN
            
        return "ControllerThreadRemoveIRFromQueue"
    
    def ControllerThreadRemoveIRFromQueue(self, local_provider):
        self.global_provider.ack_queue_ack(self.get_pid(), "IRQueueNIB")
        return "ControllerThread"
    
    def ControllerThreadForwardIR(self, local_provider):
        macros.controllerSendIR(self, local_provider, local_provider.get_value("nextIRObjectToSend", self.get_pid()))
        return "ControllerThreadRemoveIRFromQueue"
    
    def ControllerThread(self, local_provider):
        local_provider.set_value(
            self.get_pid(),
            "nextIRObjectToSend",
            self.global_provider.ack_queue_get(self.get_pid(), "IRQueueNIB")
            
        )
        return "ControllerThreadSendIR"
    

