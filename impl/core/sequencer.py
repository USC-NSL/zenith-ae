from pynadir.nadir import NadirProcess
from atomics.common import *
import atomics.operators as operators
import atomics.macros as macros


class controllerBossSequencer(NadirProcess):
    num_cvs = 1
    
    def WaitForRCSeqWorkerTerminate(self, local_provider):
        self.global_provider.wait(self.get_pid(), self._cvs[0], lambda _provider: _provider.get_value("seqWorkerIsBusy", self.get_pid()) == False)
        self.global_provider.set_value(
            self.get_pid(),
            "DAGState",
            EnumDAGState.DAG_NONE,
            [local_provider.get_value("seqEvent", self.get_pid(), ["id"])]
        )
        return "ControllerBossSeqProc"
    
    def ControllerBossSeqProc(self, local_provider):
        local_provider.set_value(
            self.get_pid(),
            "seqEvent",
            self.global_provider.fifo_get(self.get_pid(), "DAGEventQueue")
            
        )
        if (local_provider.get_value("seqEvent", self.get_pid(), ["type"]) == MODEL_VALUES.DAG_NEW):
            self.global_provider.fifo_put(self.get_pid(), "DAGQueue", local_provider.get_value("seqEvent", self.get_pid(), ["dag_obj"]))
            return "ControllerBossSeqProc"
        else:
            if (self.global_provider.get_value("seqWorkerIsBusy", self.get_pid()) != False):
                return "WaitForRCSeqWorkerTerminate"
            else:
                self.global_provider.set_value(
                    self.get_pid(),
                    "DAGState",
                    EnumDAGState.DAG_NONE,
                    [local_provider.get_value("seqEvent", self.get_pid(), ["id"])]
                )
                return "ControllerBossSeqProc"
            
        
    

class controllerSequencer(NadirProcess):
    num_cvs = 1
    
    def ControllerWorkerSeqScheduleDAG(self, local_provider):
        if (operators.dagObjectShouldBeProcessed(self, local_provider.get_value("currDAG", self.get_pid()))):
            local_provider.set_value(
                self.get_pid(),
                "toBeScheduledIRs",
                operators.getSetIRsCanBeScheduledNext(self, local_provider.get_value("currDAG", self.get_pid(), ["dag"]))
            )
            self.global_provider.wait(self.get_pid(), self._cvs[0], lambda _provider: len(local_provider.get_value("toBeScheduledIRs", self.get_pid())) > 0)
            return "SchedulerMechanism"
        self.global_provider.set_value(
            self.get_pid(),
            "seqWorkerIsBusy",
            False
        )
        if (operators.allIRsInDAGInstalled(self, local_provider.get_value("currDAG", self.get_pid(), ["dag"]))):
            local_provider.set_value(
                self.get_pid(),
                "IRDoneSet",
                operators.AddDeleteDAGIRDoneSet(self, local_provider.get_value("currDAG", self.get_pid(), ["dag", "v"]), local_provider.get_value("IRDoneSet", self.get_pid()))
            )
            return "RemoveDagFromQueue"
        return "RemoveDagFromQueue"
    
    def RemoveDagFromQueue(self, local_provider):
        self.global_provider.fifo_pop(self.get_pid(), "DAGQueue")
        operators.recordDAGFinish(self, operators.isDAGStale(self, local_provider.get_value("currDAG", self.get_pid(), ["id"]))) # NO_GEN
        return "ControllerWorkerSeqProc"
    
    def SchedulerMechanism(self, local_provider):
        if (len(local_provider.get_value("toBeScheduledIRs", self.get_pid())) == 0 or \
        operators.isDAGStale(self, local_provider.get_value("currDAG", self.get_pid(), ["id"]))):
            return "ControllerWorkerSeqScheduleDAG"
        else:
            local_provider.set_value(
                self.get_pid(),
                "nextIR",
                conditional_choose(iter(local_provider.get_value("toBeScheduledIRs", self.get_pid())), lambda x: True)
            )
            _destination7 = operators.getSwitchForIR(self, local_provider.get_value("nextIR", self.get_pid()))
            
            self.global_provider.set_value(
                self.get_pid(),
                "ScheduledIRs",
                True,
                [local_provider.get_value("nextIR", self.get_pid())]
            )

            if (operators.getIRType(self, local_provider.get_value("nextIR", self.get_pid())) == EnumOpenFlowCMD.INSTALL_FLOW):
                local_provider.set_value(
                    self.get_pid(),
                    "IRDoneSet",
                    local_provider.get_value("IRDoneSet", self.get_pid()).union({local_provider.get_value("nextIR", self.get_pid())})
                )
                
            else:
                local_provider.set_value(
                    self.get_pid(),
                    "IRDoneSet",
                    local_provider.get_value("IRDoneSet", self.get_pid()).difference({operators.getDualOfIR(self, local_provider.get_value("nextIR", self.get_pid()))})
                )
                
            self.global_provider.ack_queue_put(self.get_pid(), "IRQueueNIB", StructIR(
                IR=local_provider.get_value("nextIR", self.get_pid()),
                sw=_destination7
            ))
            local_provider.set_value(
                self.get_pid(),
                "toBeScheduledIRs",
                local_provider.get_value("toBeScheduledIRs", self.get_pid()).difference({local_provider.get_value("nextIR", self.get_pid())})
            )
            operators.markDAGAsEventful(self) # NO_GEN
            return "SchedulerMechanism"
            
        
    
    def ControllerWorkerSeqProc(self, local_provider):
        local_provider.set_value(
            self.get_pid(),
            "currDAG",
            self.global_provider.fifo_peek(self.get_pid(), "DAGQueue")
            
        )
        self.global_provider.set_value(
            self.get_pid(),
            "seqWorkerIsBusy",
            True
        )
        operators.recordDAGStart(self, local_provider.get_value("currDAG", self.get_pid())) # NO_GEN
        return "ControllerWorkerSeqScheduleDAG"
    

