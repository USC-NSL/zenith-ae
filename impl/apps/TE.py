from pynadir.nadir import NadirProcess
from atomics.common import *
import atomics.operators as operators
import atomics.macros as macros


class rcNibEventHandler(NadirProcess):
    num_cvs = 0
    
    def RCSNIBEventHndlerProc(self, local_provider):
        local_provider.set_value(
            self.get_pid(),
            "event",
            self.global_provider.fifo_peek(self.get_pid(), "RCNIBEventQueue")
            
        )
        if ((local_provider.get_value("event", self.get_pid(), ["type"]) == MODEL_VALUES.TOPO_MOD)):
            if (self.global_provider.get_value("RCSwSuspensionStatus", self.get_pid(), [local_provider.get_value("event", self.get_pid(), ["sw"])]) != local_provider.get_value("event", self.get_pid(), ["state"])):
                self.global_provider.set_value(
                    self.get_pid(),
                    "RCSwSuspensionStatus",
                    local_provider.get_value("event", self.get_pid(), ["state"]),
                    [local_provider.get_value("event", self.get_pid(), ["sw"])]
                )
                self.global_provider.fifo_put(self.get_pid(), "TEEventQueue", local_provider.get_value("event", self.get_pid()))
                
            
        elif ((local_provider.get_value("event", self.get_pid(), ["type"]) == MODEL_VALUES.IR_MOD)):
            if (operators.getRCIRState(self, local_provider.get_value("event", self.get_pid(), ["IR"])) != local_provider.get_value("event", self.get_pid(), ["state"])):
                macros.setRCIRState(self, local_provider, local_provider.get_value("event", self.get_pid(), ["IR"]), local_provider.get_value("event", self.get_pid(), ["state"]))
                
                self.global_provider.set_value(
                    self.get_pid(),
                    "ScheduledIRs",
                    False,
                    [local_provider.get_value("event", self.get_pid(), ["IR"])]
                )
                # TitledLog.info("sched", f"------ Unscheduling: {local_provider.get_value('event', self.get_pid(), ['IR'])}")
                
            
        elif ((local_provider.get_value("event", self.get_pid(), ["type"]) == MODEL_VALUES.IR_FAILED)):
            self.global_provider.set_value(
                self.get_pid(),
                "ScheduledIRs",
                False,
                [local_provider.get_value("event", self.get_pid(), ["IR"])]
            )
            # TitledLog.info("sched", f"****** Unscheduling: {local_provider.get_value('event', self.get_pid(), ['IR'])}")
            
            
        self.global_provider.fifo_pop(self.get_pid(), "RCNIBEventQueue")
        return "RCSNIBEventHndlerProc"
    

class controllerTrafficEngineering(NadirProcess):
    num_cvs = 1
    
    def ControllerTEEventProcessing(self, local_provider):
        if (local_provider.get_value("init", self.get_pid()) != True):
            if (local_provider.get_value("topoChangeEvent", self.get_pid()) == None):
                local_provider.set_value(
                    self.get_pid(),
                    "topoChangeEvent",
                    self.global_provider.fifo_peek_nb(self.get_pid(), "TEEventQueue")
                    
                )
                if (local_provider.get_value("topoChangeEvent", self.get_pid()) == None):
                    return "ControllerTEComputeDagBasedOnTopo"
                return "ControllerTEEventProcessing"
            else:
                if (local_provider.get_value("topoChangeEvent", self.get_pid(), ["state"]) == EnumSwitchState.SW_SUSPEND):
                    local_provider.set_value(
                        self.get_pid(),
                        "currSetDownSw",
                        local_provider.get_value("currSetDownSw", self.get_pid()).union({local_provider.get_value("topoChangeEvent", self.get_pid(), ["sw"])})
                    )
                    
                else:
                    local_provider.set_value(
                        self.get_pid(),
                        "currSetDownSw",
                        local_provider.get_value("currSetDownSw", self.get_pid()).difference({local_provider.get_value("topoChangeEvent", self.get_pid(), ["sw"])})
                    )
                    
                self.global_provider.fifo_pop(self.get_pid(), "TEEventQueue")
                local_provider.set_value(
                    self.get_pid(),
                    "topoChangeEvent",
                    None
                )
                return "ControllerTEEventProcessing"
            
        return "ControllerTEComputeDagBasedOnTopo"
    
    def ControllerTEProc(self, local_provider):
        if (local_provider.get_value("init", self.get_pid()) == True):
            return "ControllerTEComputeDagBasedOnTopo"
        else:
            local_provider.set_value(
                self.get_pid(),
                "topoChangeEvent",
                self.global_provider.fifo_peek(self.get_pid(), "TEEventQueue")
                
            )
            return "ControllerTEEventProcessing"
        
    
    def ControllerTEComputeDagBasedOnTopo(self, local_provider):
        macros.getNextDAGID(self, local_provider)
        local_provider.set_value(
            self.get_pid(),
            "nxtDAG",
            {"id": local_provider.get_value("DAGID", self.get_pid()), "dag": self.input_provider.get_value("TOPO_DAG_MAPPING", self.get_pid(), [local_provider.get_value("currSetDownSw", self.get_pid())])}
        )
        local_provider.set_value(
            self.get_pid(),
            "nxtDAGVertices",
            local_provider.get_value("nxtDAG", self.get_pid(), ["dag", "v"])
        )
        if (local_provider.get_value("init", self.get_pid()) == False):
            self.global_provider.set_value(
                self.get_pid(),
                "DAGState",
                EnumDAGState.DAG_STALE,
                [local_provider.get_value("prev_dag_id", self.get_pid())]
            )
            self.global_provider.fifo_put(self.get_pid(), "DAGEventQueue", MessageDAGEvent(
                type=EnumDAGState.DAG_STALE,
                id=local_provider.get_value("prev_dag_id", self.get_pid())
            ))
            return "ControllerTEWaitForStaleDAGToBeRemoved"
        else:
            local_provider.set_value(
                self.get_pid(),
                "init",
                False
            )
            local_provider.set_value(
                self.get_pid(),
                "prev_dag_id",
                local_provider.get_value("DAGID", self.get_pid())
            )
            return "ControllerTERemoveUnnecessaryIRs"
        
    
    def ControllerTESubmitNewDAG(self, local_provider):
        self.global_provider.set_value(
            self.get_pid(),
            "DAGState",
            EnumDAGState.DAG_SUBMIT,
            [local_provider.get_value("nxtDAG", self.get_pid(), ["id"])]
        )
        self.global_provider.fifo_put(self.get_pid(), "DAGEventQueue", MessageDAGEvent(
            type=MODEL_VALUES.DAG_NEW,
            dag_obj=local_provider.get_value("nxtDAG", self.get_pid())
        ))
        return "ControllerTEProc"
    
    def ControllerTERemoveUnnecessaryIRs(self, local_provider):
        local_provider.set_value(
            self.get_pid(),
            "nxtDAG",
            operators.CreateTEDAG(self, local_provider.get_value("setRemovableIRs", self.get_pid()), local_provider.get_value("nxtDAG", self.get_pid(), ["dag"])),
            ["dag"]
        )
        macros.unscheduleDagIRs(self, local_provider, local_provider.get_value("nxtDAG", self.get_pid(), ["dag", "v"]))
        return "ControllerTESubmitNewDAG"
    
    def ControllerTEWaitForStaleDAGToBeRemoved(self, local_provider):
        self.global_provider.wait(self.get_pid(), self._cvs[0], lambda _provider: _provider.get_value("DAGState", self.get_pid(), [local_provider.get_value("prev_dag_id", self.get_pid())]) == EnumDAGState.DAG_NONE)
        local_provider.set_value(
            self.get_pid(),
            "prev_dag_id",
            local_provider.get_value("DAGID", self.get_pid())
        )
        local_provider.set_value(
            self.get_pid(),
            "setRemovableIRs",
            operators.getSetRemovableIRs(self, self.input_provider.get_value("SW", self.get_pid()).difference(local_provider.get_value("currSetDownSw", self.get_pid())), local_provider.get_value("nxtDAGVertices", self.get_pid()))
        )
        return "ControllerTERemoveUnnecessaryIRs"
    

