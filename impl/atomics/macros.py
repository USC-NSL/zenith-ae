from atomics.common import *
import atomics.operators as operators


"""
Contains the definitions for PlusCal macros (i.e the `macro` block of the PlusCal
algorithm). Macros can write to process/global variables, as such they receive both
the caller reference as well as a `ValueProvider` instance to manipulate local variables.
"""

def controllerSendIR(self, local_provider, irObject):
    if (operators.isClearIR(self, irObject["IR"])):
        self.global_provider.fanout_fifo_put(self.get_pid(), "controller2Switch", irObject["sw"], MessageOpenFlowCMD(
            type=EnumOpenFlowCMD.CLEAR_TCAM,
            flow=0,
            to=irObject["sw"],
            source=self.get_mid()
        ))
        
        
    else:
        self.global_provider.fanout_fifo_put(self.get_pid(), "controller2Switch", irObject["sw"], MessageOpenFlowCMD(
            type=operators.getIRType(self, irObject["IR"]),
            flow=operators.getPrimaryOfIR(self, irObject["IR"]),
            to=irObject["sw"],
            source=self.get_mid()
        ))
        
        
    

def getNextDAGID(self, local_provider):
    if (local_provider.get_value("DAGID", self.get_pid()) == None):
        local_provider.set_value(
            self.get_pid(),
            "DAGID",
            1 # NO_GEN
            # NadirUID(1)
        )
        
        
    else:
        local_provider.set_value(
            self.get_pid(),
            "DAGID",
            local_provider.get_value("DAGID", self.get_pid()) % self.input_provider.get_value("MaxDAGID", self.get_pid()) + 1 # NO_GEN
            # (self.global_provider.uid_as_int(local_provider.get_value("DAGID", self.get_pid())) % self.input_provider.get_value("MaxDAGID", self.get_pid())) + 1
        )
        
        
    

def unscheduleDagIRs(self, local_provider, dagIRSet):
    self.global_provider.set_value(
        self.get_pid(),
        "SetScheduledIRs",
        {x: (self.global_provider.get_value("SetScheduledIRs", self.get_pid(), [x]).difference(operators.getSetUnschedulableIRs(self, dagIRSet))) for x in iter(self.input_provider.get_value("SW", self.get_pid()))}
    )
    

def setNIBIRState(self, local_provider, irID, state):
    if ((operators.isPrimary(self, irID))):
        if (state == EnumIRState.IR_DONE and \
        self.global_provider.get_value("NIBIRStatus", self.get_pid(), [irID, "dual"]) == EnumIRState.IR_DONE):
            self.global_provider.set_value(
                self.get_pid(),
                "NIBIRStatus",
                StructIRPair(
                    primary=EnumIRState.IR_DONE,
                    dual=EnumIRState.IR_NONE
                ),
                [irID]
            )
            
            
        else:
            self.global_provider.set_value(
                self.get_pid(),
                "NIBIRStatus",
                state,
                [irID, "primary"]
            )
            
            
        
        
    else:
        _primaryIR3 = operators.getPrimaryOfIR(self, irID)
        
        if (state == EnumIRState.IR_DONE and \
        self.global_provider.get_value("NIBIRStatus", self.get_pid(), [_primaryIR3, "primary"]) == EnumIRState.IR_DONE):
            self.global_provider.set_value(
                self.get_pid(),
                "NIBIRStatus",
                StructIRPair(
                    primary=EnumIRState.IR_NONE,
                    dual=EnumIRState.IR_DONE
                ),
                [_primaryIR3]
            )
            
            
        else:
            self.global_provider.set_value(
                self.get_pid(),
                "NIBIRStatus",
                state,
                [_primaryIR3, "dual"]
            )
            
            
        
        
        
        
    

def setRCIRState(self, local_provider, irID, state):
    if ((operators.isPrimary(self, irID))):
        if (state == EnumIRState.IR_DONE and \
        self.global_provider.get_value("RCIRStatus", self.get_pid(), [irID, "dual"]) == EnumIRState.IR_DONE):
            self.global_provider.set_value(
                self.get_pid(),
                "RCIRStatus",
                StructIRPair(
                    primary=EnumIRState.IR_DONE,
                    dual=EnumIRState.IR_NONE
                ),
                [irID]
            )
            
            
        else:
            self.global_provider.set_value(
                self.get_pid(),
                "RCIRStatus",
                state,
                [irID, "primary"]
            )
            
            
        
        
    else:
        _primaryIR4 = operators.getPrimaryOfIR(self, irID)
        
        if (state == EnumIRState.IR_DONE and \
        self.global_provider.get_value("RCIRStatus", self.get_pid(), [_primaryIR4, "primary"]) == EnumIRState.IR_DONE):
            self.global_provider.set_value(
                self.get_pid(),
                "RCIRStatus",
                StructIRPair(
                    primary=EnumIRState.IR_NONE,
                    dual=EnumIRState.IR_DONE
                ),
                [_primaryIR4]
            )
            
            
        else:
            self.global_provider.set_value(
                self.get_pid(),
                "RCIRStatus",
                state,
                [_primaryIR4, "dual"]
            )
            
            
        
        
        
        
    



"""
NOT GENERATED!
"""


def controllerSendDirectedReconciliation(self, local_provider, to):
    self.global_provider.fanout_fifo_put(self.get_pid(), "controller2Switch", to, MessageOpenFlowCMD(
        type=EnumOpenFlowCMD.FLOW_STAT_REQUEST,
        flow=0,
        to=to,
        source=self.get_mid()
    ))