from atomics.common import *


"""
Contains the definitions for TLA operators (i.e the `define` block of the PlusCal
algorithm). Operators always receive the caller `NadirProcess` object as their first
argument, however, we decided not to implement that as methods to make them easier to patch.
"""

def isPrimary(self, ir):
    if (self.global_provider.uid_as_int(ir) <= self.input_provider.get_value("MaxNumIRs", self.get_pid())):
        return True
    else:
        return False
    

def getDualOfIR(self, ir):
    if (self.global_provider.uid_as_int(ir) <= self.input_provider.get_value("MaxNumIRs", self.get_pid())):
        return self.global_provider.int_as_uid(self.global_provider.uid_as_int(ir) + self.input_provider.get_value("MaxNumIRs", self.get_pid()))
    else:
        return self.global_provider.int_as_uid(self.global_provider.uid_as_int(ir) - self.input_provider.get_value("MaxNumIRs", self.get_pid()))
    

def getPrimaryOfIR(self, ir):
    if (self.global_provider.uid_as_int(ir) <= self.input_provider.get_value("MaxNumIRs", self.get_pid())):
        return ir
    else:
        return self.global_provider.int_as_uid(self.global_provider.uid_as_int(ir) - self.input_provider.get_value("MaxNumIRs", self.get_pid()))
    

def getSwitchForIR(self, ir):
    return self.input_provider.get_value("IR2SW", self.get_pid(), [getPrimaryOfIR(self, ir)])

def isClearIR(self, idID):
    if (self.global_provider.uid_as_int(idID) == 0):
        return True
    else:
        return False
    

def getIRType(self, irID):
    if (self.global_provider.uid_as_int(irID) <= self.input_provider.get_value("MaxNumIRs", self.get_pid())):
        return EnumOpenFlowCMD.INSTALL_FLOW
    else:
        return EnumOpenFlowCMD.DELETE_FLOW
    

def getIRIDForFlow(self, flowID, irType):
    if (irType == EnumOpenFlowACK.INSTALLED_SUCCESSFULLY):
        return self.global_provider.int_as_uid(flowID)
    else:
        return self.global_provider.int_as_uid(flowID + self.input_provider.get_value("MaxNumIRs", self.get_pid()))
    

def getNIBIRState(self, irID):
    if (isPrimary(self, irID)):
        return self.global_provider.get_value("NIBIRStatus", self.get_pid(), [irID, "primary"])
    else:
        return self.global_provider.get_value("NIBIRStatus", self.get_pid(), [getPrimaryOfIR(self, irID), "dual"])
    

def getRCIRState(self, irID):
    if (isPrimary(self, irID)):
        return self.global_provider.get_value("RCIRStatus", self.get_pid(), [irID, "primary"])
    else:
        return self.global_provider.get_value("RCIRStatus", self.get_pid(), [getPrimaryOfIR(self, irID), "dual"])
    

def getSetUnschedulableIRs(self, nxtDAGV):
    return {(x) for x in iter(nxtDAGV) if getRCIRState(self, x) != EnumIRState.IR_NONE}

def getSetRemovableIRs(self, swSet, nxtDAGV):
    return {(x) for x in iter(self.global_provider.int_set_as_uid_set(range(self.input_provider.get_value("MaxNumIRs", self.get_pid()), 1 + 1))) if all([
        any([
            getRCIRState(self, x) != EnumIRState.IR_NONE,
            self.global_provider.get_value("ScheduledIRs", self.get_pid(), [x])
        ]),
        x not in nxtDAGV,
        getSwitchForIR(self, x) in swSet
    ])}

def getSetIRsForSwitchInDAG(self, swID, nxtDAGV):
    return {(x) for x in iter(nxtDAGV) if getSwitchForIR(self, x) == swID}

def isDependencySatisfied(self, DAG, ir):
    return not any(
        all([
            (y, ir) in DAG["e"],
            getRCIRState(self, y) != EnumIRState.IR_DONE
        ])
        for y in iter(DAG["v"])
    )

def getSetIRsCanBeScheduledNext(self, DAG):
    return {(x) for x in iter(DAG["v"]) if all([
        getRCIRState(self, x) == EnumIRState.IR_NONE,
        isDependencySatisfied(self, DAG, x),
        self.global_provider.get_value("RCSwSuspensionStatus", self.get_pid(), [getSwitchForIR(self, x)]) == EnumSwitchState.SW_RUN,
        not self.global_provider.get_value("ScheduledIRs", self.get_pid(), [x])
    ])}

def allIRsInDAGInstalled(self, DAG):
    return not any(
        getRCIRState(self, y) != EnumIRState.IR_DONE
        for y in iter(DAG["v"])
    )

def isDAGStale(self, id):
    return self.global_provider.get_value("DAGState", self.get_pid(), [id]) != EnumDAGState.DAG_SUBMIT

def isSwitchSuspended(self, sw):
    return self.global_provider.get_value("SwSuspensionStatus", self.get_pid(), [sw]) == EnumSwitchState.SW_SUSPEND

def existsMonitoringEventHigherNum(self, monEvent):
    return any(
        all([
            self.global_provider.get_value("swSeqChangedStatus", self.get_pid(), [x, "swID"]) == monEvent["swID"],
            self.global_provider.get_value("swSeqChangedStatus", self.get_pid(), [x, "num"]) > monEvent["num"],
            self.global_provider.get_value("swSeqChangedStatus", self.get_pid(), [x, "type"]) != MODEL_VALUES.CLEARED_TCAM_SUCCESSFULLY
        ])
        for x in iter(list(range(len(self.global_provider.get_value("swSeqChangedStatus", self.get_pid())))))
    )

def shouldSuspendRunningSw(self, monEvent):
    return all([
        any([
            monEvent["type"] == MODEL_VALUES.OFA_DOWN,
            monEvent["type"] == MODEL_VALUES.NIC_ASIC_DOWN,
            all([
                monEvent["type"] == MODEL_VALUES.KEEP_ALIVE,
                monEvent["installerStatus"] == EnumInstallerStatus.INSTALLER_DOWN
            ])
        ]),
        any([
            self.global_provider.get_value("eventHandlerCheckpoint", self.get_pid()) == True,
            self.global_provider.get_value("SwSuspensionStatus", self.get_pid(), [monEvent["swID"]]) == EnumSwitchState.SW_RUN
        ])
    ])

def shouldClearSuspendedSw(self, monEvent):
    return all([
        monEvent["type"] == MODEL_VALUES.KEEP_ALIVE,
        monEvent["installerStatus"] == EnumInstallerStatus.INSTALLER_UP,
        self.global_provider.get_value("SwSuspensionStatus", self.get_pid(), [monEvent["swID"]]) == EnumSwitchState.SW_SUSPEND
    ])

def shouldFreeSuspendedSw(self, monEvent):
    return all([
        monEvent["type"] == MODEL_VALUES.CLEARED_TCAM_SUCCESSFULLY,
        monEvent["installerStatus"] == EnumInstallerStatus.INSTALLER_UP,
        any([
            self.global_provider.get_value("SwSuspensionStatus", self.get_pid(), [monEvent["swID"]]) == EnumSwitchState.SW_SUSPEND,
            self.global_provider.get_value("eventHandlerCheckpoint", self.get_pid()) == True
        ])
    ])

def getIRSetToReset(self, SID):
    return {(x) for x in iter(self.global_provider.int_set_as_uid_set(range(self.input_provider.get_value("MaxNumIRs", self.get_pid()), 1 + 1))) if all([
        getSwitchForIR(self, x) == SID,
        getNIBIRState(self, x) != EnumIRState.IR_NONE
    ])}

def isFinished(self):
    return all(
        getNIBIRState(self, x) == EnumIRState.IR_DONE
        for x in iter(self.global_provider.int_set_as_uid_set(range(self.input_provider.get_value("MaxNumIRs", self.get_pid()), 1 + 1)))
    )

def allIRsInDAGAreStable(self, DAG):
    return not any(
        all([
            getRCIRState(self, y) == EnumIRState.IR_DONE,
            any([
                getRCIRState(self, getDualOfIR(self, y)) != EnumIRState.IR_NONE,
                self.global_provider.get_value("ScheduledIRs", self.get_pid(), [getDualOfIR(self, y)])
            ])
        ])
        for y in iter(DAG["v"])
    )

def dagObjectShouldBeProcessed(self, dagObject):
    return any([
        all([
            not allIRsInDAGInstalled(self, dagObject["dag"]),
            not isDAGStale(self, dagObject["id"])
        ]),
        not allIRsInDAGAreStable(self, dagObject["dag"])
    ])

def AddDeleteDAGIRDoneSet(self, irSet, doneSet):
    if (len(irSet) == 0):
        return doneSet
    else:
        _pickedIR0 = conditional_choose(iter(irSet), lambda x: True)
        if (getIRType(self, _pickedIR0) == EnumOpenFlowCMD.INSTALL_FLOW):
            return AddDeleteDAGIRDoneSet(self, irSet.difference({_pickedIR0}), doneSet.union({_pickedIR0}))
        else:
            return AddDeleteDAGIRDoneSet(self, irSet.difference({_pickedIR0}), doneSet.difference({_pickedIR0}))
        
        
    

def GetDependencyEdges(self, irToRemove, irsToConnect, edges):
    if (len(irsToConnect) == 0):
        return edges
    else:
        _irToConnect1 = conditional_choose(iter(irsToConnect), lambda x: True)
        return GetDependencyEdges(self, irToRemove, irsToConnect.difference({_irToConnect1}), edges.union({(getDualOfIR(self, irToRemove), "irToConnect")}))
        
    

def CreateTEDAG(self, irsToRemove, dag):
    if (len(irsToRemove) == 0):
        return dag
    else:
        _irToRemove2 = conditional_choose(iter(irsToRemove), lambda x: True)
        return CreateTEDAG(self, irsToRemove.difference({_irToRemove2}), StructRCDAG(
            v=(dag["v"].union({getDualOfIR(self, _irToRemove2)})),
            e=GetDependencyEdges(self, _irToRemove2, getSetIRsForSwitchInDAG(self, getSwitchForIR(self, _irToRemove2), dag["v"]), dag["e"])
        ))
        
    


"""NON-GENERATED BEGIN"""
import time
from pynadir.utils.logging import TitledLog


def getInstallIRsOfDAG(self, dagObject):
    return frozenset({x for x in dagObject["dag"]["v"] if getIRType(self, x) == EnumOpenFlowCMD.INSTALL_FLOW})


def recordDAGStart(self, dagObject):
    dagObject["dag"].make_graph()
    key = hash(getInstallIRsOfDAG(self, dagObject))
    if not hasattr(self, 'ct_dict'):
        setattr(self, 'ct_dict', dict())
        setattr(self, 'last_ct_dict', dict())
    if key not in self.ct_dict:
        # Fresh DAG!
        TitledLog.special_info("zenith", f"New DAG {hex(key)[-3:]} was given to RC")
        self.ct_dict[key] = time.time()
    else:
        if not hasattr(self, 'previous_key'):
            setattr(self, 'previous_key', key)
        if key == self.previous_key:
            # This is the same DAG still being processed
            TitledLog.special_info("zenith", f"A DAG {hex(key)[-3:]} has been redundantly scheduled")
            pass
        else:
            # New!
            TitledLog.warning("zenith", f"DAG switch from {hex(self.previous_key)[-3:]} to {hex(key)[-3:]}")
            self.ct_dict[key] = time.time()
    self.previous_key = key
    setattr(self, 'eventful', False)


def recordDAGFinish(self, is_stale):
    assert hasattr(self, 'previous_key')
    assert hasattr(self, 'ct_dict')
    if self.eventful:
        last_ct = self.last_ct_dict.get(self.previous_key)
        if last_ct is not None:
            start = max(self.ct_dict[self.previous_key], last_ct)
        else:
            start = self.ct_dict[self.previous_key]
        now = time.time()
        ct = float(round(now - start, 2))
        if not is_stale:
            TitledLog.success("zenith", f"Converged on DAG {hex(self.previous_key)[-3:]} in {str(ct)} seconds")
        else:
            TitledLog.info("zenith", f"DAG {hex(self.previous_key)[-3:]} became stale after {str(ct)} seconds")
        if not hasattr(self, 'ct_list'):
            self.ct_list = []
        self.ct_list.append(ct)
        self.last_ct_dict[self.previous_key] = now
        self.eventful = False
    else:
        TitledLog.info("zenith", "DAG was uneventful. Ignoring.")


def markDAGAsEventful(self):
    setattr(self, 'eventful', True)


def getDonesAndNones(self, irIDs) -> Tuple[Set[int], Set[int]]:
    irIDDocs = [from_nadir_type(irID) for irID in irIDs]
    states = list(self.global_provider.value_provider.query_document("NIBIRStatus", filter={"key": {"$in": irIDDocs}}))
    nones = [as_nadir_type(doc["key"]) for doc in states if doc["value"]["primary"] == "IR_NONE"]
    dones = [as_nadir_type(doc["key"]) for doc in states if doc["value"]["primary"] == "IR_DONE"]
    return set(dones), set(nones)


def getReconciledDAG(self):
    downed = frozenset({
        as_nadir_type(doc['key']) for doc in \
        self.global_provider.value_provider.query_document("SwSuspensionStatus", filter={"value.value": "SW_DOWN"})
    })
    return self.input_provider.get_value("TOPO_DAG_MAPPING", self.get_pid(), [downed])
"""NON-GENERATED END"""