
"""
Users can change the implementation of an operator or a macro. These are atomic steps
of the PlusCal algorithm, thus as long as the user can provide assurance that their will
produce the same result for each input (e.g. with fuzz-testing), then there is no danger
of race conditions and these implementation changes are safe.
We call these things `patches`, and they can be freely swapped during runtime.
"""

from atomics.common import *
import atomics.operators


def getDualOfIR_patched(self, ir):
    if (self.global_provider.uid_as_int(ir) <= self.input_provider.get_value("MaxNumIRs", self.get_pid())):
        return self.global_provider.int_as_uid('irs', self.global_provider.uid_as_int(ir) + self.input_provider.get_value("MaxNumIRs", self.get_pid()))
    else:
        return self.global_provider.int_as_uid('irs', self.global_provider.uid_as_int(ir) - self.input_provider.get_value("MaxNumIRs", self.get_pid()))


def getPrimaryOfIR_patched(self, ir):
    if (self.global_provider.uid_as_int(ir) <= self.input_provider.get_value("MaxNumIRs", self.get_pid())):
        return ir
    else:
        return self.global_provider.int_as_uid('irs', self.global_provider.uid_as_int(ir) - self.input_provider.get_value("MaxNumIRs", self.get_pid()))


def getIRIDForFlow_patched(self, flowID, irType):
    if (irType == EnumOpenFlowACK.INSTALLED_SUCCESSFULLY):
        return flowID
    else:
        return self.global_provider.int_as_uid('irs', self.global_provider.uid_as_int(flowID) + self.input_provider.get_value("MaxNumIRs", self.get_pid()))


def _getNIBIRState(self, irID, NIBIRState):
    if (atomics.operators.isPrimary(self, irID)):
        return NIBIRState[irID]["primary"]
    else:
        return NIBIRState[atomics.operators.getPrimaryOfIR(self, irID)]["dual"]


def _getRCIRState(self, irID, RCIRStatus):
    if (atomics.operators.isPrimary(self, irID)):
        return RCIRStatus[irID]["primary"]
    else:
        return RCIRStatus[atomics.operators.getPrimaryOfIR(self, irID)]["dual"]


def getSetRemovableIRs_patched(self, swSet, nxtDAGV):
    ScheduledIRs = self.global_provider.get_value("ScheduledIRs", self.get_pid())
    RCIRStatus = self.global_provider.get_value("RCIRStatus", self.get_pid())
    return {(x) for x in self.global_provider.get_uid_iterator('irs', 1, self.input_provider.get_value("MaxNumIRs", self.get_pid())) if all([
        any([
            _getRCIRState(self, x, RCIRStatus) != EnumIRState.IR_NONE,
            ScheduledIRs[x]
        ]),
        x not in nxtDAGV,
        atomics.operators.getSwitchForIR(self, x) in swSet
    ])}


def getIRSetToReset_patched(self, SID):
    NIBIRStatus = self.global_provider.get_value("NIBIRStatus", self.get_pid())
    return {(x) for x in self.global_provider.get_uid_iterator('irs', 1, self.input_provider.get_value("MaxNumIRs", self.get_pid())) if all([
        atomics.operators.getSwitchForIR(self, x) == SID,
        _getNIBIRState(self, x, NIBIRStatus) != EnumIRState.IR_NONE
    ])}


def _allIRsInDAGInstalled(self, DAG, RCIRStatus):
    return not any(
        _getRCIRState(self, y, RCIRStatus) != EnumIRState.IR_DONE
        for y in iter(DAG["v"])
    )


def _allIRsInDAGAreStable(self, DAG, RCIRStatus, ScheduledIRs):
    for y in DAG["v"]:
        is_done = _getRCIRState(self, y, RCIRStatus) == EnumIRState.IR_DONE
        dual_is_not_none = (_getRCIRState(self, getDualOfIR_patched(self, y), RCIRStatus) != EnumIRState.IR_NONE)
        dual_is_scheduled = ScheduledIRs[getDualOfIR_patched(self, y)]
        has_inflight_dual = any([dual_is_not_none, dual_is_scheduled])
        if all([is_done, has_inflight_dual]):
            if atomics.operators.isPrimary(self, y):
                TitledLog.info("sched", f"====> Primary {y} is not stable: IS_DONE={is_done} | DUAL_IS_NOT_NONE={dual_is_not_none} | DUAL_IS_SCHEDULED={dual_is_scheduled}")
            else:
                TitledLog.info("sched", f"====> Dual {y} is not stable: IS_DONE={is_done} | DUAL_IS_NOT_NONE={dual_is_not_none} | DUAL_IS_SCHEDULED={dual_is_scheduled}")
            return False
    return True


def dagObjectShouldBeProcessed_patched(self, dagObject):
    RCIRStatus = self.global_provider.get_value("RCIRStatus", self.get_pid())
    ScheduledIRs = self.global_provider.get_value("ScheduledIRs", self.get_pid())
    not_all_installed = not _allIRsInDAGInstalled(self, dagObject["dag"], RCIRStatus)
    not_stale = not atomics.operators.isDAGStale(self, dagObject["id"])
    not_stable = not _allIRsInDAGAreStable(self, dagObject["dag"], RCIRStatus, ScheduledIRs)
    return any([all([not_all_installed, not_stale]), not_stable])


def _isDependencySatisfied(self, DAG, ir, RCIRStatus):
    ancestors = DAG.get_ancestors(ir)
    return not any(
        all([
            (y, ir) in DAG["e"],
            _getRCIRState(self, y, RCIRStatus) != EnumIRState.IR_DONE
        ])
        for y in ancestors
    )


def getSetIRsCanBeScheduledNext_patched(self, DAG):
    RCIRStatus = self.global_provider.get_value("RCIRStatus", self.get_pid())
    ScheduledIRs = self.global_provider.get_value("ScheduledIRs", self.get_pid())
    RCSwSuspensionStatus = self.global_provider.get_value("RCSwSuspensionStatus", self.get_pid())
    return {(x) for x in iter(DAG["v"]) if all([
        _getRCIRState(self, x, RCIRStatus) == EnumIRState.IR_NONE,
        _isDependencySatisfied(self, DAG, x, RCIRStatus),
        RCSwSuspensionStatus[atomics.operators.getSwitchForIR(self, x)] == EnumSwitchState.SW_RUN,
        not ScheduledIRs[x]
    ])}


def existsMonitoringEventHigherNum_patched(self, monEvent):
    events = self.global_provider.get_value("swSeqChangedStatus", self.get_pid())
    return any(
        all([
            event["swID"] == monEvent["swID"],
            event["num"] > monEvent["num"],
            event["type"] != MODEL_VALUES.CLEARED_TCAM_SUCCESSFULLY
        ])
        for event in events
    )


def setNIBIRState(self, local_provider, irID, state):
    if ((atomics.operators.isPrimary(self, irID))):
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
        _primaryIR3 = atomics.operators.getPrimaryOfIR(self, irID)
        
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
    if ((atomics.operators.isPrimary(self, irID))):
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
        _primaryIR4 = atomics.operators.getPrimaryOfIR(self, irID)
        
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
from pynadir.utils.logging import TitledLog

def unscheduleDagIRs_patched(self, local_provider, dagIRSet):
    RCIRStatus = self.global_provider.get_value("RCIRStatus", self.get_pid())
    for x in dagIRSet:
        if (_getRCIRState(self, x, RCIRStatus) != EnumIRState.IR_NONE):
            self.global_provider.set_value(
                self.get_pid(),
                "ScheduledIRs",
                False,
                [x]
            )
            # TitledLog.info("sched", f"^^^^^^ Unscheduling: {x}")


def AddDeleteDAGIRDoneSet_patched(self, irSet, doneSet):
    cp = set(doneSet)
    for ir in irSet:
        if (atomics.operators.getIRType(self, ir) == EnumOpenFlowCMD.INSTALL_FLOW):
            cp.add(ir)
        else:
            cp.discard(ir)
    return cp
