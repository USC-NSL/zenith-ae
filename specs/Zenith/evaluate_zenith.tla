---------------------------- MODULE evaluate_zenith ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, eval_constants, switch_constants, nib_constants, dag, NadirTypes, NadirAckQueue

CONSTANTS ofc0, rc0
CONSTANTS CONTROLLER_THREAD_POOL, CONT_WORKER_SEQ, CONT_BOSS_SEQ, CONT_MONITOR, CONT_EVENT, 
          NIB_EVENT_HANDLER, CONT_TE
CONSTANTS TOPO_DAG_MAPPING, IR2SW, FINAL_DAG, SW_THREAD_SHARD_MAP

CONSTANTS OFCProcSet

(* Lock for switch and controller for optimization, shared between the two *)
VARIABLES switchLock, controllerLock

(* Shared queues between Zenith and the switch *)
VARIABLES controller2Switch, switch2Controller

(* This is a hidden variable of switch specification, which we will expose. *)
VARIABLES installedIRs

(* These are hidden variables of Zenith specification, which we will expose. *)
VARIABLES NIBIRStatus, FirstInstall

(* PlusCal program counter, shared between the two modules *)
VARIABLES pc

(* Internal variables, we'll not bother hiding them, since there is quite a few of them *)

\* For switch
VARIABLES sw_fail_ordering_var, 
          switchStatus, TCAM, controlMsgCounter, RecoveryStatus,
          ingressPkt, statusMsg, obj, statusResolveMsg,
          \* Specifically for complex switch model
          NicAsic2OfaBuff, Ofa2NicAsicBuff, Installer2OfaBuff, Ofa2InstallerBuff,
          ingressIR, egressMsg, ofaInMsg, ofaOutConfirmation, 
          installerInIR, notFailedSet, failedElem, failedSet, 
          recoveredElem


\* For zenith
VARIABLES TEEventQueue, DAGEventQueue, DAGQueue, 
          IRQueueNIB, RCNIBEventQueue, 
          DAGState, RCIRStatus, 
          RCSwSuspensionStatus, SwSuspensionStatus, 
          ScheduledIRs, 
          IRDoneSet, seqWorkerIsBusy,
          event, topoChangeEvent, currSetDownSw, 
          prev_dag_id, init, DAGID, nxtDAG, setRemovableIRs, 
          nxtDAGVertices,  
          seqEvent, toBeScheduledIRs, nextIR,
          currDAG, index,
          monitoringEvent, setIRsToReset, 
          resetIR, msg, irID, 
          nextIRObjectToSend,
          swSeqChangedStatus,

          eventHandlerCheckpoint,
          eventHandlerLastIRToReset,
          eventHandlerTCAMCleared,

          ofcSubmoduleFailNum,
          stepOfFailureWP, stepOfFailureEH, stepOfFailureMS,

          irsToUnschedule, unschedule


(* Each time either of the switches OR Zenith take a step, these CAN change *)
shared_vars == <<
    switchLock, controllerLock,
    controller2Switch, switch2Controller,
    pc
>>

(* Each time Zenith takes a step, these remain unchanged *)
internal_switch_vars == <<
    sw_fail_ordering_var, 
    switchStatus, installedIRs, TCAM, controlMsgCounter, RecoveryStatus,
    ingressPkt, statusMsg, obj, statusResolveMsg,
    NicAsic2OfaBuff, Ofa2NicAsicBuff, Installer2OfaBuff, Ofa2InstallerBuff,
    ingressIR, egressMsg, ofaInMsg, ofaOutConfirmation, 
    installerInIR, notFailedSet, failedElem, failedSet, 
    recoveredElem
>>

(* Each time a switch takes a step, these remain unchanged *)
internal_zenith_vars == <<
    TEEventQueue, DAGEventQueue, DAGQueue, 
    IRQueueNIB, RCNIBEventQueue, 
    DAGState, RCIRStatus, NIBIRStatus, FirstInstall,
    RCSwSuspensionStatus, SwSuspensionStatus, 
    ScheduledIRs, 
    IRDoneSet, seqWorkerIsBusy,
    event, topoChangeEvent, currSetDownSw, 
    prev_dag_id, init, DAGID, nxtDAG, setRemovableIRs, 
    nxtDAGVertices, 
    seqEvent, toBeScheduledIRs, nextIR,
    currDAG, index,
    monitoringEvent, setIRsToReset, 
    resetIR, msg, irID, 
    nextIRObjectToSend,
    swSeqChangedStatus,

    eventHandlerCheckpoint,
    eventHandlerLastIRToReset,
    eventHandlerTCAMCleared,

    ofcSubmoduleFailNum,
    stepOfFailureWP, stepOfFailureEH, stepOfFailureMS,

    irsToUnschedule, unschedule
>>

(* Any one of these variables can stutter ... *)
vars == <<
    switchLock, controllerLock,
    controller2Switch, switch2Controller, pc,
    sw_fail_ordering_var, 
    switchStatus, installedIRs, TCAM, controlMsgCounter, RecoveryStatus,
    ingressPkt, statusMsg, obj, statusResolveMsg,
    NicAsic2OfaBuff, Ofa2NicAsicBuff, Installer2OfaBuff, Ofa2InstallerBuff,
    ingressIR, egressMsg, ofaInMsg, ofaOutConfirmation, 
    installerInIR, notFailedSet, failedElem, failedSet, 
    recoveredElem,
    TEEventQueue, DAGEventQueue, DAGQueue, 
    IRQueueNIB, RCNIBEventQueue, 
    DAGState, RCIRStatus, NIBIRStatus, FirstInstall,
    RCSwSuspensionStatus, SwSuspensionStatus, 
    ScheduledIRs, 
    IRDoneSet, seqWorkerIsBusy,
    event, topoChangeEvent, currSetDownSw, 
    prev_dag_id, init, DAGID, nxtDAG, setRemovableIRs, 
    nxtDAGVertices, 
    seqEvent, toBeScheduledIRs, nextIR,
    currDAG, index,
    monitoringEvent, setIRsToReset, 
    resetIR, msg, irID, 
    nextIRObjectToSend,
    swSeqChangedStatus,
    eventHandlerCheckpoint,
    eventHandlerLastIRToReset,
    eventHandlerTCAMCleared,
    ofcSubmoduleFailNum, 
    stepOfFailureWP, stepOfFailureEH, stepOfFailureMS,
    irsToUnschedule, unschedule
>>

(* All of our processes *)
ProcSet == 
    (* Switches *)
    (({SW_SIMPLE_ID} \X SW)) \cup 
    (({NIC_ASIC_IN} \X SW)) \cup 
    (({NIC_ASIC_OUT} \X SW)) \cup 
    (({OFA_IN} \X SW)) \cup 
    (({OFA_OUT} \X SW)) \cup 
    (({INSTALLER} \X SW)) \cup 
    (({SW_FAILURE_PROC} \X SW)) \cup 
    (({SW_RESOLVE_PROC} \X SW)) \cup 
    (({GHOST_UNLOCK_PROC} \X SW)) \cup 

    (* Zenith *)
    (({rc0} \X {NIB_EVENT_HANDLER})) \cup (({rc0} \X {CONT_TE})) \cup 
    (({rc0} \X {CONT_BOSS_SEQ})) \cup (({rc0} \X {CONT_WORKER_SEQ})) \cup 
    (({ofc0} \X CONTROLLER_THREAD_POOL)) \cup (({ofc0} \X {CONT_EVENT})) \cup 
    (({ofc0} \X {CONT_MONITOR}))

Init == (* Locks *)
        /\ switchLock = <<NO_LOCK, NO_LOCK>>
        /\ controllerLock = <<NO_LOCK, NO_LOCK>>
        (* Shared queues *)
        /\ swSeqChangedStatus = <<>>
        /\ controller2Switch = [x \in SW |-> <<>>]
        /\ switch2Controller = <<>>
        (* Exposed Zenith variables *)
        /\ FirstInstall = [x \in 1..2*MaxNumIRs |-> 0]
        /\ NIBIRStatus = [x \in 1..MaxNumIRs |-> [primary |-> IR_NONE, dual |-> IR_NONE]]
        (* Hidden Zenith variables *)
        /\ TEEventQueue = <<>>
        /\ DAGEventQueue = <<>>
        /\ DAGQueue = <<>>
        /\ IRQueueNIB = <<>>
        /\ RCNIBEventQueue = <<>>
        /\ DAGState = [x \in 1..MaxDAGID |-> DAG_NONE]
        /\ RCIRStatus = [y \in 1..MaxNumIRs |-> [primary |-> IR_NONE, dual |-> IR_NONE]]
        /\ RCSwSuspensionStatus = [y \in SW |-> SW_RUN]
        /\ SwSuspensionStatus = [x \in SW |-> SW_RUN]
        /\ ScheduledIRs = [x \in 1..2*MaxNumIRs |-> FALSE]
        /\ ofcSubmoduleFailNum = [x \in OFCProcSet |-> 0]
        /\ seqWorkerIsBusy = FALSE
        /\ eventHandlerCheckpoint = FALSE
        /\ eventHandlerTCAMCleared = FALSE
        /\ eventHandlerLastIRToReset = NADIR_NULL
        (* Process rcNibEventHandler *)
        /\ event = [self \in ({rc0} \X {NIB_EVENT_HANDLER}) |-> NADIR_NULL]
        (* Process controllerTrafficEngineering *)
        /\ topoChangeEvent = [self \in ({rc0} \X {CONT_TE}) |-> NADIR_NULL]
        /\ currSetDownSw = [self \in ({rc0} \X {CONT_TE}) |-> {}]
        /\ prev_dag_id = [self \in ({rc0} \X {CONT_TE}) |-> NADIR_NULL]
        /\ init = [self \in ({rc0} \X {CONT_TE}) |-> TRUE]
        /\ DAGID = [self \in ({rc0} \X {CONT_TE}) |-> NADIR_NULL]
        /\ nxtDAG = [self \in ({rc0} \X {CONT_TE}) |-> NADIR_NULL]
        /\ nxtDAGVertices = [self \in ({rc0} \X {CONT_TE}) |-> {}]
        /\ setRemovableIRs = [self \in ({rc0} \X {CONT_TE}) |-> {}]
        /\ irsToUnschedule = [self \in ({rc0} \X {CONT_TE}) |-> {}]
        /\ unschedule = [self \in ({rc0} \X {CONT_TE}) |-> NADIR_NULL]
        (* Process controllerBossSequencer *)
        /\ seqEvent = [self \in ({rc0} \X {CONT_BOSS_SEQ}) |-> NADIR_NULL]
        (* Process controllerSequencer *)
        /\ toBeScheduledIRs = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> {}]
        /\ nextIR = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> NADIR_NULL]
        /\ currDAG = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> NADIR_NULL]
        /\ IRDoneSet = [self \in ({rc0} \X {CONT_WORKER_SEQ}) |-> {}]
        (* Process controllerWorkerThreads *)
        /\ nextIRObjectToSend = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> NADIR_NULL]
        /\ index = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> 0]
        /\ stepOfFailureWP = [self \in ({ofc0} \X CONTROLLER_THREAD_POOL) |-> 0]
        (* Process controllerEventHandler *)
        /\ monitoringEvent = [self \in ({ofc0} \X {CONT_EVENT}) |-> NADIR_NULL]
        /\ setIRsToReset = [self \in ({ofc0} \X {CONT_EVENT}) |-> {}]
        /\ resetIR = [self \in ({ofc0} \X {CONT_EVENT}) |-> NADIR_NULL]
        /\ stepOfFailureEH = [self \in ({ofc0} \X {CONT_EVENT}) |-> 0]
        (* Process controllerMonitoringServer *)
        /\ msg = [self \in ({ofc0} \X {CONT_MONITOR}) |-> NADIR_NULL]
        /\ irID = [self \in ({ofc0} \X {CONT_MONITOR}) |-> NADIR_NULL]
        /\ stepOfFailureMS = [self \in ({ofc0} \X {CONT_MONITOR}) |-> 0]
        (* Exposed switch variables *)
        /\ installedIRs = <<>>
        (* Hidden switch variables *)
        /\ sw_fail_ordering_var = SW_FAIL_ORDERING
        /\ switchStatus =                [
                              x \in SW |-> [
                                  cpu |-> NotFailed,
                                  nicAsic |-> NotFailed,
                                  ofa |-> NotFailed,
                                  installer |-> NotFailed
                              ]
                          ]
        /\ installedIRs = <<>>
        /\ NicAsic2OfaBuff = [x \in SW |-> <<>>]
        /\ Ofa2NicAsicBuff = [x \in SW |-> <<>>]
        /\ Installer2OfaBuff = [x \in SW |-> <<>>]
        /\ Ofa2InstallerBuff = [x \in SW |-> <<>>]
        /\ TCAM = [x \in SW |-> {}]
        /\ controlMsgCounter = [x \in SW |-> 0]
        /\ RecoveryStatus = [x \in SW |-> [transient |-> 0, partial |-> 0]]
        (* Process swProcess *)
        /\ ingressPkt = [self \in ({SW_SIMPLE_ID} \X SW) |-> NADIR_NULL]
        (* Process swNicAsicProcPacketIn *)
        /\ ingressIR = [self \in ({NIC_ASIC_IN} \X SW) |-> NADIR_NULL]
        (* Process swNicAsicProcPacketOut *)
        /\ egressMsg = [self \in ({NIC_ASIC_OUT} \X SW) |-> NADIR_NULL]
        (* Process ofaModuleProcPacketIn *)
        /\ ofaInMsg = [self \in ({OFA_IN} \X SW) |-> NADIR_NULL]
        (* Process ofaModuleProcPacketOut *)
        /\ ofaOutConfirmation = [self \in ({OFA_OUT} \X SW) |-> NADIR_NULL]
        (* Process installerModuleProc *)
        /\ installerInIR = [self \in ({INSTALLER} \X SW) |-> NADIR_NULL]
        (* Process swFailureProc *)
        /\ statusMsg = [self \in ({SW_FAILURE_PROC} \X SW) |-> NADIR_NULL]
        /\ notFailedSet = [self \in ({SW_FAILURE_PROC} \X SW) |-> {}]
        /\ failedElem = [self \in ({SW_FAILURE_PROC} \X SW) |-> NADIR_NULL]
        /\ obj = [self \in ({SW_FAILURE_PROC} \X SW) |-> NADIR_NULL]
        (* Process swResolveFailure *)
        /\ failedSet = [self \in ({SW_RESOLVE_PROC} \X SW) |-> {}]
        /\ statusResolveMsg = [self \in ({SW_RESOLVE_PROC} \X SW) |-> NADIR_NULL]
        /\ recoveredElem = [self \in ({SW_RESOLVE_PROC} \X SW) |-> NADIR_NULL]
        (* Global program counter *)
        /\ pc = [self \in ProcSet |-> CASE self \in ({SW_SIMPLE_ID} \X SW) -> "SwitchSimpleProcess"
                                        [] self \in ({NIC_ASIC_IN} \X SW) -> "SwitchRcvPacket"
                                        [] self \in ({NIC_ASIC_OUT} \X SW) -> "SwitchFromOFAPacket"
                                        [] self \in ({OFA_IN} \X SW) -> "SwitchOfaProcIn"
                                        [] self \in ({OFA_OUT} \X SW) -> "SwitchOfaProcOut"
                                        [] self \in ({INSTALLER} \X SW) -> "SwitchInstallerProc"
                                        [] self \in ({SW_FAILURE_PROC} \X SW) -> "SwitchFailure"
                                        [] self \in ({SW_RESOLVE_PROC} \X SW) -> "SwitchResolveFailure"
                                        [] self \in ({GHOST_UNLOCK_PROC} \X SW) -> "ghostProc"
                                        [] self \in ({rc0} \X {NIB_EVENT_HANDLER}) -> "RCSNIBEventHndlerProc"
                                        [] self \in ({rc0} \X {CONT_TE}) -> "ControllerTEProc"
                                        [] self \in ({rc0} \X {CONT_BOSS_SEQ}) -> "ControllerBossSeqProc"
                                        [] self \in ({rc0} \X {CONT_WORKER_SEQ}) -> "ControllerWorkerSeqProc"
                                        [] self \in ({ofc0} \X CONTROLLER_THREAD_POOL) -> "ControllerThread"
                                        [] self \in ({ofc0} \X {CONT_EVENT}) -> "ControllerEventHandlerProc"
                                        [] self \in ({ofc0} \X {CONT_MONITOR}) -> "ControllerMonitorCheckIfMastr"]

(* Get instances of Zenith and the topology and create the `Next` predicate *)
Switch == INSTANCE switch
Zenith == INSTANCE zenith

SwitchStep == /\ Switch!Next
              /\ UNCHANGED internal_zenith_vars

rcNibEventHandlerStep == /\ (\E self \in ({rc0} \X {NIB_EVENT_HANDLER}): Zenith!rcNibEventHandler(self))
                         /\ UNCHANGED internal_switch_vars
controllerTrafficEngineeringStep == /\ (\E self \in ({rc0} \X {CONT_TE}): Zenith!controllerTrafficEngineering(self))
                                    /\ UNCHANGED internal_switch_vars
controllerBossSequencerStep == /\ (\E self \in ({rc0} \X {CONT_BOSS_SEQ}): Zenith!controllerBossSequencer(self))
                               /\ UNCHANGED internal_switch_vars
controllerSequencerStep == /\ (\E self \in ({rc0} \X {CONT_WORKER_SEQ}): Zenith!controllerSequencer(self))
                           /\ UNCHANGED internal_switch_vars
controllerWorkerThreadsStep == /\ (\E self \in ({ofc0} \X CONTROLLER_THREAD_POOL): Zenith!controllerWorkerThreads(self))
                               /\ UNCHANGED internal_switch_vars
controllerEventHandlerStep == /\ (\E self \in ({ofc0} \X {CONT_EVENT}): Zenith!controllerEventHandler(self))
                              /\ UNCHANGED internal_switch_vars
controllerMonitoringServerStep == /\ (\E self \in ({ofc0} \X {CONT_MONITOR}): Zenith!controllerMonitoringServer(self))
                                  /\ UNCHANGED internal_switch_vars

Next == \/ SwitchStep
        \/ rcNibEventHandlerStep
        \/ controllerTrafficEngineeringStep
        \/ controllerBossSequencerStep
        \/ controllerSequencerStep
        \/ controllerWorkerThreadsStep
        \/ controllerEventHandlerStep
        \/ controllerMonitoringServerStep

(* Evaluation specification *)
Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in ({SW_SIMPLE_ID} \X SW) : WF_internal_switch_vars(Switch!swProcess(self))
        /\ \A self \in ({NIC_ASIC_IN} \X SW) : WF_internal_switch_vars(Switch!swNicAsicProcPacketIn(self))
        /\ \A self \in ({NIC_ASIC_OUT} \X SW) : WF_internal_switch_vars(Switch!swNicAsicProcPacketOut(self))
        /\ \A self \in ({OFA_IN} \X SW) : WF_internal_switch_vars(Switch!ofaModuleProcPacketIn(self))
        /\ \A self \in ({OFA_OUT} \X SW) : WF_internal_switch_vars(Switch!ofaModuleProcPacketOut(self))
        /\ \A self \in ({INSTALLER} \X SW) : WF_internal_switch_vars(Switch!installerModuleProc(self))
        /\ \A self \in ({SW_FAILURE_PROC} \X SW) : WF_internal_switch_vars(Switch!swFailureProc(self))
        /\ \A self \in ({SW_RESOLVE_PROC} \X SW) : WF_internal_switch_vars(Switch!swResolveFailure(self))
        /\ \A self \in ({GHOST_UNLOCK_PROC} \X SW) : WF_internal_switch_vars(Switch!ghostUnlockProcess(self))
        /\ \A self \in ({rc0} \X {NIB_EVENT_HANDLER}) : WF_internal_zenith_vars(Zenith!rcNibEventHandler(self))
        /\ \A self \in ({rc0} \X {CONT_TE}) : WF_internal_zenith_vars(Zenith!controllerTrafficEngineering(self))
        /\ \A self \in ({rc0} \X {CONT_BOSS_SEQ}) : WF_internal_zenith_vars(Zenith!controllerBossSequencer(self))
        /\ \A self \in ({rc0} \X {CONT_WORKER_SEQ}) : WF_internal_zenith_vars(Zenith!controllerSequencer(self))
        /\ \A self \in ({ofc0} \X CONTROLLER_THREAD_POOL) : WF_internal_zenith_vars(Zenith!controllerWorkerThreads(self))
        /\ \A self \in ({ofc0} \X {CONT_EVENT}) : WF_internal_zenith_vars(Zenith!controllerEventHandler(self))
        /\ \A self \in ({ofc0} \X {CONT_MONITOR}) : WF_internal_zenith_vars(Zenith!controllerMonitoringServer(self))
        
\* Liveness Properties
CorrectDAGInstalled == (\A x \in 1..MaxNumIRs: \/ /\ x \in FINAL_DAG.v
                                                  /\ x \in TCAM[Zenith!getSwitchForIR(x)]
                                               \/ /\ x \notin FINAL_DAG.v
                                                  /\ x \notin TCAM[Zenith!getSwitchForIR(x)])
                                                  
CorrectDoneStatusController == (\A x \in 1..MaxNumIRs: \/ NIBIRStatus[x].primary = IR_DONE
                                                       \/ x \notin FINAL_DAG.v)
                                                       
InstallationLivenessProp == <>[] (/\ CorrectDAGInstalled 
                                  /\ CorrectDoneStatusController)
InstallationInvProp == \/ ENABLED Next
                       \/ /\ CorrectDAGInstalled
                          /\ CorrectDoneStatusController
\* Safety Properties
firstHappening(seq, in) == min({x \in DOMAIN seq: seq[x] = in})
whichDAG(ir) == CHOOSE x \in rangeSeq(TOPO_DAG_MAPPING): ir \in x.v

ConsistencyReq == \A x, y \in rangeSeq(installedIRs): \/ x = y
                                                      \/ whichDAG(Zenith!getIRIDForFlow(x, INSTALLED_SUCCESSFULLY)) # whichDAG(Zenith!getIRIDForFlow(y, INSTALLED_SUCCESSFULLY))
                                                      \/ /\ firstHappening(installedIRs, x) < firstHappening(installedIRs, y)                                                         
                                                         /\ <<Zenith!getIRIDForFlow(y, INSTALLED_SUCCESSFULLY), Zenith!getIRIDForFlow(x, INSTALLED_SUCCESSFULLY)>> \notin whichDAG(x).e
                                                      \/ /\ firstHappening(installedIRs, x) > firstHappening(installedIRs, y)
                                                         /\ <<Zenith!getIRIDForFlow(x, INSTALLED_SUCCESSFULLY), Zenith!getIRIDForFlow(y, INSTALLED_SUCCESSFULLY)>> \notin whichDAG(x).e

TypeOK == Zenith!TypeOK

----
(* EVALUATION *)
----

CONSTANTS
s0, s1
----

CONSTANTS
t0, t1
----

\* Name of the switches in our topology
const_SW == {s0, s1}
----

\* Process IDs for OFC
const_OFCProcSet == (({ofc0} \X CONTROLLER_THREAD_POOL)) \cup 
                    (({ofc0} \X {CONT_EVENT})) \cup 
                    (({ofc0} \X {CONT_MONITOR}))

\* Name of threads in WP
const_CONTROLLER_THREAD_POOL == {t0}
----

\* What sort of switch failures do we want?
\*  - partial failure: Switch fails, but retains its internal state and TCAM.
\*                     If set to `0`, failure _WILL_ erase all state.
\*  - transient failure: Switch fails, but returns at some point in the future.
\*                       If set to `0`, the switch fails at some point and will
\*                       never recover again.
\* When two failure events are specified in the same set, they happen at the exact
\* same time. TLC will consider every scenario when failures are independent.

const_SW_FAIL_ORDERING == <<>>
\* const_SW_FAIL_ORDERING == <<{[sw |-> s0, partial |-> 0, transient |-> 1]}>>
\* const_SW_FAIL_ORDERING == <<{[sw |-> s0, partial |-> 0, transient |-> 1]}, {[sw |-> s0, partial |-> 0, transient |-> 1]}>>
\* const_SW_FAIL_ORDERING == <<{[sw |-> s0, partial |-> 0, transient |-> 1]}, {[sw |-> s1, partial |-> 0, transient |-> 1]}>>
----

\* How many instructions should we consider?
const_MaxNumIRs == 3
\* const_MaxNumIRs == 4
----

\* How many DAG changes should we expect at most?
const_MaxDAGID == 15
----

\* Which switch model to use? (simple/complex)
const_WHICH_SWITCH_MODEL == (s0 :> SW_SIMPLE_MODEL) @@ (s1 :> SW_SIMPLE_MODEL)
----

\* Specify which switch modules may fail (only accounted for with the complex model)
const_SW_MODULE_CAN_FAIL_OR_NOT == [cpu |-> 0, nicAsic |-> 0, ofa |-> 0, installer |-> 0]
----

\* When all failure events are accounted, what DAG do we _expect_ to see installed in the end?
const_FINAL_DAG == [v |-> {1, 2}, e |-> {<<1, 2>>}]

\* Where to install each IR?
const_IR2SW == (1 :> s0) @@ (2 :> s1) @@ (3 :> s1)
\* const_IR2SW == (1 :> s0) @@ (2 :> s1) @@ (3 :> s1) @@ (4 :> s0)

\* Mapping between topology and DAG
const_TOPO_DAG_MAPPING == 
    ({} :> [v |-> {1, 2}, e |-> {<<1, 2>>}]) @@ 
    ({s0} :> [v |-> {3}, e |-> {}])
\* const_TOPO_DAG_MAPPING == 
\*     ({} :> [v |-> {1, 2}, e |-> {<<1, 2>>}]) @@ 
\*     ({s0} :> [v |-> {3}, e |-> {}]) @@
\*     ({s1} :> [v |-> {4}, e |-> {}]) @@
\*     ({s0, s1} :> [v |-> {}, e |-> {}])

\* Which WP thread should handle which switch?
const_SW_THREAD_SHARD_MAP == (s0 :> t0) @@ (s1 :> t0)

\* How many module failures can we expect in the controller?
const_MAX_OFC_SUBMODULE_FAILS == 
    (CONT_MONITOR :> 0) @@ 
    (CONT_EVENT :> 0) @@ 
    (t0 :> 0) @@ 
    (t1 :> 0)

=============================================================================
