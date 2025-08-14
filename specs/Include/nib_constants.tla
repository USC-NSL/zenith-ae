-------------------------- MODULE nib_constants --------------------------
EXTENDS FiniteSets, TLC

(* IR states to track within the NIB *)
CONSTANTS IR_NONE, IR_SENT, IR_DONE, IR_FAILED

(* Switch states to track within the NIB *)
CONSTANTS SW_RUN, SW_SUSPEND

(* DAG states to track within NIB *)
CONSTANTS DAG_NONE, DAG_STALE, DAG_SUBMIT, DAG_NEW

(* Label to declare an IR unlocked for other threads to work on *)
CONSTANTS IR_UNLOCK

(* Label to declare a DAG unlocked for other sequencer threads to work on *)
CONSTANTS DAG_UNLOCK

(**************************************************************************)
(* Label for internal controller module states within NIB.                *)
(* This is the minimum set, and will be extended for each spec if needed. *)
(**************************************************************************)
CONSTANTS NO_STATUS, STATUS_START_SCHEDULING, STATUS_LOCKING, 
          STATUS_SENT_DONE, START_RESET_IR

(* Label for noting that an enqueued IR was never tagged by a thread *)
CONSTANTS NO_TAG

(* Maximum number of INSTALL IRs to consider *)
CONSTANTS MaxNumIRs

(* Maximum number of distinct DAGs to consider *)
CONSTANTS MaxDAGID

(* TE event types *)
CONSTANTS TOPO_MOD, IR_MOD

(* Specifically for switch-side reconciliation *)
CONSTANTS SW_RECONCILE

===========================================================================