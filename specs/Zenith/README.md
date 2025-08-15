# `ZENITH` Specification and Companion Model

- `zenith.tla` contains the full definition of `ZENITH`. It also has builtin logic for inducing module failures in OFC, as well as handling switch failures.
- `evaluate_zenith.tla` is a companion model checking specification, which can be used to describe what parameters to use to run the model checker (these include the topology, the DAGs, number of expected failures, etc.).
- `evaluate_zenith.cfg` is a TLC configuration file. In case new model values are added to the specification, this configuration file needs to be updated. Otherwise, there is little reason to change this configuration.

## Specification Inputs

The main inputs to the controller are the mapped definitions in the configuration file:
- `SW`: A set of model values, for all the switches that we can consider.
- `MaxNumIRs`: An integer, this defines the maximum number of installable network OPs that we can consider (essentially, it dictates the size of the NIB)
- `MaxDAGID`: An integer, the maximum number of DAGs that we can consider in a single behavior (dicates the size of NIB)
- `CONTROLLER_THREAD_POOL`: A set of model values, the number of threads in the OFC Worker Pool.
- `SW_FAIL_ORDERING`: A sequence, each element a set that defines which switch should fail and how. Items within a set, are bound to fail at exactly the same time. An empty sequence means that no failures are induced.
- `WHICH_SWITCH_MODEL`: A mapping from `SW` to either `SWITCH_SIMPLE_MODEL` or `SWITCH_COMPLEX_MODEL`. 
- `IR2SW`: A mapping from integers up to `MaxNumIRs`, to an element of `SW`. An IR (or a network OP as described in the paper) can be indexed with a single number, and this mapping describes where each IR should head towards.
- `TOPO_DAG_MAPPING`: A mapping from a set of switches (i.e. elements of `SW`) to a DAG record (see `FINAL_DAG` description for what this record looks like). To evaluate `ZENITH`, we use a simple TE application that given the set of failed switches in the network, elects a DAG and pushes it into the network while removing all previous configurations that it cannot allow. This mapping describes how a set of failed switches should be mapped to a new DAG in the network.
- `MAX_OFC_SUBMODULE_FAILS`: A mapping from model values to integer, it dictates the maximum number of submodule failures that we can consider in OFC. Since considering all module failures for all steps blows up the state space, we advise that modules be tested one-by-one.
- `SW_THREAD_SHARD_MAP`: A mapping from `SW` to `CONTROLLER_THREAD_POOL`, dictating which thread in the OFC Worker Pool may handle operations destined for a particular switch.
- `OFCProcSet`: Set of pairs of model values. Unless a change is made to the processes within `ZENITH`, this input can be left unchanged.
- `SW_MODULE_CAN_FAIL_OR_NOT`: Specifically for complex switch model, it describes which switch modules can or cannot fail when failure is allowed. By default, every module can fail.
- `FINAL_DAG`: A DAG (a record with two fields, `v` and `e`, where `v` is a set of integers and `e` is a set of integer pairs, describing the nodes and edges of the DAG to consider). By _final_, we mean the DAG that we _expect_ to see in the network once all failures described in `SW_FAIL_ORDERING` have passed and all transient failures have recovered.

## Changing Default Model Checking Scenario

To change what the controller goes through, one need only change these mapped values in `evaluate_zenith.tla`, under the `EVALUATION` section. These values are named as `const_*`. They are mostly self-explanatory with the exception of `const_SW_FAIL_ORDERING`.

The format that we expect this value is a sequence of sets, where each element in the set is a record with 3 fields:
- `sw`: A member of `SW`.
- `partial`: If set to **1**, will only wipe the state of modules flagged in `SW_MODULE_CAN_FAIL_OR_NOT`, otherwise must be **0** which indicates that all switch modules fail (i.e. a complete failure).
- `transient`: If set to **1**, a failed switch will eventually recover, otherwise it must be **0** which keeps the switch forever down afterwards (note that changing this would mean that one would also have to change `FINAL_DAG`, otherwise it would be impossible to converge to the DAG since its associated switch never returns to the topology).

## Runtime

> **Important Note:** We recommend around 8 GB of memory at least for most scenarios, and as many CPU cores. The number of cores, determine how quickly TLC can do a BFS on behaviors. Considering that the state space is on the larger side, this helps cut down on verification runtime. However, checking temporal properties takes much longer since it can only be done on a single thread. All verification times reported here are on a 64 core AMD EPYC 7763.

With full concurrency and default input DAGs, the runtime and state space descriptions are as follows:

| Scenario Description                                 | # States (Distinct) | State Space Diameter | Verification Time |
|------------------------------------------------------|:-------------------:|:--------------------:|:-----------------:|
| 1 WP thread(s), No Failures                          | 173 (115)           | 38                   | 1 sec             |
| 2 WP thread(s), No Failures                          | 355 (215)           | 38                   | 1 sec             |
| 1 WP thread(s), 1 Switch Failure(s)                  | 407406 (211673)     | 166                  | 21 sec            |
| 1 WP thread(s), 1 WP Failure(s)                      | 1590 (947)          | 48                   | 2 sec             |
| 2 WP thread(s), 1 WP Failure(s)                      | 5395562 (2731325)   | 176                  | 5 min 49 sec      |
| 1 WP thread(s), 1 EH Failure(s), 1 Switch Failure(s) | 6372910 (3042469)   | 179                  | 6 min 17 sec      |
| 1 WP thread(s), 2 Switch Failure(s)                  | 65668533 (31807704) | 294                  | 57 min 36 sec     |

## Small Note

The processes that induce switch failure and recovery are `swFailureProc` and `swResolveFailure`. These processes were explicitly mentioned to be unfair in the paper (as described in Listing 2, section 4). In this specification however, we have elected to make them fair, since otherwise we would not be able to dictate how many failures we can induce. Making them unfair again has the benefit of handling more scenarios at one time (including no failures) at the cost of much longer runtime.

## What If `ZENITH` Was Wrong?

To see how TLC would report an error, let us introduce a bug into our (presumably correct, it requires proof) `ZENITH`. One very simple race condition can be made between WP and MS by sending an OP first and declaring it as `IR_SENT` only _after_ we emit it.

Currently, `ZENITH` specifically avoids this (in `zenith.tla`, the label `ControllerThreadSendIR` starting on line 617 set the state to `IR_SENT` on line 648, before it actually sends the instruction in label `ControllerThreadForwardIR` by calling the macro `controllerSendIR` on line 667). Let us reverse these like the following:

```
(* Line 642 ends here *)
whichStepToFail(2, stepOfFailureWP);

if (stepOfFailureWP = 1) then
    workerPoolFails();
else
    if (stepOfFailureWP = 2) then
        workerPoolFails();
    else
        controllerSendIR(nextIRObjectToSend);
    end if;
end if;

ControllerThreadForwardIR:
    controllerWaitForLockFree();
    setNIBIRState(nextIRObjectToSend.IR, IR_SENT);

    if (stepOfFailureWP = 2) then
        workerPoolFails();
    else
        RCNIBEventQueue := Append(
            RCNIBEventQueue, 
            [type |-> IR_MOD, IR |-> nextIRObjectToSend.IR, state |-> IR_SENT]
        );
    end if;
end if;
```

Since we changed the PlusCal algorithm, we should translate it again:
```
python3 evaluate.py --action build Zenith/zenith.tla
```
And now we evaluate it, without even inducing any failures:
```
# Output the result into `tlc.out`
python3 evaluate.py --action check Zenith/evaluate_zenith.tla | tee tlc.out
```

TLC reports a temporal property violation (a deadlock in this case) which should have a preamble like the following:
```
Error: Temporal properties were violated.

Error: The following behavior constitutes a counter-example:
```

To get a better sense of the trace, we get the DIFF between steps and get rid of the initial step and the PC variable (the default behavior of `trace_utils.py`). We can do this by:
```
# Parse the TLC trace and output a DIFF in `trace.out`
python3 trace_utils.py tlc.out trace.out
```

The final two steps that we see are the following:
```
STEP 38 [[rcNibEventHandlerStep]]
	RCNIBEventQueue: <<>>
	RCIRStatus: <<[primary |-> IR_DONE, dual |-> IR_NONE], [primary |-> IR_SENT, dual |-> IR_NONE], [primary |-> IR_NONE, dual |-> IR_NONE]>>
	event: (<<rc0, NIB_EVENT_HANDLER>> :> [type |-> IR_MOD, state |-> IR_SENT, IR |-> 2])

STEP 39 [[Stuttering]]
```
The NIB Event Handler received a final update from the controller that IR index 2 has been sent and we never got the news of its installation, but if we look at the last recorded value of the switch TCAM (just look for the last time `TCAM` was seen in the trace output), we get this:
```
STEP 29 [[SwitchStep]]
	switch2Controller: <<[type |-> INSTALLED_SUCCESSFULLY, flow |-> 2, from |-> s1, to |-> ofc0]>>
	ingressPkt: (<<SW_SIMPLE_ID, s0>> :> [type |-> INSTALL_FLOW, flow |-> 1, from |-> ofc0, to |-> s0] @@ <<SW_SIMPLE_ID, s1>> :> [type |-> INSTALL_FLOW, flow |-> 2, from |-> ofc0, to |-> s1])
	controller2Switch: (s0 :> <<>> @@ s1 :> <<>>)
	switchLock: <<NO_LOCK, NO_LOCK>>
	installedIRs: <<1, 2>>
	TCAM: (s0 :> {1} @@ s1 :> {2})
```
The last step by our simple switch model, correctly installed the IR on switch `s1` and emitted an ACK on `switch2Controller`. Two steps further, the Monitoring Server records the installation of the IR on the NIB and sends the update to the NIB Event Handler on `RCNIBEventQueue`.
```
STEP 31 [[controllerMonitoringServerStep]]
	RCNIBEventQueue: <<[type |-> IR_MOD, state |-> IR_DONE, IR |-> 2]>>
	NIBIRStatus: <<[primary |-> IR_DONE, dual |-> IR_NONE], [primary |-> IR_DONE, dual |-> IR_NONE], [primary |-> IR_NONE, dual |-> IR_NONE]>>
	irID: (<<ofc0, CONT_MONITOR>> :> 2)
	FirstInstall: <<1, 1, 0, 0, 0, 0>>
```
However, a bit further we see the problem on step 33:
```
STEP 33 [[controllerWorkerThreadsStep]]
	RCNIBEventQueue: <<[type |-> IR_MOD, state |-> IR_DONE, IR |-> 2], [type |-> IR_MOD, state |-> IR_SENT, IR |-> 2]>>
	NIBIRStatus: <<[primary |-> IR_DONE, dual |-> IR_NONE], [primary |-> IR_SENT, dual |-> IR_NONE], [primary |-> IR_NONE, dual |-> IR_NONE]>>
```
Essentially, we received the ACK for IR index 2 almost immediately after we sent it, such that when Worker Pool attempted to set the state to `IR_SENT`, it was already set to `IR_DONE`!

One could solve this in many ways (like a compare-and-swap on IR state in the Worker Pool for setting the state to `IR_SENT`), but we found that setting the state first and emitting the instruction later is simpler.
