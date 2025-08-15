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