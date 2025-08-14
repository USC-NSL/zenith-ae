# General Definitions For `ZENITH` and `NADIR`
The specifications in this directory define little logic. They merely bundle constant definitions so that we do not have
to repeat them again at the top of other modules.
```
Include
  |
  +---- dag.tla                Simple definitions for reasoning about DAGs
  |
  +---- eval_constants.tla     Model value definitions used for evaluating ZENITH
  |
  +---- graph.tla              Simple definitions for reasoning about paths in graphs
  |                            and a recursive BFS operator.
  |
  +---- nib_constants.tla      Model value definitions used to describe the NIB
  |
  +---- switch_constants.tla   Model value definitions used to describe our switch model
  |
  +---- Nadir                  Definitions specifically used by NADIR as annotations
          |
          +---- NadirFIFO      Type definitions for a FIFO queue
          |
          +---- NadirAckQueue  Type definitions for a simple acknowledgement queue
          |
          +---- NadirTypes     Other type definitions (specifically functions)
```