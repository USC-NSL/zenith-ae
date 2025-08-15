# Switch Model Specification
This directory contains our switch model definitions. 
- `abstract_sw.tla` defines a simple, monolithic switch that handles operations in a single atomic step. This is the only model that is somewhat scalable.
- `switch.tla` contains a much more fine-grained switch definitions, with internal components that can fail independently.

In `eval_constants`, we define a mapping, `WHICH_SWITCH_MODEL` that maps that switch names (i.e. model values like `s0`, `s1`, etc.) to either `SWITCH_SIMPLE_MODEL` or `SWITCH_COMPLEX_MODEL`. Depending on your choice, you may use any of these to enforce which model each switch runs (it is possible to run the complex model on only a particular set of switches and leave the rest as a simple model).
