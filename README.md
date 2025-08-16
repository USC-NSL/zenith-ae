# SIGCOMM'25 Artifact Evaluation for `ZENITH`

This repository contains the specification and implementation of the `ZENITH` controller, as part of our submission to SIGCOMM 2025.

>**Note To The SIGCOMM AEC:** While we are confident in the functionality of our artifact and have provided directions for testing them and documentation, we currently do not have the bandwidth to release our code generator tool, `NADIR`. For this reason, the artifact cannot be considered complete and hence will be submitted for the ***Artifact Available*** badge.
>
> We hope to release `NADIR` with all of our previous specifications as soon as possible.

The repository contains two main components:
- **The `ZENITH` Specification:** The heart of our project is the `ZENITH` algorithm description, which we have elected to write with TLA+ and PlusCal. We have the provided the final version of the specification under the `specs` directory. Direction have been provided for how it can be model checked (be advised that model checking can take a bit).
- **The `ZENITH` Implementation and Generated Code:** Under `impl`, we have provided the full implementation of the controller, along with helper scripts that can be used to work with it. We have provided directions for setting up the environment as well as how to run the controller. The `NADIR` Python runtime (i.e. `pynadir`) can be found there as well.

# License

Our code is provided under MIT license, with the exception of the OpenFlow protocol description under `impl/openflow/ryulib` which we have borrowed from the [RYU](https://github.com/faucetsdn/ryu/tree/master) controller. The content of this particular directory were made available under Apache 2.0 license.