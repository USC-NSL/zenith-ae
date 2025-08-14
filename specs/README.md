# `ZENITH` TLA+ Specifications

This directory contains the specifications for describing and evaluating the `ZENITH` controller.
```
specs
  |
  +---- Include           TLA+ specifications that define constants and helper operators.
  |
  +---- Switch            TLA+ specifications of our switch model.
  |
  +---- Zenith            TLA+ specification of the final ZENITH controller, along with
  |                       a companion specification for model checking it.
  |
  +---- evaluate.py       A utility that links the contents of `Include` and our ZENITH 
  |                       specification with the `tla2tools.jar` file so that it can use
  |                       SANY, TLC and the PlusCal translator without the TLA+ toolbox.
  |
  +---- trace_utils.py    Some utilities for parsing the traces produced by TLC.
```

# Checking The Specification

We only need TLC and a small amount of Python code to check `ZENITH`.

## Environment Setup

We provide instructions for setting up on Ubuntu 20.04:

```
# install Java
sudo apt-get install openjdk-8-jdk

# download the tla2tools JAR file
wget https://github.com/tlaplus/tlaplus/releases/download/v1.7.4/tla2tools.jar

# Set an environment variable for pointing to the JAR file
export TLA_HOME="./tla2tools.jar"

# Install Lark and chardet
python3 -m pip install -r requirements.txt
```

## Building and Model Checking `ZENITH`

See the contents of `Zenith` folder for instructions for how to change the evaluation parameters. Once done, the model checker can be invoked by
the following:
```
# Build the ZENITH TLA+ specification from the PlusCal algorithm
python3 evaluate.py --action build Zenith/zenith.tla

# Model check ZENITH according to the evaluation setting described in the companion specification
python3 evaluate.py --action check Zenith/evaluate_zenith.tla
```
