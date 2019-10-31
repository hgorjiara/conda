#!/bin/bash

export CLASSPATH=./csolver/original.jar:.:$CLASSPATH
export PYTHONPATH=./csolver
export LD_LIBRARY_PATH=./csolver
# For Mac OSX
export DYLD_LIBRARY_PATH=./csolver
# For sat_solver
export PATH=./csolver:.:$PATH

$@
