#!/usr/bin/env bash
set -x

unset CONDA_SHLVL
eval "$(python -m conda shell.bash hook)"
conda activate base
export PYTHON_MAJOR_VERSION=$(python -c "import sys; print(sys.version_info[0])")
export TEST_PLATFORM=$(python -c "import sys; print('win' if sys.platform.startswith('win') else 'unix')")
export PYTHONHASHSEED=$(python -c "import random as r; print(r.randint(0,4294967296))") && echo "PYTHONHASHSEED=$PYTHONHASHSEED"
env | sort
conda info
conda create -y -p ./built-conda-test-env python=3.5
conda activate ./built-conda-test-env
echo $CONDA_PREFIX
[ "$CONDA_PREFIX" = "$PWD/built-conda-test-env" ] || exit 1
[ $(python -c "import sys; print(sys.version_info[1])") = 5 ] || exit 1
conda deactivate
py.test tests -m "not integration and not installed" -vv
