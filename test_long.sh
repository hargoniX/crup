#!/bin/sh

lake build || exit 1

time lake exe crup ./examples/bf0432-007.cnf ./examples/bf0432-007_proof.rup nolog
if [ $? -ne 0 ]; then
        exit 1;
fi
