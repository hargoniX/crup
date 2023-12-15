#!/bin/sh

lake build || exit 1

lake exe crup examples/test1.cnf examples/proof1.rup
if [ $? -ne 0 ]; then
        exit 1;
fi

lake exe crup examples/test1.cnf examples/proof1_alt.rup
if [ $? -ne 0 ]; then
        exit 1;
fi

lake exe crup examples/test1.cnf examples/proof1_broken.rup
if [ $? -ne 3 ]; then
        exit 1;
fi

lake exe crup examples/test2.cnf examples/proof2.rup
if [ $? -ne 0 ]; then
        exit 1;
fi

lake exe crup examples/test3.cnf examples/proof3.rup
if [ $? -ne 0 ]; then
        exit 1;
fi

lake exe crup examples/test3.cnf examples/proof3_broken.rup
if [ $? -ne 2 ]; then
        exit 1;
fi
