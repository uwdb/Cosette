#!/bin/bash

PROG=./dsl/CoqCodeGen
CODEPATH=./hott/optimizations/generated 

mkdir -p $CODEPATH

for i in ./examples/sqlrewrites/*.cos ; do
    rule=$(basename $i .cos)
    cat $i | $PROG > $CODEPATH/$rule.v
    echo "$CODEPATH/$rule.v generated."
done
