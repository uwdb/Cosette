#!/bin/bash

SED="sed -i"
UNAME=`uname`
if [[ "$UNAME" == "Darwin" ]]; then
    SED='sed -i ""'
fi

function run_test {
    for i in `seq 1 $2`;
    do
        $SED "s/[0-9]/$i/";
        for j in `seq 0 2`;
        do
            racket $1 | grep "cpu time" &
        done;
        wait;
        echo "";
    done;
}

TEST_DIR=.

EASY_TESTS="simpleRA.rkt push-projection.rkt subquery-exists.rkt magic-set.rkt"
HARD_TESTS="aggr-pull-up.rkt subquery-test.rkt aggr-join.rkt"

for test in $EASY_TESTS;
do
    echo "============== $test ==============";
    run_test $TEST_DIR/$test 4;
done;
wait

for test in $HARD_TESTS;
do
    echo "============== $test ==============";
    run_test $TEST_DIR/$test 2;
done;
wait
