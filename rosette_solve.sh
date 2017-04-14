#!/bin/bash

PROG=/Cosette/dsl/dist/build/RosetteCodeGen/RosetteCodeGen
NAME=Cosette

BUILD=generated

FILE="$1"

UUID=$(head /dev/urandom | tr -dc A-Za-z | head -c 13 )


mkdir -p rosette/$BUILD
mkdir -p .compiled/

cat $FILE | $PROG > rosette/$BUILD/$UUID.rkt
cp rosette/$BUILD/$UUID.rkt .compiled/
cd rosette
racket server.rkt $BUILD/$UUID.rkt
