#!/bin/bash

NAME=Cosette

BUILD=generated

# by default only takes in file and time as input argument
FILE="$1"
TIME="$2"

filename=$(basename "$FILE")
filename="${filename%.*}"

UUID="tmp_"$filename

mkdir -p rosette/$BUILD
mkdir -p .compiled/

cp $FILE rosette/$BUILD/$UUID.rkt
cp rosette/$BUILD/$UUID.rkt .compiled/
cd rosette

#echo "[OK] solving "$BUILD/$UUID.rkt
racket test-server.rkt $BUILD/$UUID.rkt $TIME "--symbreak" #"$3" "$4" "$5"