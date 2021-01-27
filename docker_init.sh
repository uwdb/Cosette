#!/bin/bash


NAME="cosette-minimal-container"

echo "[0] starting container with name $NAME ..."
docker run -w /Cosette --name=cosette-minimal-container  -it cosette-minimal bash

#DIR="/Cosette-Dev"
# the command to build and test solver

# uncomment the following command if not exist
# docker build -t cosette-minimal .

#echo "[0] starting container with name $NAME ..."
#docker run -v $(pwd)/:$DIR -w $DIR --name=$NAME -it cosette-minimal bash #-c "$CMD"

#echo "[2] removing the container ..."
#docker rm $NAME

#echo "[3] remove generated files ..."
#rm -r .compiled/
#rm -r dsl/dist/
#rm -r hott/.build_solve/
#rm -r rosette/generated/
#rm solver.pyc
