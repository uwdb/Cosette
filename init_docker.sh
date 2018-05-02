#!/bin/bash

DIR="/Cosette-Dev"
# the command to build and test solver
CMD="cd dsl; cabal install HUnit; cabal install Parsec; cabal build; cd .." #; python solver_test.py"
NAME="cosette-test"

# uncomment the following command if not exist
# docker pull shumo/cosette-frontend

echo "[0] starting container with name $NAME ..."
docker run -v $(pwd)/:$DIR -w $DIR --name=$NAME -it shumo/cosette-frontend bash #-c "$CMD"

#echo "[2] removing the container ..."
#docker rm $NAME

#echo "[3] remove generated files ..."
#rm -r .compiled/
#rm -r dsl/dist/
#rm -r hott/.build_solve/
#rm -r rosette/generated/
#rm solver.pyc
