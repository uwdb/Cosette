HoTTSQL: Proving Query Rewrites wth Univalent SQL Semantics
===========================================================

## Overview

We have provided a docker container containing the implementation of HoTTSQL, a machine checkable formal semantics for SQL, as well as the SQL rewrite rules that have been proved usng HoTTSQL.

The core part of HoTTSQL (HoTTIR) is implemented using Coq with Homotopy Type Theory library. The parsing of the front end language and the translation from front end language to HoTTIR is implemented using Haskell.


## Claims

1. Users can express SQL rewrite rules in HoTTSQL (front end syntax) and our system will translate HoTTSQL to HoTTIR (Sec 4).

2. HoTTSQL can be used to prove a wide range of real world SQL rewrites with brief proofs (Sec 5.1).

3. HoTTSQL's automatic solving tactic for Conjunctive queries are effective (Sec 5.2).

## Setup

1. Install [docker](https://www.docker.com/products/docker) for your host OS.

2. Pull the prepared docker container from dockerhub:
   `docker pull shumo/hottsql`

3. Run the docker container and open a console running on the docker container by (you may need to do `docker rm -f hottsql` if you already have a container named `hottsql`.):
   `docker run --name hottsql --entrypoint /bin/bash -ti shumo/hottsql` (replace `/bin/bash` with your favorite shell, also this command has not been tested in Windows)

## Run the experiment

In the docker console (See step 3 in Setup), run the following commands:

	cd /Cosette
	sh ./run_examples.sh

	
This will produce the following output:

	./hott/optimizations/generated/CQExample0.v generated.
	./hott/optimizations/generated/CQExample1.v generated.
	./hott/optimizations/generated/SelfJoin0.v generated.
	./hott/optimizations/generated/SelfJoin1.v generated.
	./hott/optimizations/generated/SelfJoin2.v generated.
	./hott/optimizations/generated/commutativeSelect.v generated.
	./hott/optimizations/generated/conjunctSelect.v generated.
	./hott/optimizations/generated/disjointSelect.v generated.
	./hott/optimizations/generated/idempotentSelect.v generated.
	./hott/optimizations/generated/inlineCorrelatedSubqueries.v generated.
	./hott/optimizations/generated/productDistributesOverUnion.v generated.
	./hott/optimizations/generated/projectionDistributesOverUnion.v generated.
	./hott/optimizations/generated/pullsubquery.v generated.
	./hott/optimizations/generated/pushdownSelect.v generated.

`run_examples.sh` will generate a Coq source code file for each rewrite rule in `Cosette/examples/` and write the Coq source code to `Cosette/hott/optimizations/generated` by calling the compiler (HoTTSQL to HoTTIR). A generated Coq file contains the specification of the rule using HoTTIR as well as a proof for the rule, which is a combination of different automated solving tactics. 

To validate the generated rewrite rules as well as the rewrite rules that we have manually proved in `Cosette/hott/optimizations`, run:

	cd /Cosette/hott
	make
	
`hoqc` (HoTT verison of `coqc`)  will be called to compile all the `*.v` file in `/Cosette/hott` folder. The success of `make` requires all the Coq proofs to be validated. This will produce the following output:
	
	mkdir .build 2> /dev/null || true
	find . -path ./.build -prune -o -name '*.v' -print | xargs cp -a --parents -t .build
	cd .build; find . -name '*.v' | xargs coq_makefile -R . Cosette -o Makefile
	sed -i.bak "s/coq/hoq/" .build/Makefile
	make -j4 -C.build
	make[1]: Entering directory `/Cosette/hott/.build'
	......
	make[1]: Leaving directory `/Cosette/hott/.build'
	make[1]: Entering directory `/Cosette/hott/.build'
	"hoqc"  -q  -R "." Cosette   library/HoTTEx
	"hoqc"  -q  -R "." Cosette   library/Denotation
	......
	"hoqc"  -q  -R "." Cosette   optimizations/Subquery
	make[1]: Leaving directory `/Cosette/hott/.build'

Each `*.v` files under `Cosette/hott/optimizations` can be inspected. For example, `Cosette/hott/optimizations/Conjunctive.v` can be checked to see our usage of conjuctive query automated solving tactic.

## Source Code

All source code is in `/Cosette` directory. The source code is arranged as follows:

* `hott`: All the Coq files, including denotation semantics of HoTTIR, a library developed from proving rewrite rules, and all the rules that we proved and validated using Coq. 

* `dsl`: Parser of HoTTSQL and translation from HoTTSQL to HoTTIR.

* `examples`: SQL rewrites expressed in HoTTSQL (all `*.cos` files).
