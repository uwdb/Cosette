HoTTSQL: Proving Query Rewrites wth Univalent SQL Semantics
===========================================================
[Shumo Chu](www.shumochu.com), [Konstantin Weitz](http://www.konne.me/), [Alvin Cheung](https://homes.cs.washington.edu/~akcheung/), [Dan Suciu](https://homes.cs.washington.edu/~suciu/)

## Overview

We have provided a docker container containing the implementation of HoTTSQL, a machine checkable formal semantics for SQL, as well as the SQL rewrite rules that have been proved using HoTTSQL.

The core part of HoTTSQL (HoTTIR) is implemented using Coq and the Homotopy Type Theory library. Parsing of the front end language and the translation from front end language to HoTTIR is implemented using Haskell.


## Claims

1. Users can express SQL rewrite rules in HoTTSQL (front end syntax) and our system will translate HoTTSQL to HoTTIR (Sec 4).

2. HoTTSQL can be used to concisely prove a wide range of real world SQL rewrite rules(Sec 5.1).

3. HoTTSQL's automatic conjunctive query solving tactics are effective (Sec 5.2).

## Setup

1. Install [docker](https://www.docker.com/products/docker) for your host OS.

2. Pull the prepared docker container from dockerhub:
   
   ```
   docker pull shumo/hottsql
   ``` 

3. Run the docker container, and open a console running in the docker container (you may need to do `docker rm -f hottsql` if you already have a container named `hottsql`.):
   
   ```
   docker run --name hottsql --entrypoint /bin/bash -ti shumo/hottsql
   ```
   
   (You can replace `/bin/bash` with your favorite shell, also this command has not been tested on Windows.)

## Running the experiment

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

`run_examples.sh` generates a Coq source code file for each rewrite rule in `Cosette/examples/` and writes the Coq source code to `Cosette/hott/optimizations/generated` by calling the parser to translate from HoTTSQL to HoTTIR. The generated Coq file contains the specification of the rule using HoTTIR as well as a proof script for the rule, which contains calls to different automated solving tactics for validating the rule.
 

To validate the rewrite rules that we have proven automatically and manually in Sec. 5 of the paper, as well as contained in `Cosette/hott/optimizations`, run 

	cd /Cosette/hott
	make
	
When executed, `hoqc` (HoTT verison of `coqc`) is called to compile each of the `*.v` files in `/Cosette/hott`. `make` only succeeds after all of the Coq proofs are validated. You should get an output that looks like the following:

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

Each `*.v` file under `Cosette/hott/optimizations` can be inspected. For example, check `Cosette/hott/optimizations/Conjunctive.v` to see our usage of the conjunctive query automated solving tactic. You can add your own rewrite rule in `Cosette/examples` and save it with extension `.cos`. To check whether cosette can prove your rewrite rule automatically, run:

	sh /Cosette/run_examples.sh
	cd /Cosette/hott
	make

If the automated tactics failed, you can try to edit the generated .v file to add your manual proof as well.


## Source Code

All source code is in `/Cosette` directory. The source code is arranged as follows:

* `hott`:  The Coq files, including denotation semantics of HoTTIR, a library developed from proving rewrite rules, and all the rules that we proved and validated using Coq. 

* `dsl`: HoTTSQL parser from HoTTSQL to HoTTIR.

* `examples`: SQL rewrites expressed in HoTTSQL front end syntax (`*.cos` files).

