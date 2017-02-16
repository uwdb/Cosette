Run SQL Rewrite Examples
========================

## Generate Coq Source Code

1. go to `Cosette/dsl` folder and compile `CoqCodeGen.lhs`:

	`ghc CoqCodeGen.lhs`

2. run `CoqCodeGen` on cosette source files under current folder:

	`cat pullsubquery.cos | ../../dsl/CoqCodeGen`
