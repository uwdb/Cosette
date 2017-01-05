Development Instructions
========================

## Set up development environment

1. Install haskell (`GHC`)
2. `cabal update`
3. `cabal sandbox init`
4. `cabal install Parsec`
5. `cabal install HUnit`

## Test parser

`runghc QueryParseTest.lhs`

## Test output to rosette

`runghc ToRosetteTest.lhs`

## Test output to Coq

`cat examples/pullsubquery.cos | runghc CosetteSolver.lhs`
