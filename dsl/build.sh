#!/bin/sh

cabal update
cabal sandbox init
cabal configure
cabal build
