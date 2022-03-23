.PHONY: build license test usage

test: build
	cabal run bnfc-system-tests

usage: build
	cabal run bnfc-system-tests -- --help

license: build
	cabal run bnfc-system-tests -- --license

build:
	make -C src
	cabal build
#--allow-newer

# EOF
