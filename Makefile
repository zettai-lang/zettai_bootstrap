PWD := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))

.PHONY: build
build:
	dune build

.PHONY: test
test:
	dune test

.PHONY: test-coverage
test-coverage:
	dune runtest --force --instrument-with bisect_ppx
	bisect-ppx-report html
	bisect-ppx-report summary

.PHONY: functest
functest:
	cd functest && nix develop .# -ic $(MAKE) ZETTAI_INTERP=$(PWD)/_build/install/default/bin/zettai_bootstrap

.PHONY: clean
clean:
	dune clean
	rm -rf _coverage
