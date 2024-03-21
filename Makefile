PWD := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
ZETTAI_INTERP := _build/install/default/bin/zettai_bootstrap

default: $(ZETTAI_INTERP)

dune-rules.mk:
	dune rules --makefile --recursive > dune-rules.mk

-include dune-rules.mk

.PHONY: test
test:
	dune test

.PHONY: test-coverage
test-coverage:
	dune runtest --force --instrument-with bisect_ppx
	bisect-ppx-report html
	bisect-ppx-report summary

.PHONY: functest
functest: $(ZETTAI_INTERP)
	cd functest && nix develop .# -ic $(MAKE) ZETTAI_INTERP=$(PWD)$(ZETTAI_INTERP)

.PHONY: clean
clean:
	dune clean
	rm -rf _coverage dune-rules.mk
