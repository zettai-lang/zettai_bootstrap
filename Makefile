.PHONY: build
build:
	dune build

.PHONY: test
test:
	dune test

.PHONY: test-coverage
test-coverage:
	dune runtest --instrument-with bisect_ppx --force
	bisect-ppx-report html
	bisect-ppx-report summary

.PHONY: clean
clean:
	rm -rf _build _coverage result
