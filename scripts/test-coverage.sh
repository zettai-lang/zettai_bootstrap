#!/usr/bin/env bash

set -euxo pipefail

test_status=0
dune runtest --sandbox none --force --instrument-with bisect_ppx || test_status="$?"

bisect-ppx-report html
bisect-ppx-report summary

test "$test_status" -eq 0
