#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell
# Require exactly one selected live smoke test; absent tools are NOT RUN.
set -euo pipefail

backend=${1:?usage: run-live-prover.sh BACKEND}
case "$backend" in
  z3|cvc5|vampire|eprover|minizinc) executable=$backend ;;
  alt-ergo) executable=alt-ergo ;;
  spass) executable=SPASS ;;
  glpk) executable=glpsol ;;
  chuffed) executable=fzn-chuffed ;;
  *) echo "::error::Unsupported required backend: $backend"; exit 2 ;;
esac
for tool in cargo "$executable"; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "::error::Required command $tool is absent for $backend; live smoke check NOT RUN"
    exit 2
  fi
done

test_name="live_${backend//-/_}_version"
if ! listing=$(cargo test --locked -p echidna --test live_prover_suite --features live-provers -- --list --exact "$test_name"); then
  echo "::error::Could not build/list the selected test; live smoke check NOT RUN"
  exit 2
fi
if ! printf '%s\n' "$listing" | grep -Fxq "$test_name: test"; then
  echo "::error::Selected test $test_name is absent; live smoke check NOT RUN"
  exit 2
fi
if ! ECHIDNA_REQUIRE_LIVE_PROVER=1 cargo test --locked -p echidna \
    --test live_prover_suite --features live-provers -- --nocapture --exact "$test_name"; then
  echo "::error::Selected $backend live smoke test failed"
  exit 1
fi
