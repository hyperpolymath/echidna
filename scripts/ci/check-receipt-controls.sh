#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell
# Accept actual model witnesses; reject three former verdict promotions.
set -euo pipefail

if ! command -v agda >/dev/null 2>&1 || [[ ! -f "${AGDA_LIBRARIES_FILE:-}" ]]; then
  echo '::error::Pinned Agda setup is missing; receipt controls NOT RUN'
  exit 2
fi
if [[ $(agda --version) != 'Agda version 2.7.0.1' ]]; then
  echo '::error::Unexpected Agda compiler; receipt controls NOT RUN'
  exit 2
fi

controls_dir=$(mktemp -d)
trap 'rm -rf -- "$controls_dir"' EXIT

cat > "$controls_dir/AcceptReceiptEvidence.agda" <<'AGDA'
module AcceptReceiptEvidence where
open import Echidna.Receipt
open import Data.Unit using (⊤)

checked-receipt : Asserts (λ _ → ⊤) sharpened proven sound w-here
checked-receipt = proven-in-sharpened-frame {assumptions = λ _ → ⊤}

checked-sample : Asserts (λ _ → ⊤) coarse tested-only sound w-there
checked-sample = one-passing-sample
AGDA

cat > "$controls_dir/RejectPostulateProjection.agda" <<'AGDA'
module RejectPostulateProjection where
open import Echidna.Receipt
open import Data.Product using (proj₂)

bad-postulate-projection :
  ∀ {assumptions frame φ w} →
  Asserts assumptions frame proven-with-postulates φ w →
  Asserts assumptions frame proven φ w
bad-postulate-projection claim = proj₂ claim
AGDA

cat > "$controls_dir/RejectWarrantAsTest.agda" <<'AGDA'
module RejectWarrantAsTest where
open import Echidna.Receipt
open import Data.Unit using (⊤)

bad-warrant-as-test : Asserts (λ _ → ⊤) coarse tested-only sound w-there
bad-warrant-as-test = warrant-elsewhere
AGDA

cat > "$controls_dir/RejectFalseSample.agda" <<'AGDA'
module RejectFalseSample where
open import Echidna.Receipt
open import Data.Nat using (zero)
open import Data.Unit using (tt)
open import Data.Vec using ([]; _∷_)
open import Data.Vec.Relation.Unary.All using ([]; _∷_)

bad-false-sample : TestEvidence sound
bad-false-sample = checked-samples zero (w-there ∷ []) (tt ∷ [])
AGDA

check_control() {
  local module=$1 expected=$2 log="$controls_dir/$1.log" result=0
  timeout --signal=TERM --kill-after=5s 90s agda \
    --no-default-libraries --library-file "$AGDA_LIBRARIES_FILE" \
    --library echidna-meta --include-path "$controls_dir" \
    --safe --without-K --cubical-compatible "$controls_dir/$module.agda" \
    > "$log" 2>&1 || result=$?
  if [[ "$result" -eq 124 || "$result" -eq 137 ]]; then
    echo "::error::$module timed out; receipt controls NOT RUN"
    exit 2
  fi
  if [[ "$expected" == accept ]]; then
    if [[ "$result" -ne 0 ]]; then
      cat "$log"
      echo "::error::$module did not accept the valid witnesses"
      exit 1
    fi
  else
    # Require the intended fixture and rejected expression. An import,
    # setup or parse error must never count as a rejecting control.
    if [[ "$result" -eq 0 ]] || ! grep -Fq "$controls_dir/$module.agda:" "$log" || \
       ! tr '\n' ' ' < "$log" | grep -Fq "$expected"; then
      cat "$log"
      echo "::error::$module did not reject the intended expression"
      exit 1
    fi
  fi
  echo "$module: $expected"
}

check_control AcceptReceiptEvidence accept
check_control RejectPostulateProjection 'when checking that the expression proj₂ claim has type'
check_control RejectWarrantAsTest 'when checking that the expression warrant-elsewhere has type'
check_control RejectFalseSample 'when checking that the expression tt has type'
