#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell
# Fixture test for the comment-aware scan in agda-cone-receipt.sh: comments
# (line, block, nested) hide nothing they should not, pragmas stay visible,
# and only the keyword `postulate` counts, not identifiers that contain it.
set -euo pipefail
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
# shellcheck source=scripts/ci/agda-cone-receipt.sh
AGDA_CONE_RECEIPT_FUNCTIONS_ONLY=1 . "$here/agda-cone-receipt.sh"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cat > "$tmp/Fx.agda" <<'AGDA'
module Fx where
-- postulate in a line comment
{- postulate in a block {- nested postulate -} still comment postulate -}
x = 1 -- trailing postulate
{-# TERMINATING #-}
postulate
  ax : Set
postulates-name : Set
f = primTrustMe
{-# OPTIONS --safe #-}
AGDA
got=$(scan "$tmp/Fx.agda" | cut -d: -f1 | tr '\n' ' ')
want="5 6 9 "
if [[ "$got" == "$want" ]]; then
  echo "agda-cone-receipt scan: ok (hits on lines $got)"
else
  echo "::error::agda-cone-receipt scan: hits on lines '$got', want '$want'"
  exit 1
fi
