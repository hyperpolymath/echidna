#!/bin/bash
# Generate provers.a2ml from a variant list.
# Snake-case conversion: PascalCase -> snake_case (matches serde default).
set -euo pipefail

cat << 'HEADER'
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# provers.a2ml — Authoritative enumeration of ECHIDNA prover backends.
#
# Generated from src/rust/provers/mod.rs::ProverKind. One section per
# variant, keyed by the variant's PascalCase name for stability against
# slug-format drift. `slug` is the snake_case identifier used on the
# wire (matches serde's rename_all = "snake_case" default).
#
# Downstream consumers:
#   - .github/workflows/backend-matrix.yml (vcl-ut) reads this file to
#     build its matrix strategy, one job per prover.
#   - Future sync check fails CI if this file drifts from ProverKind::all().
#
# SYNC SOURCE-OF-TRUTH: `pub enum ProverKind` in src/rust/provers/mod.rs.
# If that enum changes, regenerate with scripts/gen-provers-a2ml.sh.

[metadata]
version = "1.0.0"
source  = "src/rust/provers/mod.rs::ProverKind"
date    = "2026-04-24"
HEADER

printf "count   = %d\n\n" "$(wc -l < /tmp/provers-list.txt)"

while IFS= read -r variant; do
  # snake_case: lowercase + insert underscore before uppercase letter that
  # follows a lowercase letter, and before uppercase letter that starts
  # an all-caps cluster preceded by lowercase.
  slug=$(echo "$variant" | sed -E 's/([a-z0-9])([A-Z])/\1_\2/g; s/([A-Z]+)([A-Z][a-z])/\1_\2/g' | tr '[:upper:]' '[:lower:]')
  echo "[prover.${variant}]"
  echo "slug = \"${slug}\""
  echo ""
done < /tmp/provers-list.txt
