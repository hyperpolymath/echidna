#!/bin/bash
# Generate provers.a2ml from a variant list.
# Snake-case conversion: PascalCase -> snake_case (matches serde default).
#
# Usage: gen-provers-a2ml.sh <variant-list-file>
#
# Pass the variants case-insensitively sorted to match the committed
# layout (.machine_readable/provers.a2ml) and keep diffs minimal.
# Case-only ties are not resolved by the sort: list `Mizar` before
# `MizAR`, as the committed file does.
#
# The header template below declares MPL-2.0, matching both the root LICENSE
# and the committed .machine_readable/provers.a2ml (reconciled 2026-10-01,
# D262). Keep the two in step: a regeneration must not change the SPDX line.
#
# The variant-list path is a CLI argument (was the hard-coded
# /tmp/provers-list.txt); predictable /tmp/* paths are a panic-attack
# low (path-traversal / TOCTOU on multi-user runners). Callers should
# pass `$(mktemp)` or any path they control.
set -euo pipefail

VARIANT_LIST="${1:-}"
if [ -z "$VARIANT_LIST" ] || [ ! -r "$VARIANT_LIST" ]; then
  echo "usage: $0 <variant-list-file>" >&2
  echo "  (one PascalCase variant per line; e.g. \"$(mktemp)\" populated by caller)" >&2
  exit 2
fi

cat << 'HEADER'
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# provers.a2ml — Authoritative enumeration of ECHIDNA prover backends.
#
# Generated from crates/echidna-core/src/prover_kind.rs::ProverKind. One section per
# variant, keyed by the variant's PascalCase name for stability against
# slug-format drift. `slug` is the snake_case identifier used on the
# wire (matches serde's rename_all = "snake_case" default).
#
# This is a declaration inventory, not a claim that each variant has a
# runnable backend or a successful proof. See verification-integrations.a2ml
# for the assessed roles of selected tools outside and within this enum.
#
# SYNC SOURCE-OF-TRUTH: `pub enum ProverKind` in
# crates/echidna-core/src/prover_kind.rs.
# If that enum changes, regenerate with scripts/gen-provers-a2ml.sh.

[metadata]
version = "1.0.0"
source  = "crates/echidna-core/src/prover_kind.rs::ProverKind"
HEADER

# Emitted outside the quoted heredoc so it is evaluated at run time rather
# than frozen at authoring time. The comment block above contains backticks,
# so the heredoc itself must stay quoted (no command substitution).
printf 'date    = "%s"\n' "$(date -u +%F)"
printf "count   = %d\n\n" "$(wc -l < "$VARIANT_LIST")"

while IFS= read -r variant; do
  # snake_case: lowercase + insert underscore before uppercase letter that
  # follows a lowercase letter, and before uppercase letter that starts
  # an all-caps cluster preceded by lowercase.
  slug=$(echo "$variant" | sed -E 's/([a-z0-9])([A-Z])/\1_\2/g; s/([A-Z]+)([A-Z][a-z])/\1_\2/g' | tr '[:upper:]' '[:lower:]')
  echo "[prover.${variant}]"
  echo "slug = \"${slug}\""
  echo ""
done < "$VARIANT_LIST"
