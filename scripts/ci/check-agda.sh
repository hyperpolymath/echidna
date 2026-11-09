#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell
# Check the real corpus and require a fresh interface for each full source path.
set -euo pipefail

if ! command -v agda >/dev/null 2>&1 || [[ ! -f "${AGDA_LIBRARIES_FILE:-}" ]]; then
  echo "::error::Pinned Agda setup is missing; proof check NOT RUN"
  exit 2
fi
version=$(agda --version)
if [[ "$version" != "Agda version 2.7.0.1" ]]; then
  echo "::error::Unexpected compiler: $version; proof check NOT RUN"
  exit 2
fi

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
cd -- "${1:-$repo_root/meta-checker}"
# No interface from a previous attempt may establish current-run coverage.
find . -type f -name '*.agdai' -delete
# PROOF-POLICY §2.1: do not weaken these flags. UnsupportedIndexedMatch
# warnings describe the existing cubical-transport limitation (PROOF-STATUS R4).
agda --no-default-libraries --library-file "$AGDA_LIBRARIES_FILE" \
  --safe --without-K --cubical-compatible src/Echidna/MetaChecker.agda

missing=0
total=0
while IFS= read -r -d '' source; do
  total=$((total + 1))
  interface="_build/2.7.0.1/agda/${source%.agda}.agdai"
  if [[ ! -f "$interface" ]]; then
    echo "::error::$source produced no interface — module is outside the checked closure"
    missing=$((missing + 1))
  fi
done < <(find src -type f -name '*.agda' -print0)
echo "$total source modules, $((total - missing)) with fresh interfaces"
[[ "$total" -gt 0 && "$missing" -eq 0 ]]
bash "$repo_root/scripts/ci/check-receipt-controls.sh"
