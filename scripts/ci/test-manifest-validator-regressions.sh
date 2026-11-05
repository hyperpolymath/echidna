#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell
# Keep full-body checks and DEED identity/version rules when scanning large corpora.
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)
validator="$repo_root/.github/hooks/validate-a2ml.sh"
fixtures=$(mktemp -d)
trap 'rm -rf -- "$fixtures"' EXIT

run_case() {
  local name=$1 expected=$2 diagnostic=$3 result=0
  INPUT_PATH="$fixtures/$name" INPUT_STRICT=true \
    bash "$validator" > "$fixtures/$name.log" 2>&1 || result=$?
  if [[ "$result" -ne "$expected" ]]; then
    cat "$fixtures/$name.log"
    echo "::error::$name returned $result; expected $expected"
    exit 1
  fi
  if [[ -n "$diagnostic" ]] && ! grep -Fq "$diagnostic" "$fixtures/$name.log"; then
    cat "$fixtures/$name.log"
    echo "::error::$name did not report the intended defect"
    exit 1
  fi
  echo "$name: expected exit $expected"
}

for name in valid-corpus late-heading late-attestation valid-attestation; do
  mkdir -p "$fixtures/$name"
  {
    printf '%s\n' '# SPDX-License-Identifier: MPL-2.0' 'name = "corpus"' 'version = "1"'
    awk 'BEGIN { for (n = 0; n < 5000; n++) print "payload = \"unchanged record\"" }'
  } > "$fixtures/$name/corpus.a2ml"
done
printf '%s\n' '[broken-heading' >> "$fixtures/late-heading/corpus.a2ml"
printf '%s\n' '[attestation]' 'description = "no proof evidence"' >> "$fixtures/late-attestation/corpus.a2ml"
printf '%s\n' '[attestation]' 'proof = "structural fixture only"' >> "$fixtures/valid-attestation/corpus.a2ml"

mkdir -p "$fixtures/valid-deed/machine-readable" "$fixtures/missing-schema/machine-readable" "$fixtures/late-head"
printf '%s\n' '# SPDX-License-Identifier: MPL-2.0' '(estate-atlas-deed' \
  ':schema-version "1.0.0"' ':registry-version "1")' > "$fixtures/valid-deed/machine-readable/ATLAS.deed"
printf '%s\n' '# SPDX-License-Identifier: MPL-2.0' '(estate-atlas-deed' \
  ':registry-version "1")' > "$fixtures/missing-schema/machine-readable/ATLAS.deed"
printf '%s\n' '# SPDX-License-Identifier: MPL-2.0' '(unrelated)' '(estate-deed' \
  ':schema-version "1.0.0")' > "$fixtures/late-head/invalid.deed"

run_case valid-corpus 0 ''
run_case late-heading 1 'Possibly malformed section heading'
run_case late-attestation 1 'Attestation block found but missing'
run_case valid-attestation 0 ''
run_case valid-deed 0 ''
run_case missing-schema 1 'Missing version or schema_version field'
run_case late-head 1 'Missing required identity field'
