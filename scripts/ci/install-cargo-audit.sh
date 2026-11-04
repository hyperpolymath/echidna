#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell
# Use the upstream release binary instead of rebuilding cargo-audit in every job.
set -euo pipefail
trap 'echo "::error::cargo-audit setup failed; dependency audit NOT RUN"; exit 2' ERR

if [[ "$(uname -s)" != Linux || "$(uname -m)" != x86_64 ]]; then
  echo "::error::The pinned cargo-audit distribution supports Linux x86_64; audit NOT RUN"
  exit 2
fi
tool_dir=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/echidna-cargo-audit.XXXXXX")
archive="$tool_dir/cargo-audit.tgz"
curl --fail --location --retry 3 --output "$archive" \
  https://github.com/rustsec/rustsec/releases/download/cargo-audit/v0.22.2/cargo-audit-x86_64-unknown-linux-musl-v0.22.2.tgz
printf '%s  %s\n' \
  7fb9497f8594b389e5fce5ef9b92db08432996895b2e0c5a0167a69ed445c428 \
  "$archive" | sha256sum --check
tar --no-same-owner -xzf "$archive" -C "$tool_dir"
install_dir="$tool_dir/cargo-audit-x86_64-unknown-linux-musl-v0.22.2"
"$install_dir/cargo-audit" --version
if [[ -n "${GITHUB_PATH:-}" ]]; then
  printf '%s\n' "$install_dir" >> "$GITHUB_PATH"
fi
printf 'cargo-audit executable: %s\n' "$install_dir/cargo-audit"
