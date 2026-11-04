#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)
# Shared, digest-verified installer for the repository's pinned Lean toolchain.
set -euo pipefail
[[ $# == 0 ]] || { echo 'usage: install-lean.sh' >&2; exit 2; }
[[ $(uname -s) == Linux && $(uname -m) == x86_64 ]] || {
  echo 'The qualified elan asset is for x86_64 Linux only' >&2; exit 2;
}
readonly elan_version=v4.2.4
readonly elan_sha256=42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63
readonly lean_toolchain=leanprover/lean4:v4.13.0
readonly https_protocol='=https'
installer_dir=$(mktemp -d)
trap 'rm -rf -- "$installer_dir"' EXIT
curl --fail --silent --show-error --location \
  --proto "$https_protocol" --proto-redir "$https_protocol" \
  --connect-timeout 20 --max-time 120 --retry 3 --retry-max-time 300 \
  -o "$installer_dir/elan.tar.gz" \
  "https://github.com/leanprover/elan/releases/download/${elan_version}/elan-x86_64-unknown-linux-gnu.tar.gz"
printf '%s  %s\n' "$elan_sha256" "$installer_dir/elan.tar.gz" | sha256sum -c -
tar --no-same-owner -xzf "$installer_dir/elan.tar.gz" -C "$installer_dir"
export ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
"$installer_dir/elan-init" -y --no-modify-path --default-toolchain "$lean_toolchain"
"$ELAN_HOME/bin/lean" --version
