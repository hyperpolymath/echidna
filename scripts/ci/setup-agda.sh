#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell
# Pinned upstream binaries: no cold GHC bootstrap and no cached proof results.
set -Eeuo pipefail
trap 'echo "::error::Agda setup did not complete; proof check NOT RUN"; exit 2' ERR

if [[ "$(uname -s)" != Linux || "$(uname -m)" != x86_64 ]]; then
  echo "::error::The pinned Agda distribution supports Linux x86_64; proof check NOT RUN"
  exit 2
fi

agda_version=2.7.0.1
stdlib_version=2.1
cache_dir="${AGDA_ARCHIVE_CACHE:-${HOME}/.cache/echidna/agda}"
mkdir -p "$cache_dir"
toolchain_dir=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/echidna-agda.XXXXXX")
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)

fetch_verified() {
  local url=$1 archive=$2 digest=$3
  if [[ -f "$archive" ]] && ! printf '%s  %s\n' "$digest" "$archive" | sha256sum --check --status; then
    echo "::warning::Discarding a corrupt cached archive: ${archive##*/}"
    rm -- "$archive"
  fi
  if [[ ! -f "$archive" ]]; then
    curl --fail --location --retry 3 --output "$archive.download" "$url"
    printf '%s  %s\n' "$digest" "$archive.download" | sha256sum --check
    mv -- "$archive.download" "$archive"
  fi
  # Recheck warm restores too: a cache hit alone never authenticates a compiler.
  printf '%s  %s\n' "$digest" "$archive" | sha256sum --check
}

agda_archive="$cache_dir/Agda-v${agda_version}-linux.tar.xz"
stdlib_archive="$cache_dir/agda-stdlib-${stdlib_version}.tar.gz"
fetch_verified \
  "https://github.com/agda/agda/releases/download/v${agda_version}/Agda-v${agda_version}-linux.tar.xz" \
  "$agda_archive" 975b515a14877ab6bce5bfc641e16c4a3ee52ca5d7f846577dee80aa2145db8a
fetch_verified \
  "https://github.com/agda/agda-stdlib/archive/refs/tags/v${stdlib_version}.tar.gz" \
  "$stdlib_archive" 72ca3ea25094efa0439e106f0d949330414232ec4cc5c3c3316e7e70dd06d431

tar --no-same-owner -xJf "$agda_archive" -C "$toolchain_dir"
tar --no-same-owner -xzf "$stdlib_archive" -C "$toolchain_dir"
agda_dir="$toolchain_dir/Agda-v${agda_version}"
libraries="$toolchain_dir/libraries"
printf '%s\n' \
  "$toolchain_dir/agda-stdlib-${stdlib_version}/standard-library.agda-lib" \
  "$repo_root/meta-checker/echidna-meta.agda-lib" > "$libraries"
"$agda_dir/bin/agda" --version

if [[ -n "${GITHUB_ENV:-}" && -n "${GITHUB_PATH:-}" ]]; then
  {
    printf 'Agda_datadir=%s\n' "$agda_dir/data"
    printf 'AGDA_LIBRARIES_FILE=%s\n' "$libraries"
    printf 'LC_ALL=C.UTF-8\n'
  } >> "$GITHUB_ENV"
  printf '%s\n' "$agda_dir/bin" >> "$GITHUB_PATH"
fi
printf 'Agda data: %s\nLibraries: %s\nExecutable: %s\n' \
  "$agda_dir/data" "$libraries" "$agda_dir/bin/agda"
