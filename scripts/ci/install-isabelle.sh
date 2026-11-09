#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# install-isabelle.sh — install the pinned Isabelle release into
# /opt/isabelle and link /usr/local/bin/isabelle. Used by every workflow
# that needs Isabelle (live-provers T2, verification-proofs-cron), so the
# version, digest and mirrors live in one place.
#
# Why the mirror list: the upstream `dist/` path holds only the current
# release, so a pinned release 404s once the next one ships (weekly
# Isabelle/HOL, 2026-11-09). isabelle.in.tum.de has also redirected to an
# http:// mirror, which `--proto-redir =https` refuses (T2 nightly). Each
# release stays published under `website-<release>/dist/`. Every candidate
# is fetched over https only, and the tarball must match the pinned
# SHA-256 whichever host served it.
#
# Exit codes: 0 installed and `isabelle version` ran, 1 no mirror served the
# pinned tarball, or the install failed.
set -euo pipefail

RELEASE=Isabelle2025-2
SHA256=a20a507bc7c1270d8be96a9f3fbec06345387789d2dc2c4d3df6260d47bfb33c
TARBALL="${RELEASE}_linux.tar.gz"
MIRRORS=(
  "https://isabelle.in.tum.de/website-${RELEASE}/dist/${TARBALL}"
  "https://www.cl.cam.ac.uk/research/hvg/Isabelle/website-${RELEASE}/dist/${TARBALL}"
  "https://isabelle.sketis.net/website-${RELEASE}/dist/${TARBALL}"
  "https://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/${TARBALL}"
  "https://isabelle.in.tum.de/dist/${TARBALL}"
)

dest="${RUNNER_TEMP:-/tmp}/${TARBALL}"
fetched=""
for url in "${MIRRORS[@]}"; do
  echo "install-isabelle: trying $url"
  rm -f "$dest"
  if curl --proto '=https' --proto-redir '=https' -fL --connect-timeout 20 --max-time 420 \
       --retry 2 --retry-delay 10 --retry-max-time 420 --retry-all-errors -o "$dest" "$url" \
     && printf '%s  %s\n' "$SHA256" "$dest" | sha256sum --check --status; then
    fetched="$url"
    break
  fi
  echo "install-isabelle: $url did not serve the pinned tarball" >&2
done
if [ -z "$fetched" ]; then
  echo "::error::install-isabelle: no mirror served ${TARBALL} with SHA-256 ${SHA256}" >&2
  exit 1
fi
echo "install-isabelle: ${TARBALL} from $fetched (SHA-256 verified)"

sudo mkdir -p /opt/isabelle
sudo tar xzf "$dest" -C /opt/isabelle
sudo ln -sf "/opt/isabelle/${RELEASE}/bin/isabelle" /usr/local/bin/isabelle
rm -f "$dest"
isabelle version
