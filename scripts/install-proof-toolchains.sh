#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
#
# install-proof-toolchains.sh — self-provision the formal-proof toolchains that
# ECHIDNA's proof corpus is checked with: Idris2, Agda (+stdlib), Coq, Lean 4.
#
# Idempotent: re-running skips already-present components in well under a second,
# so it is safe to invoke from a SessionStart hook. The first run on a cold
# container takes ~30 min (almost all of it the Idris2 source bootstrap).
#
# Target: Ubuntu 24.04 (the Claude-on-web / GitHub-Actions base). On any other
# host, or without root, it prints a note and exits 0 rather than breaking the
# session.
set -euo pipefail

LEAN_VERSION="4.13.0"
IDRIS2_VERSION="v0.8.0"
LEAN_PREFIX="/opt/lean-${LEAN_VERSION}-linux"

log() { printf '\033[1;36m[proof-setup]\033[0m %s\n' "$*"; }
have() { command -v "$1" >/dev/null 2>&1; }

# ── Guards: only provision where it makes sense ──────────────────────────────
if [ "$(id -u)" != "0" ] && ! have sudo; then
  log "not root and no sudo — skipping (provision manually if proofs are needed)"; exit 0
fi
SUDO=""; [ "$(id -u)" = "0" ] || SUDO="sudo"
if ! have apt-get; then
  log "no apt-get (not Debian/Ubuntu) — skipping"; exit 0
fi

# Fast exit when everything is already present.
if have idris2 && have agda && have coqc && [ -x "${LEAN_PREFIX}/bin/lean" ]; then
  log "all proof toolchains already present — nothing to do"; exit 0
fi

# ── 1. APT base: agda, coq, chezscheme (for the Idris2 bootstrap), build deps ─
if ! have agda || ! have coqc || ! have chezscheme; then
  log "apt: disabling 403'ing third-party PPAs, then installing toolchains"
  for f in /etc/apt/sources.list.d/deadsnakes-*.sources /etc/apt/sources.list.d/ondrej-*.sources; do
    [ -f "$f" ] && $SUDO mv "$f" "$f.disabled" 2>/dev/null || true
  done
  $SUDO apt-get update -qq
  $SUDO apt-get install -y --no-install-recommends \
    agda agda-stdlib coq chezscheme zstd build-essential libgmp-dev curl ca-certificates git
fi

# ── 2. Register agda-stdlib (Debian ships sources but no library registration) ─
STDLIB_LIB=/usr/share/agda-stdlib/standard-library.agda-lib
if [ -d /usr/share/agda-stdlib ] && [ ! -f "$STDLIB_LIB" ]; then
  log "registering agda-stdlib"
  printf 'name: standard-library\ninclude: .\n' | $SUDO tee "$STDLIB_LIB" >/dev/null
fi
mkdir -p "$HOME/.agda"
grep -qxF "$STDLIB_LIB" "$HOME/.agda/libraries" 2>/dev/null || echo "$STDLIB_LIB" >> "$HOME/.agda/libraries"
grep -qxF 'standard-library' "$HOME/.agda/defaults" 2>/dev/null || echo 'standard-library' >> "$HOME/.agda/defaults"
# Agda errors on Unicode identifiers (ℕ, ≤, …) under a C locale — always run it
# as: LC_ALL=C.UTF-8 agda <file>.agda
log "reminder: invoke agda with LC_ALL=C.UTF-8"

# ── 3. Lean 4 (pinned tarball; the elan host 403s under the network policy) ───
if [ ! -x "${LEAN_PREFIX}/bin/lean" ]; then
  log "installing Lean ${LEAN_VERSION}"
  curl -fsSL "https://github.com/leanprover/lean4/releases/download/v${LEAN_VERSION}/lean-${LEAN_VERSION}-linux.tar.zst" -o /tmp/lean.tar.zst
  $SUDO tar --use-compress-program=unzstd -xf /tmp/lean.tar.zst -C /opt
fi
for b in lean lake; do $SUDO ln -sf "${LEAN_PREFIX}/bin/$b" /usr/local/bin/"$b"; done

# ── 4. Idris2 0.8.0 (not packaged; bootstrap from source via Chez, ~10 min) ───
if ! have idris2; then
  log "building Idris2 ${IDRIS2_VERSION} from source — this is the slow step"
  curl -fsSL "https://github.com/idris-lang/Idris2/archive/refs/tags/${IDRIS2_VERSION}.tar.gz" -o /tmp/idris2.tar.gz
  rm -rf /tmp/idris2-src && mkdir -p /tmp/idris2-src
  tar xzf /tmp/idris2.tar.gz -C /tmp/idris2-src --strip-components=1
  ( cd /tmp/idris2-src \
      && make bootstrap SCHEME=chezscheme \
      && $SUDO make install PREFIX=/usr/local \
      && $SUDO make install-with-src-libs PREFIX=/usr/local )
fi

# ── 5. Report ────────────────────────────────────────────────────────────────
log "installed versions:"
{ idris2 --version; agda --version; coqc --version | head -1; "${LEAN_PREFIX}/bin/lean" --version; } 2>/dev/null | sed 's/^/  /' || true
log "proof toolchains ready (lteLit helper lives in verification/proofs/idris2/NatLte.idr)."

# ── SOLVERS (maximal-scope stage) ────────────────────────────────────────────
# The solver corpus (proofs/{tptp,z3,cvc5,dimacs,acl2,hol_light,mizar,fstar})
# is provisioned by a sibling install-solvers.sh: z3/cvc5/eprover/vampire/spass/
# glpk/minizinc are cheap (apt + GitHub-release binaries); acl2/hol-light/mizar
# are heavy source builds. Added when that stage begins.
