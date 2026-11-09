#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# stopgap-apply.sh — apply and verify the containment stopgap on the
# api.nesy-prover.dev host (owner ruling 2026-11-05; README.adoc,
# "Containment stopgap"). Run as the `deploy` user on the host.
#
#   stopgap-apply.sh apply DIR   install DIR/Caddyfile and DIR/echidna.container,
#                                then restart and verify
#   stopgap-apply.sh verify      verify only (safe to run from any shell)
#
# It fails closed: every step that cannot be confirmed stops the run before
# anything restarts. It refuses to act unless exactly one install layout is
# present. The image the container was running is recorded in a state file,
# so `verify` works from a new shell.
#
# Overridable for testing or unusual hosts: ECHIDNA_API, QUADLET_DIR,
# CADDY_DIR, STATE_FILE, HEALTH_WAIT (seconds).
set -euo pipefail

IMAGE=ghcr.io/hyperpolymath/echidna:latest
API=${ECHIDNA_API:-https://api.nesy-prover.dev}
QUADLET_DIR=${QUADLET_DIR:-$HOME/.config/containers/systemd}
CADDY_DIR=${CADDY_DIR:-/opt/echidna}
STATE_FILE=${STATE_FILE:-${XDG_STATE_HOME:-$HOME/.local/state}/echidna/stopgap-running-image}
HEALTH_WAIT=${HEALTH_WAIT:-60}

die() { echo "stopgap: FAIL: $*" >&2; exit 1; }
ok()  { echo "stopgap: ok: $*"; }

# Exactly one of the two layouts must be installed; both or neither means
# the host is not in a state this procedure understands.
layout() {
  local q=0 a=0
  systemctl --user cat echidna.service caddy.service >/dev/null 2>&1 && q=1
  systemctl --user cat container-echidna.service container-caddy.service >/dev/null 2>&1 && a=1
  [ $((q + a)) -eq 1 ] || die "expected exactly one install layout, found quadlet=$q appendix=$a"
  if [ "$q" -eq 1 ]; then echo quadlet; else echo appendix; fi
}

running_image() {
  local id
  id=$(podman container inspect echidna --format '{{.Image}}') || die "cannot inspect the echidna container"
  [ -n "$id" ] || die "the echidna container reports no image"
  printf '%s\n' "$id"
}

# Record the image the container runs, and make :latest point at it, so a
# restart under Pull=never starts the same image.
record_and_pin() {
  local running tagged
  running=$(running_image)
  mkdir -p "$(dirname "$STATE_FILE")"
  printf '%s\n' "$running" > "$STATE_FILE"
  ok "recorded running image $running in $STATE_FILE"
  tagged=$(podman image inspect --format '{{.Id}}' "$IMAGE") || die "cannot inspect $IMAGE"
  if [ "$tagged" != "$running" ]; then
    podman tag "$running" "$IMAGE" || die "cannot re-point $IMAGE at the running image"
    tagged=$(podman image inspect --format '{{.Id}}' "$IMAGE") || die "cannot re-inspect $IMAGE"
    [ "$tagged" = "$running" ] || die "$IMAGE still does not resolve to the running image"
    ok "re-pointed $IMAGE at the running image"
  fi
}

http_code() {
  curl -s -o /dev/null -w '%{http_code}' --max-time 20 "$@" || true
}

verify() {
  [ -s "$STATE_FILE" ] || die "no recorded image in $STATE_FILE; run 'apply' first"
  local want now code waited=0
  want=$(cat "$STATE_FILE")
  now=$(running_image)
  [ "$now" = "$want" ] || die "container runs $now, recorded image was $want"
  ok "same image ($now)"

  if systemctl --user is-enabled podman-auto-update.timer >/dev/null 2>&1; then
    die "podman-auto-update.timer is still enabled"
  fi
  ok "auto-update timer disabled"

  # Caddy can take a few seconds after a restart.
  while :; do
    code=$(http_code "$API/api/health")
    [ "$code" = 200 ] && break
    [ "$waited" -ge "$HEALTH_WAIT" ] && die "/api/health returned $code, expected 200"
    sleep 5; waited=$((waited + 5))
  done
  ok "/api/health 200"

  code=$(http_code -X POST "$API/api/verify")
  [ "$code" = 403 ] || die "POST /api/verify returned $code, expected 403 (execution must be refused)"
  ok "POST /api/verify 403"
  echo "stopgap: PASS"
}

apply() {
  local src=${1:?usage: stopgap-apply.sh apply DIR}
  if [ ! -f "$src/Caddyfile" ] || [ ! -f "$src/echidna.container" ]; then
    die "$src must contain Caddyfile and echidna.container"
  fi
  grep -q '^Pull=never$' "$src/echidna.container" \
    || die "$src/echidna.container is not the stopgap version (no Pull=never)"
  grep -q '^AutoUpdate=' "$src/echidna.container" \
    && die "$src/echidna.container still sets AutoUpdate"
  grep -q '@public' "$src/Caddyfile" \
    || die "$src/Caddyfile is not the stopgap version (no @public matcher)"

  local l
  l=$(layout)
  ok "layout: $l"

  if systemctl --user list-unit-files podman-auto-update.timer >/dev/null 2>&1; then
    systemctl --user disable --now podman-auto-update.timer || die "cannot disable podman-auto-update.timer"
  fi
  record_and_pin

  install -m 0644 "$src/Caddyfile" "$CADDY_DIR/Caddyfile" || die "cannot install the Caddyfile"
  if [ "$l" = quadlet ]; then
    install -m 0644 "$src/echidna.container" "$QUADLET_DIR/echidna.container" \
      || die "cannot install echidna.container"
    systemctl --user daemon-reload || die "daemon-reload failed"
    systemctl --user restart echidna caddy || die "restart failed"
  else
    # Appendix containers carry no auto-update label, and their
    # `generate systemd --new` units do not pull an image already present.
    systemctl --user restart container-caddy || die "restart failed"
  fi
  ok "installed and restarted ($l)"
  verify
}

case "${1:-}" in
  apply)  shift; apply "$@" ;;
  verify) verify ;;
  *) echo "usage: $0 apply DIR | verify" >&2; exit 2 ;;
esac
