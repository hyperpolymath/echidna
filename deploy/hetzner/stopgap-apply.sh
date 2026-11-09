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
AUTO_UPDATE_SERVICE=podman-auto-update.service

# The containment policy. The Caddyfile check and the live probe both test
# against these, so the file and the running proxy are held to one policy.
PUBLIC_METHOD='method GET HEAD'
PUBLIC_PATH='path /api/health /api/provers'
DENY_STATUS=403
# Execution routes (src/rust/server.rs), a public path under a method the
# matcher does not admit, and a route the server does not have. Every one
# must be answered DENY_STATUS by Caddy.
DENIED_PROBES=(
  "POST /api/prove"
  "POST /api/verify"
  "POST /api/verify_raw"
  "POST /api/verify_parallel"
  "POST /api/suggest"
  "POST /api/session/create"
  "POST /api/agent/plan"
  "GET /api/search"
  "POST /api/health"
  "GET /api/stopgap-probe-unknown-route"
)

die() { echo "stopgap: FAIL: $*" >&2; exit 1; }
ok()  { echo "stopgap: ok: $*"; }

# Print a unit file's directives as "[Section] Key=Value", normalised the
# way systemd reads them: leading and trailing whitespace and whitespace
# around the first `=` dropped, blank lines and `#`/`;` comments skipped.
# Lines it cannot normalise are printed with a leading `!`.
unit_directives() {
  awk '
    { line = $0; sub(/\r$/, "", line); sub(/^[ \t]+/, "", line); sub(/[ \t]+$/, "", line) }
    line == "" || line ~ /^[#;]/ { next }
    line ~ /^\[.*\]$/ { section = line; next }
    line ~ /\\$/ { print "!line continuation: " line; next }
    {
      i = index(line, "=")
      if (i == 0) { print "!not a directive: " line; next }
      k = substr(line, 1, i - 1); v = substr(line, i + 1)
      sub(/[ \t]+$/, "", k); sub(/^[ \t]+/, "", v)
      print section " " k "=" v
    }' "$1"
}

# Refuse a unit that is not the stopgap version: exactly one Image= naming
# IMAGE, exactly one Pull=never, and no auto-update in any spelling.
check_unit() {
  local f=$1 d
  d=$(unit_directives "$f") || die "cannot read $f"
  if grep -q '^!' <<<"$d"; then
    die "$f has lines this check cannot normalise: $(grep -m1 '^!' <<<"$d")"
  fi
  if grep -q '^\[[^]]*\] AutoUpdate=' <<<"$d"; then
    die "$f still sets AutoUpdate"
  fi
  if grep -qi 'io\.containers\.autoupdate' <<<"$d"; then
    die "$f still sets the io.containers.autoupdate label"
  fi
  [ "$(grep '^\[Container\] Pull=' <<<"$d" || true)" = "[Container] Pull=never" ] \
    || die "$f is not the stopgap version (needs exactly one Pull=never in [Container])"
  [ "$(grep '^\[Container\] Image=' <<<"$d" || true)" = "[Container] Image=$IMAGE" ] \
    || die "$f must set exactly one Image=$IMAGE in [Container]"
  ok "$f: Image=$IMAGE, Pull=never, no auto-update"
}

# Refuse a Caddyfile that is not the stopgap shape. The proxy image carries
# a plugin (rate_limit) that a stock `caddy adapt` does not know, and caddy
# is not installed on the host outside that image, so this is a structural
# check of the Caddyfile text rather than of adapted JSON. It requires:
#   - exactly one `@public` matcher, whose body is exactly PUBLIC_METHOD and
#     PUBLIC_PATH, and no other named matcher;
#   - exactly one `reverse_proxy`, the only child of `handle @public`;
#   - exactly one catch-all `handle`, a sibling of `handle @public`, whose
#     only child is `respond ... DENY_STATUS`, and no other `handle`;
#   - none of the directives that re-route or reshape a request (import,
#     invoke, handle_path, rewrite, uri, method, php_fastcgi, forward_auth),
#     except `method` as the @public matcher's own line.
check_caddyfile() {
  local f=$1 problems
  problems=$(awk -v want_method="$PUBLIC_METHOD" -v want_path="$PUBLIC_PATH" -v deny="$DENY_STATUS" '
    function fail(msg) { print msg; bad = 1 }
    {
      line = $0
      sub(/\r$/, "", line)
      sub(/^[ \t]*#.*$/, "", line)       # whole-line comment
      sub(/[ \t]#.*$/, "", line)         # trailing comment
      gsub(/[ \t]+/, " ", line); sub(/^ /, "", line); sub(/ $/, "", line)
      if (line == "") next

      if (line == "}") {
        if (depth == 0) { fail("unbalanced closing brace"); next }
        h = hdr[depth]
        if (h == "@public {" && !(nkid[depth] == 2 && (kids[depth] == "|" want_method "|" want_path || kids[depth] == "|" want_path "|" want_method)))
          fail("@public must contain exactly \"" want_method "\" and \"" want_path "\"")
        if (h == "handle @public {" && !(nkid[depth] == 1 && kids[depth] ~ /^\|reverse_proxy /))
          fail("handle @public must contain only reverse_proxy")
        if (h == "handle {" && !(nkid[depth] == 1 && kids[depth] ~ ("^\\|respond( .*)? " deny "$")))
          fail("the catch-all handle must contain only respond ... " deny)
        depth--
        next
      }

      probe = line
      gsub(/\{[^{} ]+\}/, "", probe)     # placeholders such as {remote_host}
      opens = 0
      if (probe == "{") { opens = 1; probe = "" }
      else if (probe ~ / \{$/) { opens = 1; sub(/ \{$/, "", probe) }
      if (probe ~ /[{}]/) { fail("unsupported brace layout: " line); next }

      split(line, w, " "); d = w[1]
      parent = depth ? hdr[depth] : ""
      pid = depth ? id[depth] : 0
      if (depth) { nkid[depth]++; kids[depth] = kids[depth] "|" line }

      if (d ~ /^(import|invoke|handle_path|rewrite|uri|php_fastcgi|forward_auth)$/)
        fail("directive not allowed in the stopgap Caddyfile: " line)
      if (d == "method" && parent != "@public {")
        fail("method is allowed only inside @public: " line)
      if (d ~ /^@/) {
        if (line == "@public {") npublic++
        else fail("only the @public matcher may be defined: " line)
      }
      if (d == "reverse_proxy") {
        nproxy++
        if (parent != "handle @public {") fail("reverse_proxy outside handle @public: " line)
      }
      if (d == "handle") {
        if (line == "handle @public {") { npubh++; pubh_parent = pid }
        else if (line == "handle {") { ndenyh++; denyh_parent = pid }
        else fail("handle other than \"handle @public\" and the catch-all: " line)
      }

      if (opens) { depth++; hdr[depth] = line; id[depth] = ++nblocks; nkid[depth] = 0; kids[depth] = "" }
    }
    END {
      if (depth != 0) fail("unbalanced opening brace")
      if (npublic != 1) fail("expected one @public matcher, found " npublic + 0)
      if (nproxy != 1) fail("expected one reverse_proxy, found " nproxy + 0)
      if (npubh != 1) fail("expected one handle @public, found " npubh + 0)
      if (ndenyh != 1) fail("expected one catch-all handle, found " ndenyh + 0)
      if (npubh == 1 && ndenyh == 1 && pubh_parent != denyh_parent)
        fail("handle @public and the catch-all handle must be siblings")
      exit bad
    }' "$f") || die "$f is not the stopgap Caddyfile: ${problems//$'\n'/; }"
  ok "$f: forwards only @public ($PUBLIC_METHOD; $PUBLIC_PATH), everything else $DENY_STATUS"
}

# Exactly one of the two layouts must be installed; both or neither means
# the host is not in a state this procedure understands.
layout() {
  local q=0 a=0
  systemctl --user cat echidna.service caddy.service >/dev/null 2>&1 && q=1
  systemctl --user cat container-echidna.service container-caddy.service >/dev/null 2>&1 && a=1
  [ $((q + a)) -eq 1 ] || die "expected exactly one install layout, found quadlet=$q appendix=$a"
  if [ "$q" -eq 1 ]; then echo quadlet; else echo appendix; fi
}

# Confirm no podman-auto-update run is in progress. A run started before the
# timer was disabled can still pull, retag and restart. `is-active` prints
# `inactive` for a unit that does not exist; anything other than inactive
# or failed (active, activating, deactivating, reloading, no answer) refuses.
auto_update_idle() {
  local state
  state=$(systemctl --user is-active "$AUTO_UPDATE_SERVICE" 2>/dev/null || true)
  case "$state" in
    inactive|failed) ok "$AUTO_UPDATE_SERVICE is $state" ;;
    *) die "$AUTO_UPDATE_SERVICE is '${state:-unknown}', expected inactive" ;;
  esac
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
  local want now code probe method path waited=0
  want=$(cat "$STATE_FILE")
  now=$(running_image)
  [ "$now" = "$want" ] || die "container runs $now, recorded image was $want"
  ok "same image ($now)"

  if systemctl --user is-enabled podman-auto-update.timer >/dev/null 2>&1; then
    die "podman-auto-update.timer is still enabled"
  fi
  ok "auto-update timer disabled"
  auto_update_idle

  # Caddy can take a few seconds after a restart.
  while :; do
    code=$(http_code -X GET "$API/api/health")
    [ "$code" = 200 ] && break
    [ "$waited" -ge "$HEALTH_WAIT" ] && die "GET /api/health returned $code, expected 200"
    sleep 5; waited=$((waited + 5))
  done
  ok "GET /api/health 200"

  for probe in "${DENIED_PROBES[@]}"; do
    method=${probe%% *}; path=${probe#* }
    code=$(http_code -X "$method" "$API$path")
    [ "$code" = "$DENY_STATUS" ] \
      || die "$method $path returned $code, expected $DENY_STATUS (execution must be refused)"
    ok "$method $path $DENY_STATUS"
  done
  echo "stopgap: PASS"
}

apply() {
  local src=${1:?usage: stopgap-apply.sh apply DIR}
  if [ ! -f "$src/Caddyfile" ] || [ ! -f "$src/echidna.container" ]; then
    die "$src must contain Caddyfile and echidna.container"
  fi
  check_unit "$src/echidna.container"
  check_caddyfile "$src/Caddyfile"

  local l
  l=$(layout)
  ok "layout: $l"

  if systemctl --user list-unit-files podman-auto-update.timer >/dev/null 2>&1; then
    systemctl --user disable --now podman-auto-update.timer || die "cannot disable podman-auto-update.timer"
  fi
  # Disabling the timer does not end a run it already started. Stop that
  # run and confirm it is gone before the image is recorded and pinned.
  # The stop result is not trusted on its own (it fails for a unit that does
  # not exist); the state check after it is the gate.
  systemctl --user stop "$AUTO_UPDATE_SERVICE" >/dev/null 2>&1 || true
  auto_update_idle
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
