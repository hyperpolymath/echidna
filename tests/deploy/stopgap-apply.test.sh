#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# Tests deploy/hetzner/stopgap-apply.sh against stub podman, systemctl and
# curl commands. No host, container or network is touched.
set -uo pipefail

ROOT=$(cd "$(dirname "$0")/../.." && pwd)
SCRIPT=$ROOT/deploy/hetzner/stopgap-apply.sh
pass=0; fail=0

new_case() {
  T=$(mktemp -d)
  mkdir -p "$T/bin" "$T/quadlet" "$T/caddy" "$T/src"
  cp "$ROOT/deploy/hetzner/Caddyfile" "$ROOT/deploy/hetzner/echidna.container" "$T/src/"
  : > "$T/log"
  # Stub knobs (files under $T/knob/<name>), read by the stubs at call time.
  mkdir -p "$T/knob"
  echo sha-running > "$T/knob/running"      # image the container runs
  echo sha-running > "$T/knob/tagged"       # image :latest resolves to
  echo quadlet > "$T/knob/layout"           # quadlet | appendix | both | none
  echo 200 > "$T/knob/health"
  echo 403 > "$T/knob/verify"
  echo no > "$T/knob/timer_enabled"
  echo ok > "$T/knob/inspect"               # ok | fail

  cat > "$T/bin/podman" <<'EOF'
#!/usr/bin/env bash
K=$STUB/knob; echo "podman $*" >> "$STUB/log"
case "$1 $2" in
  "container inspect") [ "$(cat $K/inspect)" = ok ] || exit 125; cat $K/running ;;
  "image inspect") cat $K/tagged ;;
  "tag "*) cat $K/running > $K/tagged ;;
  *) exit 0 ;;
esac
EOF
  cat > "$T/bin/systemctl" <<'EOF'
#!/usr/bin/env bash
K=$STUB/knob; echo "systemctl $*" >> "$STUB/log"
shift  # --user
l=$(cat $K/layout)
case "$1" in
  cat)
    case "$2" in
      echidna.service) [ "$l" = quadlet ] || [ "$l" = both ] ;;
      container-echidna.service) [ "$l" = appendix ] || [ "$l" = both ] ;;
      *) exit 1 ;;
    esac ;;
  is-enabled) [ "$(cat $K/timer_enabled)" = yes ] ;;
  list-unit-files) exit 0 ;;
  disable) echo no > $K/timer_enabled ;;
  *) exit 0 ;;
esac
EOF
  cat > "$T/bin/curl" <<'EOF'
#!/usr/bin/env bash
K=$STUB/knob; echo "curl $*" >> "$STUB/log"
case "$*" in
  *api/health*) printf %s "$(cat $K/health)" ;;
  *api/verify*) printf %s "$(cat $K/verify)" ;;
esac
EOF
  chmod +x "$T/bin/"*
}

run() {  # run SCRIPT ARGS with the stubs; output in $T/out, status in $rc
  env PATH="$T/bin:$PATH" STUB="$T" QUADLET_DIR="$T/quadlet" CADDY_DIR="$T/caddy" \
      STATE_FILE="$T/state/image" HEALTH_WAIT=0 ECHIDNA_API=https://api.test \
      bash "$SCRIPT" "$@" > "$T/out" 2>&1
  rc=$?
}

check() {  # check NAME CONDITION...
  local name=$1; shift
  if "$@"; then pass=$((pass + 1)); echo "ok   - $name"
  else fail=$((fail + 1)); echo "FAIL - $name"; sed 's/^/       /' "$T/out"; fi
}
has()    { grep -q -- "$1" "$T/log"; }
hasnt()  { ! grep -q -- "$1" "$T/log"; }

# 1. Quadlet host, happy path.
new_case; echo yes > "$T/knob/timer_enabled"; run apply "$T/src"
check "quadlet apply passes" test $rc -eq 0
check "quadlet apply prints PASS" grep -q 'stopgap: PASS' "$T/out"
check "image recorded" grep -qx sha-running "$T/state/image"
check "Caddyfile installed" cmp -s "$T/src/Caddyfile" "$T/caddy/Caddyfile"
check "unit installed" cmp -s "$T/src/echidna.container" "$T/quadlet/echidna.container"
check "timer disabled" has 'systemctl --user disable --now podman-auto-update.timer'
check "both units restarted" has 'systemctl --user restart echidna caddy'

# 2. Verify later from a fresh shell reads the state file.
run verify
check "verify in a new shell passes" test $rc -eq 0

# 3. Appendix host: only the proxy changes.
new_case; echo appendix > "$T/knob/layout"; run apply "$T/src"
check "appendix apply passes" test $rc -eq 0
check "appendix restarts container-caddy" has 'systemctl --user restart container-caddy'
check "appendix leaves the quadlet dir alone" test ! -e "$T/quadlet/echidna.container"

# 4. Both layouts present: refuse before any change.
new_case; echo both > "$T/knob/layout"; run apply "$T/src"
check "both layouts refused" test $rc -ne 0
check "both layouts: nothing restarted" hasnt 'restart'
check "both layouts: no file installed" test ! -e "$T/caddy/Caddyfile"
check "both layouts: timer untouched" hasnt 'disable'

# 5. Neither layout: refuse.
new_case; echo none > "$T/knob/layout"; run apply "$T/src"
check "no layout refused" test $rc -ne 0
check "no layout: nothing restarted" hasnt 'restart'

# 6. The container cannot be inspected: stop before restarting.
new_case; echo fail > "$T/knob/inspect"; run apply "$T/src"
check "inspect failure refused" test $rc -ne 0
check "inspect failure: nothing restarted" hasnt 'restart'

# 7. :latest has moved: re-point it at the running image first.
new_case; echo sha-other > "$T/knob/tagged"; run apply "$T/src"
check "drifted tag re-pointed" has 'podman tag sha-running ghcr.io/hyperpolymath/echidna:latest'
check "drifted tag apply passes" test $rc -eq 0

# 8. Source files are not the stopgap versions.
new_case; sed -i 's/^Pull=never$/AutoUpdate=registry/' "$T/src/echidna.container"; run apply "$T/src"
check "non-stopgap unit refused" test $rc -ne 0
check "non-stopgap unit: nothing restarted" hasnt 'restart'
new_case; sed -i 's/@public/@open/g' "$T/src/Caddyfile"; run apply "$T/src"
check "non-stopgap Caddyfile refused" test $rc -ne 0

# 9. Verification failures.
new_case; run apply "$T/src"; echo 200 > "$T/knob/verify"; run verify
check "execution not refused fails verify" test $rc -ne 0
new_case; run apply "$T/src"; echo 502 > "$T/knob/health"; run verify
check "unhealthy API fails verify" test $rc -ne 0
new_case; run apply "$T/src"; echo sha-new > "$T/knob/running"; run verify
check "changed image fails verify" test $rc -ne 0
new_case; run apply "$T/src"; echo yes > "$T/knob/timer_enabled"; run verify
check "re-enabled timer fails verify" test $rc -ne 0
new_case; run verify
check "verify without a recorded image fails" test $rc -ne 0

echo "# $pass passed, $fail failed"
[ "$fail" -eq 0 ]
