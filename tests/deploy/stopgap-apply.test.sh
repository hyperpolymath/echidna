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
  echo 403 > "$T/knob/deny"                 # every other route
  mkdir -p "$T/knob/code"                   # per-route override: code/METHOD_api_path
  echo inactive > "$T/knob/au_state"        # podman-auto-update.service state
  echo no > "$T/knob/au_stuck"              # yes: stop does not end the run

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
  is-active) s=$(cat $K/au_state); echo "$s"; [ "$s" = active ] ;;
  stop) [ "$(cat $K/au_stuck)" = yes ] || echo inactive > $K/au_state ;;
  list-unit-files) exit 0 ;;
  disable) echo no > $K/timer_enabled ;;
  *) exit 0 ;;
esac
EOF
  cat > "$T/bin/curl" <<'EOF'
#!/usr/bin/env bash
K=$STUB/knob; echo "curl $*" >> "$STUB/log"
m=GET; u=
while [ $# -gt 0 ]; do
  case "$1" in
    -X) m=$2; shift 2 ;;
    -o|-w|--max-time) shift 2 ;;
    *://*) u=$1; shift ;;
    *) shift ;;
  esac
done
p=/${u#*://*/}
k=$(printf '%s%s' "$m" "$p" | tr -c 'A-Za-z0-9' _)
if [ -f "$K/code/$k" ]; then printf %s "$(cat "$K/code/$k")"
elif [ "$m $p" = "GET /api/health" ]; then printf %s "$(cat $K/health)"
elif [ "$m $p" = "POST /api/verify" ]; then printf %s "$(cat $K/verify)"
else printf %s "$(cat $K/deny)"; fi
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
nopass() { ! grep -q 'stopgap: PASS' "$T/out"; }

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

# Helpers for the cases below.
code()     { echo "$2" > "$T/knob/code/$1"; }       # code METHOD_api_path STATUS
unit()     { sed -i "$1" "$T/src/echidna.container"; }
caddy()    { sed -i "$1" "$T/src/Caddyfile"; }
untouched() {  # nothing recorded, pinned, installed or restarted
  test ! -e "$T/state/image" && test ! -e "$T/caddy/Caddyfile" \
    && test ! -e "$T/quadlet/echidna.container" && hasnt 'restart' && hasnt 'podman tag'
}
refused() {  # refused NAME: the run failed and changed nothing
  check "$1: refused" test $rc -ne 0
  check "$1: nothing changed" untouched
}

# 10. A podman-auto-update run already in progress (finding 1). Disabling
# the timer does not end it; it must be stopped and confirmed idle before
# the image is recorded.
new_case; echo yes > "$T/knob/timer_enabled"; echo active > "$T/knob/au_state"; run apply "$T/src"
check "running auto-update is stopped" has 'systemctl --user stop podman-auto-update.service'
check "running auto-update: apply passes once stopped" test $rc -eq 0
check "auto-update stopped before the image is recorded" \
  test "$(grep -n 'stop podman-auto-update.service' "$T/log" | cut -d: -f1)" \
    -lt "$(grep -n 'podman container inspect' "$T/log" | head -1 | cut -d: -f1)"
new_case; echo activating > "$T/knob/au_state"; echo yes > "$T/knob/au_stuck"; run apply "$T/src"
refused "auto-update still activating after stop"
new_case; echo active > "$T/knob/au_state"; echo yes > "$T/knob/au_stuck"; run apply "$T/src"
refused "auto-update still active after stop"
new_case; run apply "$T/src"; echo active > "$T/knob/au_state"; run verify
check "active auto-update run fails verify" test $rc -ne 0

# 11. Unit directives are normalised as systemd reads them (finding 2).
new_case; unit '/^Pull=never$/a AutoUpdate = registry'; run apply "$T/src"
refused "AutoUpdate with spaces around ="
new_case; unit '/^Pull=never$/a \  AutoUpdate=registry'; run apply "$T/src"
refused "indented AutoUpdate"
new_case; unit '/^Pull=never$/a PodmanArgs=--label io.containers.autoupdate=registry'; run apply "$T/src"
refused "auto-update label via PodmanArgs"
new_case; unit '/^Pull=never$/a Pull = always'; run apply "$T/src"
refused "second Pull= overriding never"
new_case; unit 's/^Pull=never$/#Pull=never/'; run apply "$T/src"
refused "Pull=never only in a comment"
new_case; unit 's/^Pull=never$/  Pull = never/; /^Pull/a ; AutoUpdate=registry'
unit '/^\[Container\]$/a # AutoUpdate=registry'; run apply "$T/src"
check "spaced Pull=never and commented AutoUpdate accepted" test $rc -eq 0

# 12. Image= is checked before any change (finding 3).
new_case; unit 's|^Image=.*|Image=ghcr.io/someone-else/echidna:latest|'; run apply "$T/src"
refused "unexpected Image="
new_case; unit '/^Image=/a Image=docker.io/library/busybox:latest'; run apply "$T/src"
refused "second Image="
new_case; unit 's|^Image=.*|  Image = ghcr.io/hyperpolymath/echidna:latest|'; run apply "$T/src"
check "spaced Image= with the expected reference accepted" test $rc -eq 0

# 13. The Caddyfile must have the stopgap shape, not just a @public token
# (finding 4a).
new_case; caddy 's|path /api/health /api/provers|path /api/*|'; run apply "$T/src"
refused "@public widened to /api/*"
new_case; caddy 's|method GET HEAD|method GET HEAD POST|'; run apply "$T/src"
refused "@public admits POST"
new_case; caddy 's|^\t\thandle {$|\t\thandle /api/prove {\n\t\t\treverse_proxy echidna:8081\n\t\t}\n\t\thandle {|'
run apply "$T/src"
refused "extra proxied execution route"
new_case; caddy 's|^\t\t\trespond .*|\t\t\treverse_proxy echidna:8081|'; run apply "$T/src"
refused "catch-all forwards instead of refusing"
new_case; caddy 's|^\t\t\trespond \(.*\) 403$|\t\t\trespond \1 200|'; run apply "$T/src"
refused "catch-all answers 200"
new_case; caddy 's|^\t\t\treverse_proxy echidna:8081 {$|\t\t\trewrite * /api/prove\n&|'; run apply "$T/src"
refused "rewrite inside handle @public"
new_case; printf ':8080 {\n\treverse_proxy echidna:8081\n}\n' >> "$T/src/Caddyfile"; run apply "$T/src"
refused "second site block proxying the API"
new_case; printf '# @public\napi.test {\n\treverse_proxy echidna:8081\n}\n' > "$T/src/Caddyfile"; run apply "$T/src"
refused "@public only in a comment"
new_case; caddy 's|^\t\thandle @public {$|\t\t# a comment\n&   # trailing comment|'; run apply "$T/src"
check "comments do not affect an otherwise stopgap Caddyfile" test $rc -eq 0

# 14. The live probe covers every execution route, not only /api/verify
# (finding 4b).
new_case; run apply "$T/src"
for route in POST/api/prove POST/api/verify POST/api/verify_raw GET/api/stopgap-probe-unknown-route; do
  check "probe sent: ${route%%/*} /${route#*/}" has "curl .* -X ${route%%/*} https://api.test/${route#*/}"
done
for route in POST_api_prove POST_api_verify_raw POST_api_verify_parallel POST_api_session_create \
             POST_api_agent_plan GET_api_stopgap_probe_unknown_route POST_api_health; do
  new_case; run apply "$T/src"; code "$route" 200; run verify
  check "reachable $route fails verify" test $rc -ne 0
  check "reachable $route: no PASS" nopass
done
new_case; run apply "$T/src"; code POST_api_prove 000; run verify
check "unanswered probe fails verify" test $rc -ne 0

echo "# $pass passed, $fail failed"
[ "$fail" -eq 0 ]
