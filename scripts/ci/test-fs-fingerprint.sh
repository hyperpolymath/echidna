#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Self-test for scripts/ci/fs-fingerprint.sh: identical trees agree, and a
# content, mode or link-target change is reported at the changed path and
# its ancestors only. Names with spaces, "|" and "&" survive intact.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
t=$(mktemp -d); trap 'rm -rf -- "$t"' EXIT
fp() { (cd "$1" && tar --sort=name -cf - .) | bash "$here/fs-fingerprint.sh" "$2"; }
fail() { echo "FAIL: $*" >&2; exit 1; }

mkdir -p "$t/a/opt/elan/toolchains/lean/lib" "$t/a/usr/bin"
echo hi > "$t/a/usr/bin/x"
echo lean > "$t/a/opt/elan/toolchains/lean/lib/a.olean"
echo s > "$t/a/opt/elan/settings.toml"
ln -s ../usr/bin/x "$t/a/opt/link"
echo odd > "$t/a/opt/we|ird &name"
chmod 0644 "$t/a/usr/bin/x"

clone() { rm -rf "$t/b"; cp -a "$t/a" "$t/b"; }
changed() { diff <(fp "$t/a" "$1") <(fp "$t/b" "$1") | sed -n 's/^> [0-9a-f]\{64\}  //p' | sort | tr '\n' ' '; }

clone
[[ -z $(changed 4) ]] || fail "identical trees differ"
fp "$t/a" 2 | grep -qx '[0-9a-f]\{64\}  opt/we|ird &name' || fail "odd name lost"

echo changed > "$t/b/opt/elan/toolchains/lean/lib/a.olean"
[[ $(changed 3) == "opt opt/elan opt/elan/toolchains " ]] || fail "deep content change: $(changed 3)"
[[ $(changed 6) == "opt opt/elan opt/elan/toolchains opt/elan/toolchains/lean opt/elan/toolchains/lean/lib opt/elan/toolchains/lean/lib/a.olean " ]] \
  || fail "deep content change at depth 6: $(changed 6)"

clone; chmod 0755 "$t/b/usr/bin/x"
[[ $(changed 3) == "usr usr/bin usr/bin/x " ]] || fail "mode change: $(changed 3)"

clone; ln -sfn ../usr/bin/y "$t/b/opt/link"
[[ $(changed 2) == "opt opt/link " ]] || fail "link target change: $(changed 2)"

# fs-fingerprint-drift.sh names the deepest differing paths, odd names whole.
clone; echo changed > "$t/b/opt/elan/toolchains/lean/lib/a.olean"; echo x > "$t/b/opt/we|ird &name"
rm "$t/b/usr/bin/x"
fp "$t/a" 9 > "$t/fa"; fp "$t/b" 9 > "$t/fb"
leaves=$(bash "$here/fs-fingerprint-drift.sh" "$t/fa" "$t/fb" | tr "\n" "|")
[[ $leaves == "opt/elan/toolchains/lean/lib/a.olean|opt/we|ird &name|usr/bin/x|" ]] || fail "drift leaves: $leaves"
[[ -z $(bash "$here/fs-fingerprint-drift.sh" "$t/fa" "$t/fa") ]] || fail "self-drift not empty"

if echo | bash "$here/fs-fingerprint.sh" 0 2>/dev/null; then fail "depth 0 accepted"; fi
echo "PASS: fs-fingerprint names exactly the changed paths (content, mode, link target)"
