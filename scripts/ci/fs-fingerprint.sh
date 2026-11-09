#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# fs-fingerprint.sh DEPTH < image.tar
#
# Reads a filesystem tar stream (`podman export`) on stdin. It prints one
# line, "<sha256>  <path>", for every path at most DEPTH components deep.
# A regular file's digest covers its content and mode. A symlink's covers
# its target. A directory's covers the entries beneath it (type, mode,
# path, and content digest or link target).
#
# Two builds whose image IDs differ can then be compared path by path.
# The paths whose digests differ name where the drift is, not just which
# layer. Nothing is extracted to disk: file contents are hashed as they
# stream past (GNU tar --to-command). Owners and timestamps are left out,
# since `podman build --timestamp` already fixes the times.
set -euo pipefail
depth=${1:?usage: fs-fingerprint.sh DEPTH < image.tar}
[[ $depth =~ ^[1-9][0-9]*$ ]] || { echo "fs-fingerprint: DEPTH must be a positive integer" >&2; exit 2; }
for tool in tar sha256sum awk sort; do
  command -v "$tool" >/dev/null || { echo "fs-fingerprint: $tool missing" >&2; exit 2; }
done
tar --version | head -n 1 | grep -q 'GNU tar' || { echo "fs-fingerprint: GNU tar required" >&2; exit 2; }

work=$(mktemp -d)
trap 'rm -rf -- "$work"' EXIT
mkfifo "$work/stream"

# One pass for listings (types, modes, link targets) and one for content
# hashes: tee splits the single input stream so it is read only once.
# The single quotes are deliberate: tar runs the command, which expands them.
# shellcheck disable=SC2016
tee "$work/stream" < /dev/stdin \
  | tar -x --to-command='printf "%s %s %s\n" "$(sha256sum | cut -d" " -f1)" "$TAR_MODE" "$TAR_FILENAME"' \
      -f - > "$work/files" &
hasher=$!
# --quoting-style=escape keeps one entry per line whatever the names hold.
tar --quoting-style=escape -tv --numeric-owner -f - < "$work/stream" > "$work/listing"
wait "$hasher"

# Manifest: "<path>\t<type>\t<mode-or-perm>\t<digest-or-target>", path
# normalised to no leading "./" or "/". Regular files come from the hash
# pass; directories and symlinks from the listing.
awk '{ p = $0; sub(/^[^ ]+ [^ ]+ /, "", p); sub(/^\.?\//, "", p); if (p != "") printf "%s\tf\t%s\t%s\n", p, $2, $1 }' "$work/files" > "$work/manifest"
awk '
  {
    t = substr($1, 1, 1); perm = substr($1, 2)
    # Fields: perms owner size date time name [-> target]
    name = ""; for (i = 6; i <= NF; i++) { if ($i == "->") break; name = name (name == "" ? "" : " ") $i }
    target = ""; for (j = i + 1; j <= NF; j++) target = target (target == "" ? "" : " ") $j
    sub(/^\.?\//, "", name); sub(/\/$/, "", name)
    if (name == "") next
    if (t == "d") printf "%s\td\t%s\t-\n", name, perm
    else if (t == "l") printf "%s\tl\t%s\t%s\n", name, perm, target
    else if (t == "h") printf "%s\th\t%s\t%s\n", name, perm, target
  }' "$work/listing" >> "$work/manifest"
LC_ALL=C sort -t "$(printf '\t')" -k1,1 -o "$work/manifest" "$work/manifest"

# For every path up to DEPTH: a file/link digests its own row; a directory
# digests every row at or beneath it. One awk pass emits "prefix\trow"
# pairs; grouping and hashing happen per prefix.
awk -v depth="$depth" -F '\t' '
  {
    n = split($1, part, "/")
    prefix = ""
    for (k = 1; k <= n && k <= depth; k++) {
      prefix = prefix (k == 1 ? "" : "/") part[k]
      print prefix "\t" $0
    }
  }' "$work/manifest" | LC_ALL=C sort -t "$(printf '\t')" -k1,1 -s > "$work/pairs"

awk -F '\t' '
  function flush() { if (cur != "") { close(cmd); } }
  {
    if ($1 != cur) { flush(); cur = $1; esc = cur; gsub(/[\\|&]/, "\\\\&", esc); cmd = "sha256sum | cut -c1-64 | sed \"s|$|  " esc "|\"" }
    line = $2; for (i = 3; i <= NF; i++) line = line "\t" $i
    print line | cmd
  }
  END { flush() }' "$work/pairs" | LC_ALL=C sort -k2
