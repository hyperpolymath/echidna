#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# fs-fingerprint.sh DEPTH < image.tar
#
# Reads a filesystem tar stream (`podman export`) on stdin and prints one
# line, "<sha256>  <path>", for every path at most DEPTH components deep.
# A regular file's digest covers its content and permissions; a symlink's
# or hard link's covers its target; a directory's covers every entry beneath
# it (type, permissions, path, and content digest or link target).
#
# Comparing two builds path by path then names where they drift, not only
# which layer. Nothing is extracted: content is hashed as it streams past.
# Owners and timestamps are deliberately left out (`podman build
# --timestamp` fixes the times; owners are not what reproducibility means).
#
# Names are untrusted (they come from an image). They are never put into a
# shell command: names and link targets are read from tar's C-quoted
# listing, which is lossless (spaces, tabs, quotes and newlines survive as
# escapes), content digests are matched to entries by archive order, and
# directory digests are computed over numbered group files.
set -euo pipefail
depth=${1:?usage: fs-fingerprint.sh DEPTH < image.tar}
[[ $depth =~ ^[1-9][0-9]*$ ]] || { echo "fs-fingerprint: DEPTH must be a positive integer" >&2; exit 2; }
for tool in tar sha256sum awk sort join xargs; do
  command -v "$tool" >/dev/null || { echo "fs-fingerprint: $tool missing" >&2; exit 2; }
done
tar --version | head -n 1 | grep -q 'GNU tar' || { echo "fs-fingerprint: GNU tar required" >&2; exit 2; }

work=$(mktemp -d)
trap 'rm -rf -- "$work"' EXIT
mkfifo "$work/stream"
export LC_ALL=C

# Single read of stdin, split two ways. The --to-command runs once per
# regular file in archive order and prints only that file's digest: the
# file name is not used, so it cannot be interpreted.
tee "$work/stream" \
  | tar -x --to-command='sha256sum | cut -c1-64' -f - > "$work/digests" &
hasher=$!
tar --quoting-style=c -tv --numeric-owner -f - < "$work/stream" > "$work/listing"
wait "$hasher"

# Manifest rows: "<path>\t<type>\t<perms>\t<digest-or-target>", where path
# and target keep tar's C escapes (no raw tab or newline can occur), with a
# leading "./" or "/" removed. Regular files take the next digest in order.
awk -v digests="$work/digests" '
  # The i-th C-quoted string ("...", with \" escapes) on the line.
  function quoted(s, which,    i, c, n, start, out, inq) {
    n = 0; inq = 0; out = ""
    for (i = 1; i <= length(s); i++) {
      c = substr(s, i, 1)
      if (!inq) { if (c == "\"") { inq = 1; out = "" } continue }
      if (c == "\\") { out = out c substr(s, i + 1, 1); i++; continue }
      if (c == "\"") { inq = 0; if (++n == which) return out; continue }
      out = out c
    }
    return ""
  }
  function clean(p) { sub(/^\.?\//, "", p); sub(/\/$/, "", p); return p }
  {
    t = substr($1, 1, 1); perm = substr($1, 2)
    name = clean(quoted($0, 1))
    if (t == "-" || t == "C") {
      if ((getline d < digests) <= 0) { print "fs-fingerprint: fewer digests than files" > "/dev/stderr"; exit 3 }
      if (name != "") printf "%s\tf\t%s\t%s\n", name, perm, d
    }
    else if (name == "") next
    else if (t == "d") printf "%s\td\t%s\t-\n", name, perm
    else if (t == "l") printf "%s\tl\t%s\t%s\n", name, perm, quoted($0, 2)
    else if (t == "h") printf "%s\th\t%s\t%s\n", name, perm, clean(quoted($0, 2))
    else printf "%s\t%s\t%s\t-\n", name, t, perm
  }
  END { if ((getline d < digests) > 0) { print "fs-fingerprint: more digests than files" > "/dev/stderr"; exit 3 } }
' "$work/listing" | sort -t "$(printf '\t')" -k1,1 > "$work/manifest"

# Every row is credited to each ancestor prefix up to DEPTH. awk writes
# each prefix's rows to a numbered file (the number, not the name, is the
# file name) and an index "number<TAB>prefix"; sha256sum then hashes the
# numbered files, and join maps digests back to prefixes.
mkdir "$work/g"
awk -v depth="$depth" -v dir="$work/g" -F '\t' '
  {
    n = split($1, part, "/"); prefix = ""
    for (k = 1; k <= n && k <= depth; k++) {
      prefix = prefix (k == 1 ? "" : "/") part[k]
      if (!(prefix in id)) { id[prefix] = ++count; printf "%d\t%s\n", count, prefix > (dir "/index") }
      print $0 >> (dir "/" id[prefix])
      # Keep the number of open files bounded on large images.
      close(dir "/" id[prefix])
    }
  }' "$work/manifest"
[[ -s "$work/g/index" ]] || exit 0
(cd "$work/g" && find . -maxdepth 1 -type f ! -name index -printf '%f\0' \
   | xargs -0 sha256sum | awk '{ print $2 "\t" $1 }' | sort -t "$(printf '\t')" -k1,1) > "$work/sums"
sort -t "$(printf '\t')" -k1,1 "$work/g/index" \
  | join -t "$(printf '\t')" -o 2.2,1.2 - "$work/sums" \
  | awk -F '\t' '{ print $1 "  " $2 }' | sort -k2
