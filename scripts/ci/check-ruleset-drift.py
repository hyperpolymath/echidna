#!/usr/bin/env python3
# SPDX-License-Identifier: MPL-2.0
"""Compare the committed ruleset snapshot with the rulesets GitHub enforces.

Snapshot files live in .github/rulesets/live/<name>.json, one per ruleset,
keyed by the ruleset `id`. The top-level .github/rulesets/*.json files are
historical payloads and are not compared.

Reading rulesets needs repository administration read. Run this with a token
that has it (`GH_TOKEN=... python3 scripts/ci/check-ruleset-drift.py`). The
default GITHUB_TOKEN may not be enough in Actions; see the workflow note in
.github/rulesets/README.adoc. Exit codes: 0 no drift, 1 drift, 2 cannot read.

Regenerate the snapshot after an intentional change, not to silence drift:
    python3 scripts/ci/check-ruleset-drift.py --write
"""
import argparse
import glob
import json
import os
import subprocess
import sys

VOLATILE = {"_links", "created_at", "updated_at", "node_id", "current_user_can_bypass", "source", "source_type"}


def normalise(obj):
    if isinstance(obj, dict):
        return {k: normalise(v) for k, v in obj.items() if k not in VOLATILE}
    if isinstance(obj, list):
        return [normalise(v) for v in obj]
    return obj


def gh_json(args):
    out = subprocess.run(["gh", "api", *args], check=True, capture_output=True, text=True)
    return json.loads(out.stdout)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", default="hyperpolymath/echidna")
    ap.add_argument("--dir", default=".github/rulesets/live")
    ap.add_argument("--write", action="store_true")
    args = ap.parse_args()

    try:
        listing = gh_json([f"repos/{args.repo}/rulesets"])
    except (subprocess.CalledProcessError, FileNotFoundError, json.JSONDecodeError) as exc:
        print(f"cannot read rulesets for {args.repo}: {exc}", file=sys.stderr)
        return 2

    live = {}
    for r in listing:
        live[r["id"]] = normalise(gh_json([f"repos/{args.repo}/rulesets/{r['id']}"]))

    if args.write:
        os.makedirs(args.dir, exist_ok=True)
        for rid, body in live.items():
            name = body["name"].replace("/", "-")
            with open(os.path.join(args.dir, f"{name}.json"), "w", encoding="utf-8") as fh:
                json.dump(body, fh, indent=2, sort_keys=True)
                fh.write("\n")
        print(f"wrote {len(live)} ruleset snapshot(s) to {args.dir}")
        return 0

    drift, seen = [], set()
    for path in sorted(glob.glob(os.path.join(args.dir, "*.json"))):
        with open(path, encoding="utf-8") as fh:
            snap = normalise(json.load(fh))
        rid = snap.get("id")
        seen.add(rid)
        if rid not in live:
            drift.append(f"{path}: ruleset {rid} ({snap.get('name')}) is in the snapshot but not enforced")
        elif live[rid] != snap:
            drift.append(f"{path}: ruleset {rid} ({snap.get('name')}) differs from the enforced state")
    for rid, body in live.items():
        if rid not in seen:
            drift.append(f"ruleset {rid} ({body.get('name')}) is enforced but has no snapshot")

    for d in drift:
        print(f"::error::{d}")
    print(f"rulesets enforced: {len(live)}, snapshots: {len(seen)}, drift: {len(drift)}")
    return 1 if drift else 0


if __name__ == "__main__":
    sys.exit(main())
