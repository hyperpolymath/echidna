#!/usr/bin/env python3
# SPDX-License-Identifier: MPL-2.0
"""Fail CI when an allow-fail unit lacks an owner or an expiry, or has expired.

Every workflow line that sets `continue-on-error` to anything other than the
literal `false` must carry, on the same line:

    # allow-fail: issue=#<n> expires=YYYY-MM-DD

The checker is deliberately text-based: it needs no YAML library, and it sees
the same literal the runner sees. It does not decide what happens at expiry.
A person does (ultraplan Phase 2.3, tracking issue #416).

Usage: check-allow-fail-expiry.py [--today YYYY-MM-DD] [--warn-days N] [DIR ...]
"""
import argparse
import datetime as dt
import glob
import os
import re
import sys

KEY = re.compile(r"^\s*continue-on-error:\s*(?P<value>[^#]*?)\s*(?:#.*)?$")
MARK = re.compile(r"#\s*allow-fail:\s*issue=#(?P<issue>\d+)\s+expires=(?P<date>\d{4}-\d{2}-\d{2})\b")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("dirs", nargs="*", default=[".github/workflows"])
    ap.add_argument("--today", default=None)
    ap.add_argument("--warn-days", type=int, default=21)
    args = ap.parse_args()
    today = dt.date.fromisoformat(args.today) if args.today else dt.date.today()

    errors, warnings, units = [], [], 0
    files = []
    for d in args.dirs:
        files += sorted(glob.glob(os.path.join(d, "*.yml")) + glob.glob(os.path.join(d, "*.yaml")))

    for path in files:
        with open(path, encoding="utf-8") as fh:
            for lineno, line in enumerate(fh, 1):
                m = KEY.match(line.rstrip("\n"))
                if not m or m.group("value") == "false":
                    continue
                units += 1
                where = f"{path}:{lineno}"
                mk = MARK.search(line)
                if not mk:
                    errors.append(f"{where}: continue-on-error without '# allow-fail: issue=#N expires=YYYY-MM-DD'")
                    continue
                try:
                    expiry = dt.date.fromisoformat(mk.group("date"))
                except ValueError:
                    errors.append(f"{where}: invalid expiry date {mk.group('date')}")
                    continue
                if expiry < today:
                    errors.append(f"{where}: allow-fail expired on {expiry} (issue #{mk.group('issue')}); make it blocking, re-justify, or remove")
                elif (expiry - today).days <= args.warn_days:
                    warnings.append(f"{where}: expires {expiry} (issue #{mk.group('issue')})")

    for w in warnings:
        print(f"::warning::{w}")
    print(f"allow-fail units checked: {units}")
    if errors:
        for e in errors:
            print(f"::error::{e}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
