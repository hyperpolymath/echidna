#!/usr/bin/env python3
# SPDX-License-Identifier: MPL-2.0
"""Check the declared prover inventory and the selected integration ledger."""

from __future__ import annotations

import re
import subprocess
import sys
import tomllib
from datetime import date
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / ".machine_readable/verification-integrations.a2ml"
STATUSES = {
    "backend_declared",
    "partial_non_backend",
    "via_parent",
    "not_integrated",
    "not_a_prover",
}


def enum_variants(source: Path) -> set[str]:
    text = source.read_text(encoding="utf-8")
    start = text.index("pub enum ProverKind")
    opening = text.index("{", start)
    depth = 1
    cursor = opening + 1
    while depth:
        if text[cursor] == "{":
            depth += 1
        elif text[cursor] == "}":
            depth -= 1
        cursor += 1
    body = text[opening + 1 : cursor - 1]
    return set(re.findall(r"^\s*([A-Za-z][A-Za-z0-9_]*)\s*,", body, re.M))


def main() -> int:
    with LEDGER.open("rb") as stream:
        ledger = tomllib.load(stream)
    meta = ledger["metadata"]
    assert meta["schema"] == "verification-integrations/1"
    assert meta["enum_default"] == "declared_unverified"
    date.fromisoformat(meta["reviewed"])

    variants = enum_variants(ROOT / meta["enum_source"])
    with (ROOT / meta["enum_registry"]).open("rb") as stream:
        registered = tomllib.load(stream)
    assert set(registered["prover"]) == variants, "provers.a2ml differs from ProverKind"
    assert registered["metadata"]["count"] == len(variants)
    assert registered["metadata"]["source"] == f'{meta["enum_source"]}::ProverKind'

    tracked = set(
        subprocess.check_output(
            ["git", "ls-tree", "-r", "--name-only", "HEAD"], cwd=ROOT, text=True
        ).splitlines()
    )
    tools = ledger["tool"]
    for name, entry in tools.items():
        status = entry["status"]
        assert status in STATUSES, f"{name}: unknown status {status}"
        assert entry.get("role"), f"{name}: missing role"
        variant = entry.get("prover_kind")
        if status == "backend_declared":
            assert variant in variants, f"{name}: missing ProverKind {variant}"
            assert entry.get("local_paths"), f"{name}: missing backend evidence"
        else:
            assert variant is None, f"{name}: non-backend entry claims a ProverKind"
            assert name not in variants, f"{name}: now has a ProverKind; update status"
        if status == "via_parent":
            assert entry.get("parent_tool") in tools, f"{name}: missing parent tool"
        for path in entry.get("local_paths", []):
            assert path in tracked, f"{name}: missing tracked evidence {path}"

    print(f"OK: {len(variants)} ProverKind declarations; {len(tools)} assessed tool roles")
    return 0


if __name__ == "__main__":
    sys.exit(main())
