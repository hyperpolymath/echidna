<!--
SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Issue specifications

Drafted issue specifications for the ParadisEO metaheuristic integration roadmap.
Each file is the body for one GitHub issue; the title and labels are in the file header.

To produce an issue body from a file (everything after the `# ` title line, without the SPDX header):

```sh
awk 'f;/^# /{f=1}' issues/<file> | sed '1{/^$/d}' > /tmp/body.md
```

| ID     | Repository                   | GitHub issue | File                                                  |
|--------|------------------------------|--------------|-------------------------------------------------------|
| ECH-01 | hyperpolymath/echidna        | #420         | `echidna-01-pareto-moeo.md`                           |
| ECH-02 | hyperpolymath/echidna        | #421         | `echidna-02-cmaes-julia-gnn.md`                       |
| ECH-03 | hyperpolymath/echidna        | #422         | `echidna-03-chapel-island-migration.md`               |
| ECH-04 | hyperpolymath/echidna        | #424         | `echidna-04-ffi-abi-bridge.md`                        |
| PB-01  | hyperpolymath/proof-burrower | not filed    | `proof-burrower-01-combinatorial-tactic-synthesis.md` |
| PB-02  | hyperpolymath/proof-burrower | not filed    | `proof-burrower-02-ledger-fitness-formulation.md`     |
| EB-01  | hyperpolymath/echidnabot     | not filed    | `echidnabot-01-adaptive-ci-portfolio-scheduler.md`    |

#423 on hyperpolymath/echidna is unrelated to this roadmap.

## Status

- **ECH-01..04** are filed on hyperpolymath/echidna and carry all their labels. On 2026-10-09 their bodies were replaced by hand with a different text that is not these files; the owner decides which is canonical (see `docs/handover/PARADISEO-ROADMAP-PROMPT.adoc`, WP0). `scripts/issues/sync-roadmap-issues.sh` syncs the bodies from these files (dry run by default; refuses to replace hand-edited bodies without `--overwrite`).
- **PB-01, PB-02, EB-01** are drafts for copying to their own repositories. They are not filed.

## Provenance of the PB and EB drafts

The PB and EB specifications were written from this repository. Statements about
proof-burrower and echidnabot are marked *[unverified]*: they come from a read-only look
at `proof-burrower@be897dd` and `echidnabot@ae52833`, and were not built, run or confirmed
by those repositories' maintainers. Re-check them against the current code before filing.
Statements about echidna were checked against echidna `main` at `7fd369d`.

## Labels missing in the target repositories

Labels named in the drafts that did not exist when they were written (checked 2026-10-09):

| Repository                   | Missing labels                                                      |
|------------------------------|---------------------------------------------------------------------|
| hyperpolymath/proof-burrower | `area:swarm`, `rust`, `search-tactics`, `area:ledger`, `heuristics` |
| hyperpolymath/echidnabot     | `area:dispatcher`, `ci-optimization` (`rust` exists)                |

All labels used by ECH-01..04 exist on hyperpolymath/echidna.
