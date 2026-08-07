<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

# Debt register

Known, measured debt in this repository: licensing, documentation, and code.
Supersedes [`tech-debt-2026-05-26.md`](tech-debt-2026-05-26.md), which is
retained as a dated snapshot.

**Every entry carries the command that produced its figure.** An entry without
evidence is a rumour, and rumours do not belong in a debt register. Re-run the
commands from the repository root before acting on any item — they are the
definition of the finding, not a description of it.

Entries are **not** issues. Where a GitHub issue already tracks an item it is
linked; where the fix requires a decision only the owner can make, the entry
says so explicitly and stops there.

Priorities: **P0** — a downstream consumer can be actively misled or harmed.
**P1** — a reader is misinformed but not exposed. **P2** — friction, cost, or
latent risk.

---

## P0 — Licensing: the repository states four different licences

**This is the most serious item in the register.** A recipient cannot determine
the terms under which they receive this software, and every surface they might
reasonably consult gives a different answer.

| Surface | What it states | Evidence |
|---|---|---|
| `LICENSE` (full GNU text) | AGPL-3.0-or-later | `head -3 LICENSE` |
| `Cargo.toml` | AGPL-3.0-or-later | `grep '^license' Cargo.toml` |
| README badge | AGPL-3.0-or-later | `grep -m1 'License:' README.md` |
| Per-file SPDX headers — **590 source files** (584 `MPL-2.0`, 6 dual with `Palimpsest-0.6`) | MPL-2.0 | `L1` below |
| Per-file SPDX headers | AGPL-3.0-or-later — **zero files** | `L2` below |
| `NOTICE` | MPL-2.0, and points at `LICENSE` for the "full text" — but `LICENSE` is AGPL | `head -10 NOTICE` |
| `.reuse/dep5` (`src/*`) | `PMPL-1.0 AND Palimpsest-0.6` | `grep -m1 -A3 'Files: src' .reuse/dep5` |
| `.github/workflows/governance.yml` | `PMPL-1.0-or-later` | `head -1 .github/workflows/governance.yml` |
| GitHub's own detection | "Other" — no licence identified | `gh repo view --json licenseInfo` |

```bash
# L1 — source files declaring MPL-2.0 (590: 584 plain + 6 dual)
git grep -I -h -m1 -oP 'SPDX-License-Identifier:\s*\K[A-Za-z0-9.\-+]+( (AND|OR) [A-Za-z0-9.\-+]+)*' \
  -- '*.rs' '*.jl' '*.zig' '*.chpl' '*.idr' '*.agda' '*.res' '*.sh' '*.ncl' | sort | uniq -c

# L2 — source files declaring AGPL (0)
git grep -l 'SPDX-License-Identifier:.*AGPL' -- '*.rs' '*.jl' '*.zig' | wc -l
```

The difference is not cosmetic. MPL-2.0 is file-level weak copyleft with no
network clause; AGPL-3.0-or-later is strong copyleft that reaches users served
over a network. A downstream integrator reading the file headers would conclude
they may offer a modified ECHIDNA as a hosted service without publishing their
changes. The `LICENSE` file says otherwise. **Because the per-file headers are
themselves a licence grant, this exposure is real, not theoretical.**

Two further consequences:

- **REUSE non-compliance.** `.reuse/dep5` and nine file headers reference
  `PMPL-1.0` and `Palimpsest-0.6`, but `LICENSES/` contains only
  `AGPL-3.0-or-later.txt`, `CC-BY-SA-4.0.txt`, and `MPL-2.0.txt`. A REUSE
  conformance run cannot resolve those identifiers.
  Evidence: `ls LICENSES/` and `git grep -l Palimpsest`.
- **GitHub reports the licence as "Other"**, so the repository shows no licence
  in search, the sidebar, or the API. The likely cause is the
  `SPDX-License-Identifier:` line prepended to `LICENSE` above the GNU text,
  which stops GitHub's detector matching the body. Removing that one line is a
  low-risk experiment that does not alter the grant.

**Owner decision required — do not "fix" this in a routine PR.** The recorded
decision (`CLAUDE.md`, matching `Cargo.toml`) is AGPL-3.0-or-later. Applying it
means rewriting the SPDX header of every source file, which is a re-licensing
act with consequences for existing recipients and any contributor who submitted
under MPL terms. Nobody should do that on their own initiative.

Suggested sequence, once the owner has ruled:

1. Confirm the intended licence for **code** and for the **documentation
   surface** separately — `CLAUDE.md` states the MPL headers on docs are
   deliberate, so the two may legitimately differ.
2. Reconcile `NOTICE` first: it is the only surface that is internally
   self-contradictory (it names MPL and cites an AGPL file as its text).
3. Add the missing `LICENSES/` texts, or remove the `PMPL-1.0` /
   `Palimpsest-0.6` references if those licences are retired.
4. Only then sweep the per-file headers, in one reviewable commit per language.
   A previous blind SPDX sweep in this estate mis-licensed files by imposing a
   header where a different one already existed further down the file — grep the
   whole file, move the identifier, never impose one.
5. Drop the prepended SPDX line from `LICENSE` and confirm GitHub detects it.

---

## P1 — Documentation

### D1. Prover counts drift across surfaces *(issue [#251](https://github.com/hyperpolymath/echidna/issues/251))*

**Largely addressed** in the documentation refresh that added this file; recorded
because the underlying cause is structural and will recur.

The tree contained five different counts — 48, 105, 128, 138, 141 — because
four different things are all called "the number of provers": enum variants
(141), implementation files (105), implementations with `suggest_tactics`
(102), and default-exposed core backends (12). All four are defensible; none is
"the" count. [`PROVER_COUNT.md`](PROVER_COUNT.md) is now canonical, carries the
commands that reproduce each figure, and explains the denominators.

**Residual risk:** the `R5a` CI rule
(`.github/canonical-references/prover-counts.yml`) that forbids bare counts
covers only the top-level document set named in that file. `docs/`,
`.machine_readable/`, `crates/*/README.md` and `.github/*.md` are **out of
scope**, which is precisely where the drift accumulated. Extending the rule's
scope is unfinished work.

### D2. Tier membership is hand-maintained and unverifiable

`PROVER_COUNT.md`'s tier table is the routing contract, but only Tier 1
(`ProverKind::all_core()`) and Tier 9 are machine-checkable. Tier 4's
"19 placeholder backends" and Tier 8's "13 corpus-only provers" are asserted,
not derived, and were not re-measured in this pass — they are marked as
indicative in the table. Making tier membership an attribute on each
`ProverKind` variant would make the table generated rather than maintained.

### D3. Unearned OpenSSF Best Practices badge

`README.md` displays a hardcoded green "OpenSSF Best Practices" badge that
links to the project **registration** form, not to a passing scorecard:

```bash
grep -oE 'bestpractices.dev[^)]*' README.md
# bestpractices.dev/en/projects/new?repo_url=https://github.com/hyperpolymath/echidna
```

The badge image is a static `img.shields.io` green label, so it will read as
"passed" regardless of the project's actual standing — including now, when the
project is not registered. Either register the project and use the real badge
(which reflects the true tier and changes when it lapses), or remove the badge.
A permanently-green badge that cannot fail is indistinguishable from a false
claim. This is a known estate-wide pattern, not unique to this repository.

### D4. Broken links in historical release notes

Nine dead links remain in `docs/releases/RELEASE_NOTES_v1.2.md` and
`RELEASE_NOTES_v1.3.md`, pointing at design documents that are not in the tree
(`CHAPEL_METALAYER_ANALYSIS.md`, `ZIG_FFI_ANALYSIS.md`,
`FUTURE_DEVELOPMENT_ROADMAP.md`, `QUICKSTART.md`, and others). Live documents
were repaired in the refresh; these were deliberately left, because release
notes are dated records and rewriting them rewrites history. They should either
be de-linked in place or the referenced documents restored from git history.

```bash
# re-measure broken relative links across all Markdown/AsciiDoc
git grep -nE '\]\([A-Za-z0-9_./-]+\.(md|adoc)\)' -- '*.md' '*.adoc' | while IFS= read -r l; do
  src="${l%%:*}"; ref=$(echo "$l" | grep -oE '\]\([A-Za-z0-9_./-]+\)' | sed -E 's/^\]\(//;s/\)$//')
  for r in $ref; do [ -e "$(dirname "$src")/$r" ] || echo "$src -> $r"; done
done
```

### D5. `echidna-playground/SECURITY.md` references absent files

It links to `README.md`, `CHANGELOG.md`, `CONTRIBUTING.md` and
`SECURITY-ACKNOWLEDGMENTS.md` inside `echidna-playground/`; none exist
(`ls echidna-playground/`). The sub-project's security policy therefore
directs a reporter to nothing. Either add the files or point the links at the
parent repository's equivalents.

### D6. Root scaffold documents displaced the real ones — *fixed, recorded*

`ARCHITECTURE.md` and `GOVERNANCE.md` at the repository root contained generic
template text with **zero** project-specific content, while the real documents
sat at `docs/ARCHITECTURE.md` (160 lines) and `GOVERNANCE.adoc` (162 lines):

```bash
grep -icE 'echidna|prover|neurosym|trust' ARCHITECTURE.md     # was 0
grep -icE 'echidna|prover|RSR|hyperpolymath' GOVERNANCE.md     # was 0
```

This was worse than duplication. GitHub surfaces the `.md` member in its
community-standards checks and contributor prompts, so the document most
readers landed on described a project that could have been anything. Both are
now explicit pointers to the canonical documents, following the pattern
`CONTRIBUTING.md` already used correctly.

**Watch for recurrence:** these files match the estate's scaffold-template
shape, so a future template sweep may reinstate them. The check above is the
detector — a root `.md` scoring 0 is scaffold, not documentation.

### D7. `.machine_readable/6a2/` no longer exists

The six descriptiles moved to `.machine_readable/descriptiles/`. Seventeen
documents pointed at the old path and were repaired in the refresh, but the
contractile configurations still name `.machine_readable/6a2/DRIFT.a2ml` and
`.machine_readable/6a2/ratification-<session-id>.a2ml` as **write
destinations**:

```bash
git grep -n '6a2/' -- '*.ncl'
```

Those were left alone deliberately: `6a2` is a concept name there, not a stale
path, and changing a contractile's evidence sink is a semantic decision. But the
directory does not exist, so any drift-log write has nowhere to land. Confirm
whether the sink should be created or repointed.

---

## P2 — Code

### C1. ReScript remains, though the language policy bans it

31 files (`git ls-files '*.res' '*.resi' | wc -l`). Project policy names
ReScript as banned with AffineScript-TEA as the replacement, and the migration
is blocked on missing AffineScript primitives — `Http::fetch`, `Async`, `Json`
— tracked in issues [#266](https://github.com/hyperpolymath/echidna/issues/266)
and [#117](https://github.com/hyperpolymath/echidna/issues/117). The debt is the
gap between a stated ban and an unmigrated tree, and the honest reading is that
the policy is aspirational until those primitives land.

### C2. 185 `#[allow(dead_code)]` suppressions

```bash
git grep -c 'allow(dead_code)' -- '*.rs' | awk -F: '{s+=$2} END{print s}'
```

Each one silences the compiler's own report of unreachable code. At this volume
the suppressions, not the compiler, define what counts as live code — so genuine
dead code is no longer detectable. Worth a pass to distinguish
scaffolding-for-planned-work (annotate with the tracking issue) from code that
should be deleted.

### C3. Placeholder backends are indistinguishable from working ones at the API

Tier 4 backends are `ProverKind` variants with mock-only invocation, but they
are reachable through the same `ProverKind` selection as real ones. A caller
selecting one receives a response shaped like a proof result. `container-ci.yml`
runs stub-sentinel detection for Tier-3 cells; the corresponding guarantee for
Tier-4 placeholders at the API boundary is not documented. Related: D2 — the
placeholder count itself is unverified.

### C4. Unfinished-work markers

Low and healthy for a tree this size — recorded as a baseline to watch:

```bash
git grep -cE 'TODO|FIXME|XXX' -- '*.rs' | awk -F: '{s+=$2} END{print s}'   # 11 across 6 files
git grep -cE 'todo!\(\)|unimplemented!\(\)' -- '*.rs' | awk -F: '{s+=$2} END{print s}'   # 1
```

---

## Already tracked as issues

Open issues covering debt not duplicated above: [#314](https://github.com/hyperpolymath/echidna/issues/314)
(hypatia baseline gate un-armed — currently the reason `Governance` fails on
`main`), [#310](https://github.com/hyperpolymath/echidna/issues/310) (dead
`VERISIMDB_PAT`), [#252](https://github.com/hyperpolymath/echidna/issues/252)
(machine-readable currency audit), [#242](https://github.com/hyperpolymath/echidna/issues/242)
(structural drift in path references), [#240](https://github.com/hyperpolymath/echidna/issues/240)
(ReScript deprecated-API triage), [#239](https://github.com/hyperpolymath/echidna/issues/239)
(safety-alert classification), [#216](https://github.com/hyperpolymath/echidna/issues/216)
(SPDX-FileCopyrightText hook blocks commits — a licensing-adjacent item that
should be resolved alongside P0).

## Maintaining this file

Add an entry when you find debt you are not fixing in the same change. Include
the command that measures it. Remove an entry only when the command that
detected it comes back clean — not when the work "feels done".
