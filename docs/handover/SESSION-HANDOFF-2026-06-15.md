<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
# Session handoff — 2026-06-15

Snapshot of the estate-reconciliation work (echidna + echidnabot) for the next
session. Master tracker **echidna#238 is closed**; remaining work is split into
discrete issues, captured below by normative tier (MUST / INTEND / WISH).

Legend: **done** = merged this campaign · **open** = tracked issue · **owner** =
needs the repo owner (policy/SPDX/branch-delete) · **blocked** = gated on another item.

## Status — ECHIDNA

| Tier | Item | Status | Ref |
|------|------|--------|-----|
| MUST | Proof corpus repaired + CI-gated (Coq/Lean/Agda/Idris2) | done | #234 / #244 |
| MUST | Every workflow job has `timeout-minutes` | done | #247 (closed #241) |
| MUST | `hooks/` dir (RSR pre-commit-enforcement requirement) | this PR | #254·2 |
| MUST | `src/rust/main.rs` SPDX hook blocks *all* commits to it | open · owner 1-liner | #216 |
| MUST | `creusot-verify` CI red (`alt-ergo` not apt-installable) | open | #250 |
| MUST | `salt/`/Python rule stale vs standards (no `salt/` exists) | open · owner doc | #254·1 |
| MUST | Prover-count drift (48/105/113/128 vs `PROVER_COUNT.md`) | open · owner (R5a) | #251 |
| INTEND | `--features verisim` 22 compile errors | open | #245 |
| INTEND | machine_readable + contractile currency audit | open | #252 |
| INTEND | Reconcile remaining RSR divergences (lang-tier undeclared) | open | #254·3 |
| INTEND | Delete 6 reconciled stale branches | open · owner (proxy 403) | #253 |
| INTEND | Wire 13 dispatcher adapters | blocked by #216 | `feat/corpus-dispatcher-all-17-adapters` |
| INTEND | Structural-drift stale paths; ReScript→AffineScript migration | open | #242, #240, #266 |
| WISH | Split Rust/FFI/proof safety alerts by risk class | open | #239 |
| WISH | GNN-at-scale; Cap'n Proto / Chapel-full / coprocessors; 8-stage endpoint | aspirational | `docs/ROADMAP.md` |

## Status — ECHIDNABOT

| Tier | Item | Status | Ref |
|------|------|--------|-----|
| MUST | README test-count 129→184 + ProverSlug | done | #86 |
| MUST | `echidna-fuzz` rate-limit-check timeout | done | #89 |
| MUST | `LICENSE` missing SPDX header (Licence-consistency fails every PR) | open · owner-only | #87 |
| MUST | `.gitignore`/`.gitattributes` PMPL→MPL SPDX drift | open · owner-only | #83 |
| MUST | `gitbot-shared-context` path dep (no bare-clone build) | accepted debt — do not fix | #18 |
| MUST-NOT | `admitted_stub.v` / `sorry_stub.lean` | intentional dogfood failures — leave | — |
| INTEND | Post-checkpoint hygiene (STATE dual-truth, SESSION_SUMMARY, contractiles, `.scm`, SONNET-TASKS, `curl\|sh`) | open | #88 |
| INTEND | `proof-debt.md` TBD→rationale; cflite shared-context vendoring | open | #68, #67 |
| WISH | Codeberg adapter; pre-built Podman images; K8s distributed; full bot-modes | aspirational | #62, #61, #59 |

## Hard constraints (carry forward — these OVERRIDE defaults)
- **Languages:** no Python (the `salt/` exception was removed upstream), no TypeScript, no Go. Use Rust / Julia / Idris2 / Agda / Zig / Chapel / AffineScript / Nickel per `CLAUDE.md`.
- **Build:** Justfile primary (RSR-H14). **Containers:** Podman + `Containerfile`, never Docker/`Dockerfile` (RSR-H15). **Packaging:** Guix; **no Nix** (`flake.nix`/`flake.lock` banned estate-wide).
- **SPDX / LICENSE edits are owner-only, manual, file-by-file** (#216 / #83 / #87) — never automate; automated sweeps must not touch licence headers.
- **echidnabot dogfood stubs** (`admitted_stub.v`, `sorry_stub.lean`) are intentional failures — never "fix".
- **echidnabot** cannot `cargo build` from a bare clone (path-dep #18) — for code work use a `gitbot-fleet` monorepo checkout; doc work is fine standalone.
- **Branch ref-deletes return HTTP 403** via the session git proxy and the GitHub MCP has no delete-branch tool, so branch cleanup (#253) is **owner-only**.
- Develop on `claude/<topic>` branches; open **draft** PRs; be **frugal** with GitHub comments.

## Prompt for the next session

Copy-paste the block below to the next Claude:

> Continue estate maintenance on `hyperpolymath/echidna` + `hyperpolymath/echidnabot`.
>
> **First read:** echidna issue #238 (closed master checkpoint), `docs/handover/SESSION-HANDOFF-2026-06-15.md`, `AFFIRMATION.adoc`, and both repos' `CLAUDE.md` (their rules OVERRIDE defaults).
>
> **Where things stand:** the multi-language proof corpus is repaired, CI-gated, and green on `main`; the master checkpoint is closed; all this campaign's PRs merged. Remaining work is in discrete issues, grouped MUST / INTEND / WISH in the handoff doc.
>
> **Pick up in this order:**
> 1. *Flag to the owner (don't auto-do — SPDX/policy/branch-delete):* #216 (main.rs SPDX hook — unblocks the `feat/corpus-dispatcher-all-17-adapters` branch), echidnabot #87 + #83 (LICENSE/SPDX), #251 (prover-count — fix the GitHub repo description first), #253 (delete the 6 stale branches).
> 2. *Doable now, as draft PRs:* #250 (install `alt-ergo` via opam in `formal-verification.yml`), #245 (`--features verisim` — 22 compile errors), #252 (machine_readable + contractile currency audit — run a Haiku scout before bulk edits), #254 (reconcile the RSR divergences: drop the stale `salt/` wording, declare the polyglot language set as an out-of-template adaptation), echidnabot #88 (hygiene).
>
> **Honor the hard constraints** in the handoff doc (SPDX = owner-only; dogfood stubs intentional; Podman/Justfile/Guix; no Python/TS/Go). Develop on `claude/<topic>` branches, open draft PRs, keep GitHub comments frugal.

---
_Generated 2026-06-15. Source of truth for status: the linked issues + `CHANGELOG.md` + git log; this snapshot drifts._
