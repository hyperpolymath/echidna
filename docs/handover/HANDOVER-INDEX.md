<!-- SPDX-License-Identifier: MPL-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->

# Handover Index

**Status**: canonical map of the `docs/handover/` suite. Last revised: 2026-05-26.

Each file in this directory is either:
- a **prompt** — a self-contained brief for the next agent to execute a named
  workstream, OR
- a **runbook** — an operational guide for a now-live workstream, OR
- a **plan** — a multi-sprint coordination document, OR
- a **state log** — running notes from prior sessions.

Read this index first to know which file is which.

## Active prompts (next agent picks one to execute)

| File | Workstream | Pre-condition | Effort |
|---|---|---|---|
| [`L1-CAPNPROTO-PROMPT.md`](L1-CAPNPROTO-PROMPT.md) | Stage 5a — Cap'n Proto IPC | L3 hand-off green ≥ 7 days | ~2 sprints |
| [`L2-CHAPEL-PROMPT.md`](L2-CHAPEL-PROMPT.md) | Stage 5b — Chapel L2.2+ (speculative search, corpus-parallel, multi-locale) | L1 landed | ~4 sprints |
| [`L3-LIVE-PROVER-CI-PROMPT.md`](L3-LIVE-PROVER-CI-PROMPT.md) | Stage 5d — Tier-4 live-CI provisioning | Tier-1 main CI green ≥ 7 days | ~1 sprint |
| [`PHASE-3-PROMPT.md`](PHASE-3-PROMPT.md) | Modal + real-algebraic backends (Wave-2 follow-on) | Wave-2 done | ~1 sprint |
| [`SUGGEST-CLI-PROMPT.md`](SUGGEST-CLI-PROMPT.md) | `suggest` verb implementation | None | ~3 days |

## Active runbooks (live workstream is in production)

| File | What it covers |
|---|---|
| [`S4-LOOP-CLOSURE-RUNBOOK.md`](S4-LOOP-CLOSURE-RUNBOOK.md) | VeriSim learning-loop end-to-end test (`just test-s4-loop`) and operational verification |
| [`S5-VERIFICATION-RUNBOOK.md`](S5-VERIFICATION-RUNBOOK.md) | Trained-GNN-weights verification flow: `just train-cpu` → `/gnn/health` → `just eval` |

## Plans (multi-sprint coordination)

| File | Scope |
|---|---|
| [`PRODUCTION-WIRING-PLAN.md`](PRODUCTION-WIRING-PLAN.md) | Three-tier (L1 Cap'n Proto / L2 Chapel / L3 live CI) production-wiring plan. L1 prompt is the executable derivative. |

## Deferred-work trackers

| File | Tracks |
|---|---|
| [`THEOREM-METADATA-MIGRATION.md`](THEOREM-METADATA-MIGRATION.md) | Future migration of 8 parser-site structural meta-tags out of `Theorem.aspects` into a dedicated `TheoremKind` field. Boundary filter contains the damage; this is hygiene. |

## State & navigation

| File | What it is |
|---|---|
| [`TODO.md`](TODO.md) | Living backlog. Single source of truth for "what's next" between sprints. P0–P4 priority bands. |
| [`STATE.md`](STATE.md) | Running human-readable state log. Complement to `.machine_readable/6a2/STATE.a2ml`. |
| [`README.md`](README.md) | Original handover suite intro (older; kept for orientation). |

## Warmup material

| File | Audience |
|---|---|
| [`llm-warmup-dev.md`](llm-warmup-dev.md) | LLM session warmup for contributors |
| [`llm-warmup-user.md`](llm-warmup-user.md) | LLM session warmup for end-users |

## Execution order (when starting a fresh sprint)

1. Read `STATE.md` (or `STATE.a2ml`) for the current sprint state.
2. Read `TODO.md` for the prioritised backlog.
3. Pick the next-up prompt from "Active prompts" whose pre-condition is met.
4. Execute the prompt; cite this index in commits if you reorder priorities.
5. When a prompt is "consumed" by completion, retire it into the git-history
   archive — do not leave consumed prompts alongside active ones.

## Stage cross-reference

Maps `docs/ROADMAP.md` stage IDs to the handover artefact that drives each:

| Stage | Drives | Artefact |
|---|---|---|
| 2a/2c | GNN training + eval | `S5-VERIFICATION-RUNBOOK.md` |
| 3a/3b | Verisim read paths | `S4-LOOP-CLOSURE-RUNBOOK.md` (done) |
| 3c | Outcome emission wiring | Stage-3c plan in chat history (no dedicated handover yet — to be written when work begins) |
| 4c/4d | `suggest_tactics` GNN ranking | `SUGGEST-CLI-PROMPT.md` |
| 5a | Cap'n Proto IPC | `L1-CAPNPROTO-PROMPT.md` |
| 5b | Chapel L2.2+ | `L2-CHAPEL-PROMPT.md` |
| 5d | Tier-4 live CI | `L3-LIVE-PROVER-CI-PROMPT.md` |

## When this index goes stale

Update conditions:
- A prompt is completed → move it to a `archive/` subdirectory or delete and note in this file.
- A new prompt is added → add a row to the appropriate section.
- A stage status changes in `docs/ROADMAP.md` → update the cross-reference table.

Quick check: `ls docs/handover/*.md | wc -l` should match the number of rows
across all tables above. As of 2026-05-26, this file accounts for 13 entries.
