// SPDX-License-Identifier: PMPL-1.0-or-later

# Echidna Handover Prompts

This directory mirrors the Echidna continuation prompts that live on the
author's Desktop so that a fresh clone of this repo has the full handover
context tracked in version control.

| File | Scope |
|------|-------|
| `PRODUCTION-WIRING-PLAN.md` | Master plan (L1 Cap'n Proto + L2 Chapel maximal + L3 live-prover CI) |
| `L1-CAPNPROTO-PROMPT.md`    | L1 — swap HTTP+JSON Rust↔Julia for Cap'n Proto |
| `L2-CHAPEL-PROMPT.md`       | L2 — promote Chapel POC to first-class parallel dispatch layer |
| `L3-LIVE-PROVER-CI-PROMPT.md` | L3 — live subprocess CI tiered across 48 prover backends |

## Source of truth

The Desktop copies at `~/Desktop/ECHIDNA-*.md` remain the working drafts
the author edits in-session. These in-repo copies are the canonical
versions for:

- Anyone cloning the repo without Desktop access
- Submodule consumers reading docs without a shell
- Git archaeology (diff across time)

When a session updates a handover prompt, update **both** the Desktop
copy and the in-repo copy in the same commit. If they drift, the in-repo
copy wins because it is the committed one.

## Current status (as of 2026-04-19)

- **L3 Wave-1** (Tier-1, every PR, 9 backends): DONE — `b022bf4`.
- **L3 Wave-2** (Tier-2, nightly, 10 backends): DONE for 9; `hol-light`
  deferred to Wave-3. Commits `9a4aeeb` + `6717b12`.
- **L3 Wave-3** (Tier-3, weekly, 9 backends): scaffold only; needs
  per-backend Containerfiles. Handover hints in
  `.machine_readable/6a2/STATE.a2ml` under `[wave-3-handover-hints]`.
- **L3 Wave-4** (Tier-4, quarterly, 19 backends): scaffold only;
  retained as mock-only unless a maintainer volunteers.
- **L2 Chapel**: `--features chapel` now self-links against bundled
  Zig stubs (`53ab9b8`); real `libechidna_chapel.so` CI path still
  outstanding.
- **L1 Cap'n Proto**: not yet started.
