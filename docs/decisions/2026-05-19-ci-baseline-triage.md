<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->

# 2026-05-19 — CI baseline triage: real defects vs baseline-rot vs infra jam

ADR-style record of the CI triage done while landing PR #73 and the
two baseline-blocker follow-ups (#86, #87). Written so future humans
**and** agents do not re-litigate these red checks. Companion
machine-readable record:
`.machine_readable/6a2/STATE.a2ml § [session-2026-05-19-ci-baseline-triage]`.

## TL;DR for anyone debugging echidna PR CI

A red check on an echidna PR is one of **three** distinct things. Do
not treat them the same:

1. **Real, in-scope PR defect** — caused by the PR's own diff. Fix it
   on the PR.
2. **Baseline rot** — fails identically on `origin/main`, independent
   of any PR diff. **Do not block the PR on it.** Fix in a *dedicated*
   PR off `main`; blocked PRs clear on their next `main` merge.
3. **#77 CI-infra jam** — runner never assigned, or job fast-fails in
   ~15–30 s with **no step logs**. Not a code defect. Estate-infra,
   tracked in #77; an estate-wide remediation owns it.

**Merge is gated only by these 6 required status checks** (GitHub
branch protection on `main`, verified 2026-05-19):

- `Analyze (rust)`
- `Cargo check + clippy + fmt`
- `Dependency audit`
- `Dogfood Gate`
- `Hypatia Neurosymbolic Analysis`
- `OpenSSF Scorecard`

Everything else (`MVP Smoke`, `Julia Integration`, `Minimum Supported
Rust Version`, `PR (address)`, `Validate A2ML/K9 manifests`,
`governance / *`, the `T1–T4` prover matrices) is **non-gating**. A
red non-required check does not stop auto-merge.

## What was triaged (PR #73 = Wave-3 consolidation, MERGED `d3db97d`)

| Check | Class | Resolution |
|---|---|---|
| `Build & verify container image` | **Real PR defect** | The minimal `.containerization/Containerfile` + `Containerfile.full` copied only `src/rust`+`src/interfaces`; the workspace `Cargo.toml` has path-deps `crates/echidna-core` + `crates/typed_wasm` and `crates/*` members. `Containerfile.wave3` fixed it; the other two were left stale (`Containerfile.mcp` was already correct). Carried `COPY crates ./crates` + `COPY benches ./benches` to both — merged in #73. |
| `Test Suite`, `Code Coverage`, `MVP Smoke`, `Julia Integration` | **Baseline rot** | `rust-ci.yml` ran with `--all-features` → forced on `flint`/`spark`/`chapel` (system-lib features) → `cargo test` link-failed `unable to find library -lflint` on **every** PR. → issue #85 → **PR #86**. |
| `governance / *` (3 jobs, ~15 s, no logs), most pending required jobs | **#77 infra jam** | Runner-assignment / fast-fail-no-logs. Parked on #77. |
| `PR (address)` (clusterfuzzlite) | Pre-existing, non-gating | Action hardcodes `.clusterfuzzlite/Dockerfile`; repo ships `Containerfile`. → **PR #87** (tracked symlink). |
| `Minimum Supported Rust Version` | Baseline / #77-class | Fails **identically on `main`** (24 s, zero step logs). Not introduced by any PR; not required. |

## Decision 1 — `rust-ci.yml` feature flags (#85 → #86)

**Root cause is the workflow, not the code.** `build.rs` *correctly*
gates every `-l...` link directive behind `#[cfg(feature = "...")]`
for `flint`/`spark`/`chapel`. The defect was `rust-ci.yml` forcing
those features on via `--all-features` on a runner with no `libflint`
/ GNAT / Zig FFI lib.

**Key distinction that shaped the fix:** only `cargo test` (and
`cargo build`) invoke the **linker**. `cargo clippy`, `cargo doc`,
`cargo check` type-check and lint the `cfg`-gated code **without
linking**, so they tolerate `--all-features` on a bare runner.

Therefore:

- `clippy`, `doc`, `check` → **keep `--all-features`** (full
  lint/compile coverage of flint/spark/chapel, zero infra cost).
- the two `cargo test` steps → **`--features verisim`** (the only
  pure-Rust optional feature; `live-provers ⊇ verisim`).

A blanket `--features verisim` everywhere was **rejected** because it
would stop CI ever compiling/linting ~510 LoC of `flint`
(`src/rust/coprocessor/flint.rs`) and the root-crate `spark`-gated FFI
(`src/rust/ffi/spark_axiom.rs`, `axiom_tracker.rs`) — a silent
coverage hole. `flint`/`spark`/`chapel` *test execution* stays covered
by their dedicated workflows (`chapel-ci.yml`, the SPARK Theatre Gate,
`live-provers.yml`).

Validated in CI: `Test Suite` goes ✗ on `main` → **✓ 3m18s** on #86;
local `cargo test --lib --features verisim` = 1092 passed, 0 failed.

## Decision 2 — clusterfuzzlite filename (#87)

The `google/clusterfuzzlite` `build_fuzzers` action hardcodes the path
`.clusterfuzzlite/Dockerfile` and exposes **no** filename input. House
style is `Containerfile` (Podman-not-Docker estate rule). Resolution:
a **tracked symlink** `.clusterfuzzlite/Dockerfile → Containerfile`
(git mode `120000`) — clusterfuzzlite resolves through it, the
canonical SPDX-headed file keeps the house name, zero blast radius
(nothing references `.clusterfuzzlite/Containerfile` by name). This
check is **non-gating**; the fix is hygiene so the fuzz job runs.

## Standing guidance (do not re-litigate)

- Before "fixing" a red echidna check: `git show origin/main:<path>`
  and check whether the same check is red on `main`. If yes → it is
  baseline rot or #77; **do not** patch it on the feature PR.
- Auto-merge (squash) is the norm here. Arm it; do **not**
  admin-override CI-gated PRs.
- `#77` is estate-infra. Symptoms: queued-forever jobs, ~15–30 s
  fast-fail with empty `--log-failed`. Not collapsible from a repo PR.
