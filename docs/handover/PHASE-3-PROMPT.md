<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
# Echidna Phase 3 — Real-Algebraic + Modal/Hybrid Backends — Opus Handoff Prompt

**Context**: Phase 3 of the ECHIDNA expansion is the
**architecturally trickiest** of the three remaining phases. Unlike
Phases 2B and 4, where the backends are mostly subprocess CAS shells
or DL/probabilistic solvers with familiar shapes, Phase 3 brings in
*differential dynamic logic*, *cylindrical algebraic decomposition*,
*Reduce-CAS shims*, *connection-method intuitionistic / modal*, and
*tableau generators for arbitrary modal logics*. Per the
**ECHIDNA-EXPANSION-TOMORROW-2026-04-28** plan: "Don't farm these
out. Pick a 2-3 hour midweek slot and ask Opus to do them solo. Each
is ~250 LOC but the semantics matter."

This document is **that brief**. It locks the design for all 7
remaining Phase 3 backends, names the worked example already landed
(`keymaerax.rs`), and gives the next Opus session a step-by-step path
to closing the phase.

**Master plan**: `~/Desktop/ECHIDNA-EXPANSION-TOMORROW-2026-04-28.md`
**Reference doc**: `docs/ROADMAP.md` row "Every important solver"
**Status as of 2026-04-27**: KeYmaera X **landed** in
`src/rust/provers/keymaerax.rs` (8/8 tests passing); 6 backends
remain.

## Status table

| Backend | Status | LOC | Notes |
|---|---|---|---|
| **KeYmaera X** (dDL / hybrid systems) | ✅ landed 2026-04-27 | 313 | Worked example for this brief |
| **QEPCAD-B** (cylindrical algebraic decomposition) | 🟡 open | ~250 | CAD input format |
| **Redlog** (Reduce-CAS frontend, real algebra) | 🟡 open | ~250 | Reduce shim + real-quantifier elim |
| **MleanCoP** (connection-method intuitionistic) | 🟡 open | ~250 | Prolog-based, esoteric output |
| **ileanCoP** (intuitionistic leanCoP variant) | 🟡 open | ~250 | Shares parser with MleanCoP |
| **nanoCoP** (lean-er connection prover) | 🟡 open | ~250 | Same family as above |
| **MetTeL2** (tableau generator for modal logics) | 🟡 open | ~250 | JVM, configuration-heavy |

Total expected: ~1500 LOC + tests for the 6 remaining.

## Architectural patterns (per-backend semantics)

### KeYmaera X (✅ already done — worked example)

- **Input format**: `.kyx` archive entries with hybrid programs.
- **Output**: stdout/stderr scan for `proved` / `closed` / `qed` (closed)
  vs `open subgoals` / `failed` / `untrusted` (open or refuted).
- **Trust tier**: 2 (delegates QE to external CAS — Mathematica/Z3/Polya).
- **FFI u8**: 128.
- **Reference**: `src/rust/provers/keymaerax.rs`. Use this as the
  template for the remaining six.

### QEPCAD-B (CAD)

- **Input**: prefixed-formula syntax for real-quantifier elimination
  problems. Header with variable order, then `(quantifier x)[ formula ]`.
- **CLI invocation**: stdin-driven REPL; backends typically pipe
  the QEPCAD input followed by `finish` to flush.
- **Output**: prints either `Equivalent quantifier-free formula:
  <expr>` (success) or error / `unable to compute`. Consider
  formula `True` / `False` as `verify_proof` outcome.
- **Trust tier**: 2 (CAD result is sound but the implementation is
  large; no external proof certificate).
- **Hazard**: very long runtimes for formulae with > 4 variables;
  honour the timeout aggressively.

### Redlog (REDUCE-CAS frontend)

- **Input**: REDUCE-CAS surface syntax — `rlqe formula;` for QE,
  `rlcad` for CAD-based decision, etc. Statements terminated with
  `;` or `$` (silent).
- **CLI invocation**: spawn `redcsl` (CSL build of Reduce) or
  `redpsl`, feed the Redlog `load_package redlog;` then the goal,
  read stdout.
- **Output**: scan for `true`, `false`, or a residual quantifier-free
  formula. `true` → `verify_proof` returns `Ok(true)`; everything
  else either `Ok(false)` or `Err`.
- **Trust tier**: 2 (parallel to QEPCAD).
- **Hazard**: Reduce sometimes prints leading whitespace and
  `END OF FILE` markers. Strip carefully.

### MleanCoP / ileanCoP / nanoCoP (connection-method)

These three share a parser and CLI shape; implement them as **three
backend files** but factor common helpers into a private
`connection_method.rs` module if the duplication exceeds ~30 LOC.

- **Input**: TPTP CNF/FOF (MleanCoP) or intuitionistic / modal
  variants (ileanCoP, nanoCoP).
- **CLI invocation**: Prolog-driven; typical call is
  `swipl -g "leancop:prove('input.p')" -t halt`. Variants differ in
  the `prove/1` predicate name.
- **Output**: lines like `% SZS status Theorem` /
  `% SZS status CounterSatisfiable` / `% SZS status GaveUp`
  (when the upstream uses TPTP-style SZS) OR plain
  `+ matrix proof found` (when in native mode).
- **Trust tier**: 2 for MleanCoP (classical), 3 for ileanCoP
  (intuitionistic kernel is small — connection method) and nanoCoP
  (similarly small kernel).
- **Hazard**: Prolog stack overflow on goals with deep unification —
  bound the heap with `--stack-limit=256m`.

### MetTeL2 (tableau generator)

- **Input**: a tableau **specification** (logic axioms in MetTeL's
  syntax) plus a goal formula. Different from a one-shot prover —
  MetTeL2 generates a tableau prover *for* the supplied logic, then
  uses it. We only support the "use the bundled standard logics"
  path for v1 (S4, K, KT, KD45, ...).
- **CLI invocation**: `java -jar mettel2.jar -s <logic>.spec
  -i <input>.mt` (typical). Wrap with `-version` probe.
- **Output**: `Provable.` / `Not provable.` / `Unknown.` (tableau
  open).
- **Trust tier**: 2 — the generated tableau prover is correct by
  construction, but we don't formally check the spec.
- **Hazard**: JVM cold-start latency. Cache the JVM via
  `--keep-alive` if benchmark numbers ask for it later.

## What "landed" looks like (using KeYmaera X as the template)

For each backend, you produce:

1. **Backend file** at `src/rust/provers/<name>.rs`. Mirror
   `keymaerax.rs`:
   - Crate-level `//!` doc explaining *why this backend exists* and
     the *input format / output parsing*.
   - Module-level `#![allow(dead_code)]` (warranted: tests are
     gated by `#[cfg(test)]`).
   - `pub struct <Name>Backend { config: ProverConfig }`.
   - `impl <Name>Backend { new, to_<format>, parse_result }`.
   - `#[async_trait] impl ProverBackend for <Name>Backend` —
     `kind`, `version`, `parse_file`, `parse_string`, `apply_tactic`
     (return `anyhow::anyhow!(... not supported ...)` if
     non-interactive), `verify_proof`, `export`,
     `suggest_tactics` (return `Ok(vec![])` for v1),
     `search_theorems` (return `Ok(vec![])`), `config`, `set_config`.
   - `#[cfg(test)] mod tests` with at minimum: `_kind`,
     `_to_<format>_basic`, `_parse_result_proved`,
     `_parse_result_failed`, `_parse_result_inconclusive`.

2. **mod.rs wiring** — add the backend at all 10 integration points.
   Use `keymaerax` as the search anchor for each:

   1. `pub mod <name>;` at the top of `mod.rs` (~line 70).
   2. `<Name>` variant in the `ProverKind` enum.
   3. Match arm in the name parser (`"<name>" | "<alias>" =>
      Ok(ProverKind::<Name>)`).
   4. `ProverKind::<Name>,` in the `all()` list (~line 700).
   5. `ProverKind::<Name> => <complexity>,` in the complexity table
      (~line 800).
   6. `ProverKind::<Name> => <trust>,` in the trust tier table
      (~line 960).
   7. `ProverKind::<Name> => <ml_score>,` in the ML guidance table
      (~line 1090).
   8. `ProverKind::<Name> => "<binary>",` in the binary-name table
      (~line 1224).
   9. `ProverKind::<Name> =>
      Ok(Box::new(<name>::<Name>Backend::new(config))),` in the
      factory dispatch (~line 1614).
   10. **FFI: u8 mapping at `src/rust/ffi/mod.rs`** — add
       `<n> => Some(ProverKind::<Name>),` to `kind_from_u8` and
       `ProverKind::<Name> => <n>,` to `kind_to_u8`. KeYmaera X took
       slot 128; the remaining six get 129..134 in the order:
       QEPCAD-B (129), Redlog (130), MleanCoP (131),
       ileanCoP (132), nanoCoP (133), MetTeL2 (134). MetiTarski is
       already at its existing slot — do not renumber existing
       entries.

3. **Tests** — at minimum 8 unit tests per backend (the count
   `keymaerax.rs` ships). Pattern after the `keymaerax::tests`
   block.

4. **Acceptance gate**: `cargo build --lib` clean (no new warnings
   beyond the pre-existing four), `cargo test --lib <name>`
   passes 100%, `cargo test --lib` overall green.

## Sequencing recommendation

The six remaining backends differ wildly in semantics. Suggested
order — **easiest first** (sets up the dispatch wiring once, then
the harder ones reuse it):

1. **QEPCAD-B** — clean CAD input, well-documented stdout markers.
2. **Redlog** — same shape as QEPCAD but uses Reduce CSL; reuse
   subprocess pattern.
3. **MetTeL2** — JVM call, simple stdout parse.
4. **MleanCoP** — Prolog binding, TPTP I/O.
5. **ileanCoP** — share helpers with MleanCoP; intuitionistic
   nuances in `parse_result`.
6. **nanoCoP** — share helpers with the leanCoP family; lighter
   tactic surface.

Budget ~30 minutes per backend file + ~15 minutes for the 10
integration points + ~15 minutes for tests + verification = 1 hour
per backend. Whole phase: 6 hours. Don't try to compress; semantics
matter.

## Per-backend FFI u8 reservations

Already fixed in mod.rs/ffi.rs. Repeat here so a future Opus session
doesn't have to re-derive them:

| Backend | FFI u8 |
|---|---|
| KeYmaera X | 128 |
| QEPCAD-B | 129 |
| Redlog | 130 |
| MleanCoP | 131 |
| ileanCoP | 132 |
| nanoCoP | 133 |
| MetTeL2 | 134 |

## Acceptance criteria for the *phase*

1. All 6 remaining backend files exist under `src/rust/provers/`.
2. `cargo build --lib` clean (0 errors, no new warnings).
3. `cargo test --lib` passes (every existing test green plus
   ≥ 6 × 8 = 48 new backend tests).
4. `provers/mod.rs` `all()` list contains all 7 Phase 3 backends.
5. Each backend's `verify_proof` calls the upstream binary with the
   correct flag — gated such that **missing binary returns a
   structured error**, not a panic. (KeYmaera X already does this
   via `Command::spawn().context(...)`.)
6. `docs/ROADMAP.md` row "Every important solver" updated with the
   new ProverKind count (currently 128 → 134 after Phase 3 closes).
7. `PROOF-NEEDS.md` and `.machine_readable/6a2/STATE.a2ml`
   reflect the closure of Phase 3.

## Non-goals

- **No upstream binary provisioning.** The CI containers don't have
  KeYmaera X, QEPCAD-B, Redlog, leanCoP family, or MetTeL2
  installed; integration tests gated by `#[cfg(feature =
  "<name>-real")]` are out of scope here. Document the gap.
- **No Bellerophon / leanCoP tactic-language dispatch.** All
  Phase 3 backends route through `verify_proof` only; interactive
  `apply_tactic` returns the "not supported" error per the
  KeYmaera X pattern.
- **No GNN integration for these backends.** The GNN ranking layer
  (§4.4 of ECHIDNA-NOTES) is a separate phase; Phase 3
  `suggest_tactics` returns `Ok(vec![])`.
- **No formal proofs of `verify_proof` correctness for Phase 3.**
  These are dispatch-only backends; their outputs feed the
  `compute_trust_level` pipeline at most. Trust tier 2 is the
  ceiling without certificate output.

## Test fixtures (where they should live)

For each backend, add a tiny `tests/fixtures/<name>/` directory
containing 2-3 `.kyx` / `.qep` / `.red` / `.p` / `.mt` example
problems lifted from the upstream documentation. These are *not*
loaded in the unit tests (which use string literals); they exist
for hand-running `echidna prove` against a local install during
development.

## What you (Opus, future session) should NOT do

- **Do not implement Bellerophon / leanCoP tactic compilation**
  inside the backend file. That is a separate ~1500 LOC project
  per the ECHIDNA-NOTES §4.1 design.
- **Do not add upstream-binary auto-detection logic** to mod.rs.
  Keep the binary-name table simple; deployment-time
  configuration handles binary location.
- **Do not modify the trust pipeline** (`src/rust/dispatch.rs`,
  `verification/`) to "support" the new backends. They plug in
  through the existing `ProverBackend` trait; no pipeline edit
  should be necessary.
- **Do not break MetiTarski**. It's already shipped (Phase 1B,
  cbd9449); it stays at trust tier 2 / FFI slot whatever it has.
  Don't reshuffle existing FFI numbers.

## How to verify phase completion (5-minute sanity check)

```bash
cd /var/mnt/eclipse/repos/echidna
cargo build --lib                                # 0 errors
cargo test --lib qepcad redlog mleancop ileancop nanocop mettel2 keymaerax  \
                                                  # all green
grep -c "ProverKind::" src/rust/provers/mod.rs   # should rise by 6
git log --oneline | head -10                     # 6 fresh feat() commits
```

## Tracking

- This brief: `docs/handover/PHASE-3-PROMPT.md`
- Master plan: `~/Desktop/ECHIDNA-EXPANSION-TOMORROW-2026-04-28.md`
- Worked example: `src/rust/provers/keymaerax.rs` (committed
  2026-04-27)
- Companion handoff: `docs/handover/SUGGEST-CLI-PROMPT.md`
  (the §4.1/4.3 mechanical-baseline brief from the same session)

When Phase 3 closes, update this file's status table to all-green,
move the doc to `docs/handover/archived/`, and link the closing
commits.
