<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->

# 2026-05-31 — Per-prover spawn hooks: cwd + filenameOverride

ADR-style record of the mechanism added to `ProverInfo` and
`tryProver` (`src/chapel/parallel_proof_search.chpl`) to handle
provers whose CLI invocation requires per-prover state at spawn
time. Closes issues #158 (Idris2 env hook) and #159 (Agda
filename hook), both surfaced by the Wave-1 MRR baseline
(`docs/bench/2026-05-30-chapel-mrr-baseline.md`).

## Status

Accepted. Implemented in the PR that introduces this ADR.

## Context

The L2.2 rehabilitation arc (#133 → PR #146) shipped the Chapel
metalayer with a single uniform `tryProver(info, goal, …)`
contract: every prover gets a temp file named
`goal_<ProverName>_<nodeId>.<fileExt>`, spawned from the parent's
CWD with the parent's environment. That contract held for ~22 of
the 30 registered backends (Coq, Lean, the SMT row, ATPs, etc.)
but two of the 30 — Idris2 and Agda — broke at spawn time:

- **Idris2** (`idris2 --check`) resolves its prelude relative to
  `IDRIS2_PREFIX` (or the install root) AND requires the source
  file to live inside the configured source directory. The
  Wave-1 invocation `idris2 --check /tmp/echidna-chapel/goal_Idris2_0.idr`
  failed with `Module Prelude not found` even when the parent
  shell had `IDRIS2_PREFIX` set, because the source file wasn't
  in the cwd Idris2 used as its source dir (the parent's cwd,
  not the temp dir).
- **Agda** (`agda --safe`) requires the source-file basename
  to be a valid Agda identifier AND the module declaration
  inside the file to match the basename. `goal_Agda_0.agda`
  is rejected by the lexer (`in the name 0, the part 0 is not
  valid because it is a literal`); even after fixing the
  lexer issue, Agda then enforces module-name = file-name and
  rejects mismatched module declarations.

The Wave-1 baseline (`docs/bench/2026-05-30-chapel-mrr-baseline.md`)
explicitly tracked these as caveats 1 + 2, deferred as Wave-2
follow-up issues (`#158`/`#159`).

## Decision

**Two new optional fields on `ProverInfo`** with empty-string
defaults that preserve the prior contract for the 28 provers
that don't need per-prover spawn state:

```chapel
record ProverInfo {
    var id: int;
    var name: string;
    // … existing fields …
    var cwd: string;              // "" = inherit parent CWD
    var filenameOverride: string; // "" = goal_<name>_<nodeId>.<ext>
}
```

A custom `proc init(…, cwd = "", filenameOverride = "")` keeps
all 30 existing registry call-sites compiling unchanged
(default arguments fill the new fields). A zero-arg `proc init()`
is also defined so `var provers: [0..29] ProverInfo` continues
to default-construct each slot — without it the custom positional
init would shadow Chapel's auto-generated zero-arg init and the
array declaration would fail to compile.

`tryProver` consumes both fields:

- **`filenameOverride`** swaps the generic
  `goal_<name>_<nodeId>.<fileExt>` for a literal basename (with
  extension) when set. The default form remains locale-id-suffixed
  so non-overriding provers stay collision-free across locales in
  multi-locale runs.
- **`cwd`** is implemented as a shell wrapper around the spawn:
  `sh -c "cd <cwd> && exec <executable> <args>"`. This is the
  thread-safe equivalent of `chdir()` — process-global `chdir`
  would race against other parallel spawn calls inside a
  `coforall`, but a per-subprocess `sh -c` keeps the directory
  change local. The parent's full environment (including
  `IDRIS2_PREFIX`, `IDRIS2_DATA_DIR`) is inherited regardless,
  per POSIX spawn defaults.

Registry entries updated:

- `provers[0]` (Agda) sets `cwd = "/tmp/echidna-chapel"` and
  `filenameOverride = "Trivial.agda"`. The fixture
  `tests/chapel_fixtures/agda_trivial.agda` declares
  `module Trivial where` to match.
- `provers[4]` (Idris2) sets `cwd = "/tmp/echidna-chapel"` and
  `filenameOverride = "Trivial.idr"`. The fixture
  `tests/chapel_fixtures/idris2_trivial.idr` already declared
  `module Trivial`, so its content is unchanged.

The Justfile `bench-chapel-mrr` recipe gained a derived
`IDRIS2_PREFIX` step: if the env var isn't set and `which idris2`
resolves, the recipe sets it to `dirname(dirname(realpath(which idris2)))`.
This means a user with idris2 on PATH no longer needs to remember
to export the prefix manually for `just bench-chapel-mrr` to
work end-to-end.

## Alternatives considered

1. **Per-prover env-extra list (key=value pairs)** — rejected as
   over-engineered. Chapel `spawn` inherits parent env by default;
   the only env hole was Idris2's `IDRIS2_PREFIX`, which the
   Justfile recipe now derives and exports parent-side. No prover
   in the current registry needs a per-spawn env override that
   isn't already in the parent.
2. **Auto-extract module name from goal content** (regex
   `^module\s+(\w+)`) — rejected as fragile. Works for clean
   fixtures but breaks on goals containing comments-before-module,
   pragmas, or multi-module files. The explicit
   `filenameOverride` field keeps the registry honest about which
   provers have basename constraints.
3. **Per-prover spawn callback (function pointer in the record)** —
   rejected for now: Chapel records with function fields are
   awkward to construct in a literal-initialiser-heavy registry,
   and the two-field mechanism handles every concrete need
   surfaced by Wave-1. Revisit if a third spawn-time wart appears.
4. **`POSIX_spawn`-style explicit cwd in Chapel `spawn`** — Chapel
   2.x `Subprocess.spawn` does not expose a `cwd` parameter at
   the time of writing (verified against the apt-shipped 2.3.0 and
   the source-built 2.8.0). The shell-wrapper workaround sidesteps
   the gap with no Chapel-version dependency.

## Consequences

**Positive.**

- `just bench-chapel-mrr` now shows `idris2_trivial → true` and
  `agda_trivial → true` across all three strategies, satisfying
  the explicit acceptance criteria for both #158 and #159.
- The hook pattern is general — future provers with similar
  module-name or working-directory requirements (Lean 4 already
  works out-of-the-box but a future fixture might trigger its
  `Lake` workspace check; Isabelle has session-name resolution)
  can be wired by adding two field values to their registry
  entry, no `tryProver` changes.
- The Wave-1 baseline document's caveats 1 + 2 (formerly tracked
  as Wave-2 follow-ups) are closed, leaving only caveat 3
  (sub-second wall-clock jitter, which is a measurement-method
  issue, not a metalayer defect).

**Negative.**

- Shell-wrapping every `cwd`-using prover costs one `fork+exec`
  for the `sh` itself per invocation. For 0.1-second prover runs
  this is ~5% overhead; for the 10-30 s real-corpus benchmark
  target (#161), it's negligible. If this becomes a hot path,
  switching to a direct-spawn cwd implementation (when Chapel
  exposes it) would remove the overhead.
- `filenameOverride` couples the registry entry to fixture
  content (the fixture's `module X where` declaration must match
  the override). This is acceptable because the fixture corpus
  is small and version-controlled together with the registry;
  a real-corpus runner would need a different convention (or
  the auto-extract approach from "Alternatives" above).

**Net.** Two scoped one-line additions to `ProverInfo` close
both acceptance-criterion-driven Wave-3 issues with no churn
to the 28 unaffected provers; the shell-wrapper approach buys
portability across Chapel 2.x runtimes; the Justfile derivation
of `IDRIS2_PREFIX` removes the last user-side env-export
ceremony.

## Toolchain version pinning

- `chpl 2.3.0` (CI) and `chpl 2.8.0` (local). The custom
  `proc init` syntax + `init this` invariant used here is
  stable across both.
- `idris2 0.8.0` (local). `IDRIS2_PREFIX`-based prelude
  resolution is the documented mechanism; the source-directory
  check is `idris2 --check`-specific (a `package`-driven build
  doesn't have the same constraint).
- `agda 2.6.3`. The module-name = filename rule is permanent
  Agda design (`Issue #1062` upstream).

These pins are re-stated in `chapel-ci.yml`, `Justfile`, and
`docs/decisions/2026-05-30-chapel-rehabilitation.md`.
