# Echidna L3 — Live-Prover CI — Continuation Prompt

**Context**: Echidna (`/var/mnt/eclipse/repos/verification-ecosystem/echidna/`) has 48 trait-wired
prover backends, but CI only tests them with `MockProver`. Mission: make every provisionable
backend run against a canonical micro-goal on a predictable cadence. Guix primary, Nix fallback.

**Master plan**: `~/Desktop/ECHIDNA-PRODUCTION-WIRING-PLAN.md`
**Order**: L3 (this) → L1 (Cap'n Proto) → L2 (Chapel max).

---

## Where L3 is when this prompt fires

Wave-1 (Tier-1, every PR — 9 backends) DONE in kickoff session, commit `b022bf4`:
- `manifests/live-provers.scm` — Guix manifest with Tier-1 + Tier-2 provers
- `flake.nix` — expanded with matching `liveProverDeps`
- `.github/workflows/live-provers.yml` — tiered workflow (Tier-1 PR, Tier-2 nightly, etc.)
- `tests/live_prover_suite.rs` — Rust test harness with Tier-1 version-check tests

Wave-2 (Tier-2, nightly — 10 backends) **DONE 2026-04-19** in commits `9a4aeeb` + `6717b12`:
- Real provisioning commands for coq, agda, why3 (apt); idris2 (source bootstrap
  against Chez Scheme); lean4 (elan); isabelle (Isabelle2024 tarball); dafny
  (`dotnet tool install --global Dafny`); fstar (GitHub release tarball, binary
  `fstar.exe`); tlaps (self-extracting installer for `tlapm`).
- `hol-light` **deferred** to Wave-3 container path — no prebuilt binary and opam
  build is ~20 min + camlp5.
- `tests/live_prover_suite.rs` extended with `live_fstar_version` + `live_tlaps_version`.
- Local verification (not CI yet): 18/18 tests pass, 13 backends return real versions,
  5 auto-skip when binaries are absent.

`tests/live_goals/` was listed in the handover-artefacts but not actually created.
Wave-2 version-check tests do not need it; Wave-2 / Wave-3 goal-check extensions will.

## What to finish in L3 (remaining)

### Wave-2 verification in CI (not just local)
The Wave-2 provisioning installers are not yet exercised by a real CI run —
nightly needs to fire (cron `0 3 * * *`) to surface any CI-specific breakage
(apt mirror changes, GitHub release URL format drift, dotnet sdk availability,
etc.). Watch the next nightly after merge; fix any red matrix cells in-place.

### Wave-3: Tier-3 backends (Weekly)
Container/special-env path: Tamarin, ProVerif, Imandra, SCIP, OR-Tools, HOL4, ACL2, Twelf, Metamath.
These likely need per-backend Containerfiles (Podman, not Docker — per project CLAUDE.md).

### Wave-4: Tier-4 backends (Quarterly, allow-fail)
Best-effort: Mizar, Nuprl, PVS, Minlog, Dedukti, Arend, KeY, Prism, UPPAAL, ViPER, NuSMV, Spin,
TLC, CBMC, Seahorn, dReal, Boogie, Kissat, Alloy. Many will stay mock-only (document why).

### Harden wiring depth for shallow backends
Audit flagged **Dafny (165 LoC)** as stub-ish — upgrade to deep during L3 so the live test isn't
measuring a broken subprocess wrapper.

### VeriSimDB integration
Per `feedback_verisimdb_policy`: the live-prover harness should emit a VeriSimDB record per run
(prover, goal, outcome, duration, exit code). Schema TBD — coordinate with VeriSimDB repo.

## Acceptance for L3 complete

- Tier-1 green on every PR
- Tier-2 green on nightly (or documented flaky backends with `continue-on-error: true`)
- Tier-3 runs weekly with per-backend allow-fail
- Tier-4 runs quarterly, results archived
- Dafny upgraded from 165 LoC stub to deep subprocess wiring
- `guix shell -m manifests/live-provers.scm -- just test-live` works locally
- VeriSimDB records emitted (if schema ready)
- Mock tests retained as fast pre-CI smoke

## Hand to L1 when

- All four waves land or are explicitly deferred with rationale in STATE.a2ml
- Tier-1 has run green on main for ≥7 days

---

## Rules active in this session

- GitHub-only mirroring (per memory `feedback_github_only_mirroring`)
- Commit ASAP, specific paths (`feedback_commit_asap`)
- Pre-commit: `panic-attack assail` (`feedback_panic_attack_precommit`)
- No `.unwrap() → .expect("TODO")` refactor (`feedback_unwrap_to_expect_antipattern`)
- Session close marker: `SAFE TO CLOSE` literal at end of final message

## Key files to read first

1. `~/Desktop/ECHIDNA-PRODUCTION-WIRING-PLAN.md`
2. `/var/mnt/eclipse/repos/verification-ecosystem/echidna/.machine_readable/6a2/STATE.a2ml`
3. `/var/mnt/eclipse/repos/verification-ecosystem/echidna/manifests/live-provers.scm`
4. `/var/mnt/eclipse/repos/verification-ecosystem/echidna/.github/workflows/live-provers.yml`
5. `/var/mnt/eclipse/repos/verification-ecosystem/echidna/tests/live_prover_suite.rs`
