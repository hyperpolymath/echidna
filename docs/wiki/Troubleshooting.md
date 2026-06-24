<!-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
# Troubleshooting

## Build fails with `openssl` errors

```bash
# Guix (recommended)
guix shell openssl pkg-config -- just build

# Fedora / RHEL
sudo dnf install openssl-devel pkg-config

# Debian / Ubuntu
sudo apt install libssl-dev pkg-config
```

## Prover binary not found

The 12 core backends require their binaries on PATH. Diagnose:

```bash
just doctor
# or manually
which coqc lean idris2 isabelle z3 cvc5 vampire eprover
```

Install via Guix manifest:

```bash
guix shell -m manifests/live-provers.scm -- just doctor
```

Or use the sealed container:

```bash
podman build -f .containerization/Containerfile.wave3 -t echidna:wave3 .
podman run --rm -it echidna:wave3 just doctor
```

## Sandbox permission errors

ECHIDNA uses Podman or bubblewrap for solver containment. On SELinux systems:

```bash
sudo setsebool -P container_use_devices 1
```

If Podman rootless fails with subuid/subgid issues:

```bash
# Verify user namespaces are configured
podman system migrate
```

## `cargo test` fails with a Julia error

The ML sidecar tests require Julia 1.10+ on PATH. They're feature-gated; to run only the Rust-pure unit tests:

```bash
cargo test --lib                    # 1067 unit tests, no Julia needed
cargo test --test gnn_augment_integration  # mock-server integration, no Julia needed
```

The full integration tests that exercise Julia live behind `--features verisim` and require both `VERISIM_URL` reachable and the Julia server running. See [`docs/ENV-VARS.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/ENV-VARS.md).

## `just train-cpu` errors with "Manifest not found"

Julia dependencies need instantiation on first run:

```bash
julia --project=src/julia -e 'using Pkg; Pkg.instantiate()'
```

If the manifest is stale relative to your Julia version:

```bash
julia --project=src/julia -e 'using Pkg; Pkg.update()'
```

Note: `Pkg.update()` regenerates `Manifest.toml`; commit it if the update is intentional.

## `cargo fmt --check` fails in CI

Apply locally and commit:

```bash
cargo fmt
git add -A && git commit -m 'chore(fmt): apply cargo fmt'
```

## CI is red on `main` (perpetual queued)

This is a known infra-side issue tracked in [issue #77](https://github.com/hyperpolymath/echidna/issues/77). Structural fixes (concurrency blocks, correct `runs-on:`) have landed; the runner-availability root cause is org-level and out of band for the codebase.

## VeriSimDB unreachable

VeriSimDB is in a sibling repo (`verification-ecosystem/verisimdb`). Without it, the learning loop is read-only:

```bash
# Default
export VERISIM_URL=http://localhost:8080

# Or skip the loop:
cargo build  # without --features verisim
```

See [`docs/handover/S4-LOOP-CLOSURE-RUNBOOK.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/handover/S4-LOOP-CLOSURE-RUNBOOK.md) for the operational details.

## Corpus adapter returns empty Corpus

If `corpus::<adapter>::ingest(root)` returns a `Corpus` with `entries.is_empty()`:

1. **Confirm the root path.** Adapters take the *project* root, not an individual source file. Check the path resolves and is a directory.
2. **Check walk exclusions.** Each adapter excludes build / VCS / heap caches (e.g. Isabelle skips `*/heaps/*`, Coq skips `_build/`, …). If your tree uses non-standard out-of-tree build directories, files under them won't be indexed.
3. **Verify the file extension matches.** The [`docs/CORPUS-ADAPTERS.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/CORPUS-ADAPTERS.md) table lists the canonical extensions per adapter (`*.thy` for Isabelle, `*.mm` for Metamath, `*.fst` / `*.fsti` for F\*, etc.). Non-canonical extensions (e.g. `.hol4` instead of `*Script.sml`) are silently skipped.

## Synonym lookup returns empty

If `SynonymTable::load(ProverKind::X, dir)?.alternatives("name")` returns `vec![]`:

1. **Confirm the TOML exists** at `data/synonyms/<prover>.toml`. `SynonymTable::load` returns an empty table (without error) if the file is missing — verify with `ls data/synonyms/`.
2. **Check the schema.** Rows must be `[[synonym]]`, not `[[entries]]` or `[[entry]]`. Each row needs `canonical = "..."` and `aliases = [...]` at minimum. Anything else parses as zero entries.
3. **Verify the filename mapping** in `prover_table_filename` in [`src/rust/suggest/synonyms.rs`](https://github.com/hyperpolymath/echidna/blob/main/src/rust/suggest/synonyms.rs). The canonical filenames are: `agda.toml`, `coq.toml`, `lean4.toml` (note the `4`), `idris2.toml`, `isabelle.toml`, `metamath.toml`, `mizar.toml`, `hol4.toml`, `hol_light.toml` (underscore), `dafny.toml`, `why3.toml`, `fstar.toml`, `acl2.toml`. Mismatches resolve to an empty table.
4. **Cross-prover dictionaries are different.** `_msc2020.toml`, `_wordnet_math.toml`, `_conceptnet_seed.toml` load via `load_cross_prover_dicts`, not `SynonymTable::load`; merge them into a per-prover table with `merge_external()`.

## Bayesian arbiter posterior stuck at 0.5

If `BayesianArbiter::combine(&evidence)` returns `p_proven ≈ p_refuted ≈ 0.5`:

The likely cause is that every `ProverEvidence` in your slice carries `Verdict::Timeout`, `Verdict::Unknown`, or `Verdict::Error`. Those verdicts contribute a likelihood ratio of 1.0 — no log-odds update — so the posterior stays at the prior. See the `timeouts_only_leave_entropy_at_prior_entropy` test in `src/rust/verification/bayesian_arbiter.rs`.

**Fix**: feed at least one `Verdict::Proven` or `Verdict::Refuted`. If your prover never returns a decisive verdict, either raise its timeout budget (`DispatchConfig::timeout`) or replace it with a different backend for that goal class.

## Dempster-Shafer returns HighConflict error

`DempsterShaferArbiter::combine_all()` returns `Err(ArbiterError::HighConflict(k))` when the cumulative conflict mass `k > 0.95` — the provers are strongly disagreeing and DS refuses to commit a posterior on principle.

**Options**:

- Use the **Bayesian arbiter** with a strong prior (e.g. `BayesianArbiter::new(0.99)`) if you have a domain reason to favour one outcome.
- Use the **Pareto arbiter** (`src/rust/verification/pareto_arbiter.rs`) if the disagreement reflects multi-axis trade-offs rather than truth-value conflict.
- Investigate the evidence — high conflict often signals a bug in one prover's harness (wrong axioms loaded, stale binary, sandbox leakage) rather than a genuine logical disagreement.

## Hazard flag is set unexpectedly

`AxiomUsage::other` (and the boolean flags) are filled by **heuristic** scanners in each corpus adapter. They run against comment-stripped source and can false-positive when a banned token appears inside a string literal, an ML antiquotation, or a doc-comment fragment that survived stripping.

Review the `axiom_usage.other` strings on the offending `CorpusEntry` — they record the exact substring that triggered the flag. If it's inside a literal, the flag is heuristic noise; the adapter doc-strings (e.g. the Isabelle module-doc) explicitly note that "banned tokens inside ML antiquotations or string literals can still be flagged for human review."

The adapters are deliberately quality "heuristic, not authoritative" — see [`docs/CORPUS-ADAPTERS.md`](https://github.com/hyperpolymath/echidna/blob/main/docs/CORPUS-ADAPTERS.md) and the module-level docs on `src/rust/corpus/mod.rs`. If false positives accumulate for your project, file an issue with the triggering substring; the heuristic can be tightened per-adapter.

## Wiki page is wrong

This wiki is a navigation aid. **The repo wins.** File an issue or PR against the doc the wiki page points to; the wiki itself is refreshed periodically from the repo state.
