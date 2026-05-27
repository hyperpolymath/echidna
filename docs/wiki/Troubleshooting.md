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

## Wiki page is wrong

This wiki is a navigation aid. **The repo wins.** File an issue or PR against the doc the wiki page points to; the wiki itself is refreshed periodically from the repo state.
