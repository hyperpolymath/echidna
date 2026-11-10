# SPDX-License-Identifier: MPL-2.0
# Imported by the root Justfile (hotspot split); recipes moved verbatim.

# ─────────────────────────────────────────────────────────────────────
# Saturation campaign 2026-06-01 — recipes for the new corpus / vocab /
# arbiter / exchange surface. See docs/decisions/2026-06-01-saturation-
# campaign.md and docs/CORPUS-ADAPTERS.adoc.
# ─────────────────────────────────────────────────────────────────────

# Ingest a project tree via one of the 13 new corpus adapters
# (isabelle / metamath / mizar / hol_light / hol4 / dafny / why3 /
#  fstar / acl2_books / tptp / smtlib / proofnet / minif2f).
corpus-ingest-saturation adapter root:
    cargo run --bin echidna -- corpus ingest --root {{root}} --adapter {{adapter}}

# Ingest an Ada/SPARK tree (specs `*.ads`, bodies `*.adb`). Detects
# GNATprove escape hatches (`pragma Assume`, suppressed checks) and the
# sparklib `Lemma_*` convention.
corpus-ingest-spark root:
    cargo run --bin echidna -- corpus ingest --root {{root}} --adapter spark_ada

# Ingest a Rust/Creusot tree (`#[requires]` / `#[ensures]` / `pearlite!`).
# `#[trusted]` is reported as a postulate, not as a proved function.
corpus-ingest-creusot root:
    cargo run --bin echidna -- corpus ingest --root {{root}} --adapter creusot

# Ingest the hyperpolymath estate: every repo's `src/abi` Idris2 tree plus
# the Agda type-theory libraries (echo/epistemic/secret/tropical/
# choreographic-types), merged into one corpus tagged with repo + layer.
# ROOT is the directory that contains the repositories.
corpus-ingest-estate root="..":
    cargo run --bin echidna -- corpus ingest --root {{root}} --adapter hyperpolymath_estate

# Run the corpus-stats summary across all 20 adapter outputs found under
# data/corpus/*.json (skips any missing without failing).
corpus-stats-all:
    @for f in data/corpus/*.json; do \
        [ -f "$f" ] || continue; \
        echo "--- $f"; \
        cargo run --bin echidna --quiet -- corpus stats --index "$f" 2>/dev/null || echo "  (skipped)"; \
    done

# Load every per-prover synonym TOML + the 5 cross-prover dictionaries
# (_msc2020 / _wordnet_math / _conceptnet_seed / _disciplines /
# _verification_systems) and report counts.
synonym-load-test:
    cargo test --lib --quiet suggest::synonyms 2>&1 | tail -20

# Lexicon v2: apply the Nickel contract (data/synonyms/schema.ncl) to every
# synonym table and to the accept/reject fixtures. Needs nickel >= 1.12.
lexicon-check:
    scripts/lexicon-check.sh
    cargo test --locked --test lexicon_v2_test

# Mine lexicon candidates across training_data/ corpora: cognates, false
# friends and synonym candidates as JCS JSON Lines under target/lexicon-scan.
# Flag-only (evidence = none); never edits data/synonyms/. Presets: learning,
# spanning, in-family, full.
lexicon-scan preset="learning":
    cargo run --locked --bin echidna -- lexicon scan --preset {{preset}}
    cargo test --locked --test lexicon_scan_test

# Run the saturation-campaign cargo tests only (139 cases + 1 ignored).
test-saturation:
    cargo test --lib -- \
        corpus:: \
        verification::bayesian_arbiter \
        verification::dempster_shafer \
        verification::pareto_arbiter \
        exchange::tptp \
        exchange::smtlib \
        exchange::smtcoq \
        exchange::lambdapi \
        suggest::synonyms

# Smoke-test the arbiter trio with synthetic evidence.
# Prints posterior verdict from each of: Bayesian, Dempster-Shafer, Pareto.
arbiter-smoke:
    cargo run --bin echidna --quiet -- arbiter smoke 2>/dev/null || \
        echo "(arbiter-smoke CLI not yet wired — see src/rust/verification/{bayesian,dempster_shafer,pareto}_arbiter.rs for unit-test entry points)"

# Validate that the E-R schema doc + Cap'n Proto schema are
# byte-identical with the recorded SHA in .machine_readable/er-schema.sha256.
# (CI gate planned — see docs/architecture/VERISIM-ER-SCHEMA.adoc
#  "Drift detection".)
er-schema-drift-check:
    @echo "Checking E-R schema drift..."
    @sha256sum docs/architecture/VERISIM-ER-SCHEMA.adoc \
               crates/echidna-wire/schemas/verisim_er.capnp \
               | sha256sum | head -c 64
    @echo " (current combined hash; compare against .machine_readable/er-schema.sha256 when CI gate lands)"


secret-scan-trufflehog:
    @command -v trufflehog >/dev/null && trufflehog filesystem . --only-verified || true
