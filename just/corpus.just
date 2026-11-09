# SPDX-License-Identifier: MPL-2.0
# Imported by the root Justfile (hotspot split); recipes moved verbatim.

# ── Corpus / training pipeline ─────────────────────────────────
#
# Five steps in order: provision upstream mirrors, run every extractor,
# merge per-prover proof_states into UNIFIED, align the premise files
# to UNIFIED's fresh ids, then retrain.  Each step is idempotent;
# re-running only touches what has changed.  See
# scripts/provision_corpora.sh --list for the source catalogue.

# Clone every upstream prover corpus into external_corpora/.
# Pass specific names to provision a subset: `just provision-corpora metamath mathlib4`.
provision-corpora *NAMES:
    @if [ -z "{{NAMES}}" ]; then \
        scripts/provision_corpora.sh --all; \
    else \
        scripts/provision_corpora.sh {{NAMES}}; \
    fi

# Report which upstream corpora are on disk and their sizes.
corpora-status:
    scripts/provision_corpora.sh --status

# Run every scripts/extract_*.jl against the provisioned corpora.
# Pass names to run a subset: `just extract-corpora metamath mathlib4`.
extract-corpora *NAMES:
    scripts/extract_all.sh {{NAMES}}

# Merge per-prover proof_states_*.jsonl into proof_states_UNIFIED.jsonl
# with fresh sequential ids (dedupes by prover+theorem).
merge-corpora:
    julia --project=src/julia scripts/merge_corpus.jl

# Rebuild premises_COMPLETE.jsonl with proof_ids that match UNIFIED.
# merge-corpora rewrites every proof_state id to a fresh sequential
# counter; the premise files keep the original extractor ids, so this
# step re-joins premises to UNIFIED via (prover, theorem) — the durable
# key merge_corpus.jl already dedupes on.  Without this step the
# dataloader's proof_id join matches ~0% of records.
align-premises:
    julia --project=src/julia scripts/align_premises.jl

# Full retrain from provisioned corpora.  Honours ECHIDNA_MAX_PROOF_STATES
# (0 = unlimited), ECHIDNA_NUM_EPOCHS, ECHIDNA_NUM_NEGATIVES.
#
# Depends on align-premises: without that step the dataloader joins
# premise.proof_id against proof_state.id and fails at ~0% match because
# merge_corpus.jl rewrites proof_state ids to fresh sequential counters
# while the premise files keep the original per-extractor ids.  Running
# align-premises is idempotent and cheap (seconds on a 2M premise set).
retrain: align-premises
    julia --project=src/julia src/julia/run_training.jl

# Retrain without the align-premises prerequisite — use only when you
# know premises_COMPLETE.jsonl is already aligned (e.g. you just ran
# just align-premises manually and want to iterate on model code).
retrain-skip-align:
    julia --project=src/julia src/julia/run_training.jl

# Full training run on the real corpus (auto-selects GPU when available).
# Honours ECHIDNA_MAX_PROOF_STATES, ECHIDNA_NUM_EPOCHS, ECHIDNA_NUM_NEGATIVES.
# Produces models/neural/{premise_selector,tactic_predictor}.bson, vocab.json,
# updates models/model_metadata.txt, and appends to training_data/metrics_baseline.jsonl.
train:
    julia --project=src/julia src/julia/run_training.jl

# CPU smoke pass: 2000 proof states, 2 epochs — fast end-to-end sanity check.
# Safe to run on any dev box without a GPU.  Produces the same artefacts as `train`.
train-cpu:
    ECHIDNA_MAX_PROOF_STATES=2000 ECHIDNA_NUM_EPOCHS=2 julia --project=src/julia src/julia/run_training_cpu.jl

# Evaluate trained model on held-out validation split (MRR / top-k).
# Requires `just train-cpu` (or `just train`) to have produced models/neural/.
# Appends one JSONL row to training_data/eval_results.jsonl and exits non-zero
# if MRR < 0.66 (below the cosine baseline).
eval:
    julia --project=src/julia src/julia/eval_held_out.jl

# End-to-end pipeline: provision → extract → merge → align → retrain.
# Use `ECHIDNA_MAX_PROOF_STATES=0 just corpus-refresh` to lift the sample cap.
corpus-refresh: provision-corpora extract-corpora merge-corpora align-premises retrain

# Run training using the saturation-campaign corpus adapters as the
# data source. Requires `just provision-corpora` to have populated
# data/corpus/ first. Per-prover invocation; default lean.
train-from-corpus prover="lean":
    @julia --project=src/julia src/julia/run_training.jl \
        --prover {{prover}} \
        --corpus-json $(ls data/corpus/*.json | tr '\n' ',') \
        --synonyms-dir data/synonyms

# Run the eight-axis metrics suite against the current corpus and post
# results to VeriSimDB. Falls back to training_data/metrics_<run_id>.jsonl
# if VERISIM_URL is unreachable. Target values are documented in
# metrics/README.adoc.
metrics:
    julia --project=src/julia metrics/run_all.jl

# Report corpus balance across provers from stats_UNIFIED.json.
corpus-stats:
    @julia -e 'using JSON3, Printf; \
      s = JSON3.read(read("training_data/stats_UNIFIED.json", String)); \
      counts = s.per_prover_counts; \
      pairs = sort(collect(counts), by = x -> -x[2]); \
      total = sum(last.(pairs)); \
      println("Total proofs: ", total, "   provers with data: ", length(pairs)); \
      println("Rank  Prover                     Count    Share"); \
      for (i,(p,c)) in enumerate(pairs); \
          @printf("%3d   %-25s  %7d   %5.2f%%\n", i, p, c, 100c/total); \
      end'

# Generate docs
doc:
    cargo doc --no-deps --open

# Update dependencies
update:
    cargo update

# Regenerate Cap'n Proto bindings from schemas/echidna.capnp.
# Requires capnp compiler: https://capnproto.org/install.html
# Output: src/rust/ipc/echidna_capnp.rs (checked in; do not edit by hand)
capnp-gen:
    @command -v capnp >/dev/null 2>&1 || { echo "capnp compiler not found — install from https://capnproto.org/install.html"; exit 1; }
    capnp compile -orust schemas/echidna.capnp -I /usr/include
    @echo "Rust bindings generated. Commit src/rust/ipc/echidna_capnp.rs."

# Audit dependencies
audit:
    cargo audit
