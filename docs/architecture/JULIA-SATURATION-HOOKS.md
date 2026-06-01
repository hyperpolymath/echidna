<!--
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
SPDX-License-Identifier: MPL-2.0
-->

# Julia Saturation Hooks — Rust corpus adapters → Julia GNN pipeline

**Status**: canonical for the hand-off topology produced by the
2026-06-01 saturation campaign on branch `prover-corpus-saturation`.
Wire-in PR (the ~50-LoC additions to `run_training.jl`) lands AFTER
both this branch and the parallel
`wave3/161-162-bench-telemetry-corpus` branch merge.
**Date**: 2026-06-01.
**Companion ADR**:
`docs/decisions/2026-06-01-saturation-campaign.md`.

## 1. Integration topology

```
Rust corpus adapter            (src/rust/corpus/<adapter>.rs)
  → Corpus JSON                (via Corpus::save_json)
    → CorpusLoader.load_corpus_json          [Julia, NEW this campaign]
      → corpus_to_training_examples
        → TrainingDataset                    [Julia, existing — wave3-owned]
          → train_solver!                    [Julia, existing — wave3-owned]
            → models/neural/                 [Julia, existing — wave3-owned]
```

The whole left half (Rust → Corpus JSON → Julia loader) is new in this
campaign. The whole right half (TrainingDataset → train_solver! →
models/neural) is pre-existing AND under sibling-branch ownership. The
join point — the `Vector{NamedTuple}` returned by
`corpus_to_training_examples` — is the hand-off contract documented in
§4.

## 2. Julia files ADDED in this campaign

All under `src/julia/`:

| File | Role |
|------|------|
| `corpus_loader.jl` | New `CorpusLoader` module — reads `Corpus` JSON and produces `TrainingExample`-shaped NamedTuples. |
| `saturation_synonyms.jl` | New `SaturationSynonyms` module — reads per-prover synonym TOMLs and the three cross-prover dictionaries (`_msc2020`, `_wordnet_math`, `_conceptnet_seed`). |
| `README.md` (addendum section only) | Documents the two new modules and the deliberate hand-off boundary. Existing content untouched. |

These three are **the entirety of the Julia surface area** added by
the campaign. No edits to any pre-existing Julia file.

## 3. Julia files DELIBERATELY NOT TOUCHED

The following are wave3-owned and/or sit downstream of the GNN training
trigger; they remain untouched on this branch:

| File | Owner | Why not touched |
|------|-------|-----------------|
| `src/julia/run_training.jl` | wave3 chapel bench + telemetry session | Bench harness modifications in flight. Wiring the new loader in is the follow-up PR (§5). |
| `src/julia/training/train.jl` | wave3 / GNN-trigger | Holds `TrainingExample` / `TrainingDataset` / `train_solver!`. Schema is the hand-off target, not the target of edits. |
| `src/julia/training/dataloader.jl` | wave3 / GNN-trigger | Holds the existing JSONL `proof_states / premises / tactics` pipeline. New corpus adapters are additive; they don't replace it. |
| `src/julia/models/neural_solver.jl` | wave3 / GNN-trigger | Encoder + GNN architecture. Downstream of `TrainingDataset`. |
| `src/julia/models/encoder.jl` | wave3 / GNN-trigger | Same. |
| `src/julia/run_training_cpu.jl` | wave3 chapel bench session | CPU baseline runner. Touching it would collide with bench numbers. |

The saturation campaign ADR §"Coordination with wave3/161-162"
enumerates the same hard-exclusion set on the Rust + data side; this
table is the Julia mirror.

## 4. Hand-off contract: field-name and arity guarantees

`CorpusLoader.corpus_to_training_examples(corpus, prover_kind::Symbol)`
returns `Vector{NamedTuple}`. Each element has fields:

| Field | Type | Meaning |
|-------|------|---------|
| `proof_state_fields` | `NamedTuple` | `(goal, context, hypotheses, available_premises, proof_depth, metadata)` — ready to be spread into a `ProofState(prover, …)` call. |
| `candidate_premise_field_rows` | `Vector{NamedTuple}` | Each row: `(name, statement, frequency_score, relevance_score)`. Caller wraps in `Premise(name, statement, prover, nothing, freq, rel)`. |
| `relevant_indices` | `Vector{Int}` | 1-based indices into `candidate_premise_field_rows`. Initially `1:n` (every recorded dependency is by definition relevant). |
| `prover_symbol` | `Symbol` | Passed-through from the caller; maps to `ProverType` via the existing `safe_parse_prover` table in `dataloader.jl`. |
| `adapter` | `String` | Source adapter (`"lean"`, `"coq"`, `"mizar"`, …). Useful as a metadata tag. |
| `qualified` | `String` | Fully-qualified entry name (`"Foo.Bar.thm1"`). |
| `hazards` | `Dict{String, Any}` | The Rust `AxiomUsage` flags. Consumers DROP entries where any of `postulate / believe_me / assert_total / admitted / sorry / trustme` is `true` (matches Rust SA design-search reject filter). |
| `proof` | `Union{String, Nothing}` | The defining-equation body, if present. `Nothing` for postulates and data declarations. |

### Mapping to existing Julia types

The training-side targets (defined in `src/julia/EchidnaML.jl` +
`src/julia/training/train.jl`) are unchanged:

- `ProofState(prover::ProverType, goal::String, context::Vector{String}, hypotheses::Vector{String}, available_premises::Vector{String}, proof_depth::Int, metadata::Dict{String, Any})`
- `Premise(name::String, statement::String, prover::ProverType, embedding::Union{Nothing, Vector{Float32}}, frequency_score::Float32, relevance_score::Float32)`
- `TrainingExample(proof_state::ProofState, candidate_premises::Vector{Premise}, relevant_indices::Vector{Int}, prover::ProverType)`

The wiring shim is purely a constructor adapter. No type changes are
required on the wave3 side.

### Cross-references inside the corpus

`corpus.by_qualified` and `corpus.by_name` are passed through verbatim
from the JSON; consumers that want to fill in the empty `statement`
column on `candidate_premise_field_rows` can join against
`corpus.by_qualified[dep_qualified]` → `corpus.entries[idx].statement`.

## 5. Follow-up wiring PR (after wave3 lands)

Single PR, scope ≈ 50 LoC. Sketch:

```julia
# In src/julia/run_training.jl, near the existing dataloader call:
include("corpus_loader.jl"); using .CorpusLoader

function load_corpus_examples(corpus_paths::Vector{String},
                              prover_kind::Symbol)
    corpora = [CorpusLoader.load_corpus_json(p) for p in corpus_paths]
    merged = CorpusLoader.merge_corpora(corpora)
    rows = CorpusLoader.corpus_to_training_examples(merged, prover_kind)
    examples = TrainingExample[]
    for row in rows
        # Skip axiom-class hazards.
        any(values(row.hazards)) && continue

        prover = safe_parse_prover(string(prover_kind))
        prover === nothing && continue

        ps = ProofState(prover,
                        row.proof_state_fields.goal,
                        row.proof_state_fields.context,
                        row.proof_state_fields.hypotheses,
                        row.proof_state_fields.available_premises,
                        row.proof_state_fields.proof_depth,
                        row.proof_state_fields.metadata)
        premises = [Premise(p.name, p.statement, prover, nothing,
                            p.frequency_score, p.relevance_score)
                    for p in row.candidate_premise_field_rows]
        push!(examples, TrainingExample(ps, premises,
                                        row.relevant_indices, prover))
    end
    return examples
end
```

The PR also adds a `--corpus-json` CLI flag to `run_training.jl` that
threads the corpus paths through `load_corpus_examples` and unions the
result with whatever `load_jsonl_proof_states` already returns.

Hazard policy: drop entries with ANY axiom flag set. Matches the
Rust SA design-search reject convention documented at
`src/rust/corpus/mod.rs::AxiomUsage`.

## 6. Cross-references

- ADR: `docs/decisions/2026-06-01-saturation-campaign.md`
- Corpus adapter index: `docs/CORPUS-ADAPTERS.md`
- E-R schema for the verisim store these training examples eventually
  feed: `docs/architecture/VERISIM-ER-SCHEMA.md`
- Handover scoping document:
  `docs/handover/PROVER-CORPUS-SATURATION-LANE.md`
- Rust corpus root: `src/rust/corpus/mod.rs`
- Rust synonyms root: `src/rust/suggest/synonyms.rs`
- Julia module addendum: `src/julia/README.md` §"Saturation-campaign
  addendum (2026-06-01)"
