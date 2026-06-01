# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-License-Identifier: MPL-2.0
#
# corpus_loader.jl
#
# Reads `Corpus` JSON files emitted by the Rust corpus adapters added
# in the saturation campaign (2026-06-01). Bridges the 17 adapter output
# paths (agda, coq, lean, idris2, isabelle, metamath, mizar, hol_light,
# hol4, dafny, why3, fstar, acl2_books, tptp, smtlib, proofnet, minif2f)
# into the Julia GNN training pipeline as `TrainingExample`-shaped rows.
#
# This module is intentionally STANDALONE: it does not `using` any of the
# existing training pipeline modules. Consumers wire the output into
# `TrainingDataset` themselves — see `docs/architecture/JULIA-SATURATION-HOOKS.md`
# for the integration topology.

"""
    CorpusLoader

Reads `Corpus` JSON files emitted by Rust corpus adapters (saturation
campaign 2026-06-01). Bridges the 17 adapter output paths into the
Julia GNN training pipeline.

The Rust source of truth is `src/rust/corpus/mod.rs::Corpus`. Schema
fields: `root`, `adapter`, `modules`, `entries`, `by_name`,
`by_qualified`, `dependents`. Each `CorpusEntry` carries `name`,
`qualified`, `module_idx`, `kind`, `statement`, `proof`, `line`,
`dependencies`, `axiom_usage` (a `HazardTags` struct).

See `docs/decisions/2026-06-01-saturation-campaign.md` for the
campaign that produced these adapters and the rationale for this
ingestion shim.
"""
module CorpusLoader

using JSON

export load_corpus_json,
       corpus_to_training_examples,
       corpus_stats,
       merge_corpora,
       corpus_loader_test

# ----------------------------------------------------------------------
# Public API
# ----------------------------------------------------------------------

"""
    load_corpus_json(path::String) -> NamedTuple

Read one Rust `Corpus` JSON file and return it as a NamedTuple with
fields `(:root, :adapter, :modules, :entries, :by_name, :by_qualified,
:dependents, :source_path)`.

Mirrors `src/rust/corpus/mod.rs::Corpus` (serde-derived JSON). The
input file is whatever `Corpus::save_json` wrote — pretty-printed JSON
holding the same field names as the Rust struct.

The two index maps `by_name` and `by_qualified` are passed through
verbatim. Consumers that need fast lookup can rebuild a Julia-side
`Dict{String, Vector{Int}}` from them; we keep them as parsed JSON
objects to avoid pinning a particular Julia type choice on every
caller.

# Arguments
- `path::String`: absolute or relative path to a `<adapter>.json` file
  on disk.

# Returns
A NamedTuple. `:modules` and `:entries` are `Vector{Any}` where each
element is a `Dict{String,Any}` matching the Rust schema field-by-field.

# Errors
Raises `SystemError` if the file cannot be read; raises a
JSON parse error if the file is malformed.
"""
function load_corpus_json(path::String)
    raw = read(path, String)
    obj = JSON.parse(raw)

    return (
        root = get(obj, "root", ""),
        adapter = get(obj, "adapter", "unknown"),
        modules = get(obj, "modules", Any[]),
        entries = get(obj, "entries", Any[]),
        by_name = get(obj, "by_name", Dict{String,Any}()),
        by_qualified = get(obj, "by_qualified", Dict{String,Any}()),
        dependents = get(obj, "dependents", Dict{String,Any}()),
        source_path = path,
    )
end

"""
    corpus_to_training_examples(corpus, prover_kind::Symbol) -> Vector

Translate `CorpusEntry` rows (as loaded by `load_corpus_json`) into the
`TrainingExample` shape consumed by `src/julia/training/dataloader.jl`.

This function does NOT import `dataloader.jl` (avoids a circular
dependency with sibling-branch ownership of the training pipeline). It
returns plain `NamedTuple`s carrying the expected fields; the caller
wires them into `TrainingExample(...)` constructors at the consumption
site.

# Expected downstream shape

`src/julia/training/train.jl::TrainingExample` has fields:
    proof_state::ProofState
    candidate_premises::Vector{Premise}
    relevant_indices::Vector{Int}
    prover::ProverType

`src/julia/EchidnaML.jl::ProofState` has fields:
    prover::ProverType
    goal::String
    context::Vector{String}
    hypotheses::Vector{String}
    available_premises::Vector{String}
    proof_depth::Int
    metadata::Dict{String, Any}

`src/julia/EchidnaML.jl::Premise` has fields:
    name::String
    statement::String
    prover::ProverType
    embedding::Union{Nothing, Vector{Float32}}
    frequency_score::Float32
    relevance_score::Float32

# What we produce

A `Vector{NamedTuple}` where each element has fields:
    (:proof_state_fields, :candidate_premise_field_rows,
     :relevant_indices, :prover_symbol, :adapter, :qualified,
     :hazards)

`:proof_state_fields` is a NamedTuple with `(goal, context,
hypotheses, available_premises, proof_depth, metadata)` ready to be
spread into a `ProofState(prover_kind, …)` call. `:hazards` carries
the Rust `AxiomUsage` flags so callers can drop entries with
`postulate / believe_me / admitted / sorry / trustme`.

Premises are extracted from each entry's `dependencies` field. Each
dependency becomes a candidate premise; `relevant_indices` initially
marks them all relevant (`1..n`), since the Rust adapter only records
premises that the entry actually references.

# Arguments
- `corpus`: a NamedTuple from `load_corpus_json`.
- `prover_kind::Symbol`: the Julia-side prover kind symbol, e.g.
  `:lean`, `:coq`, `:agda`. Caller maps to `ProverType` enum.

# Returns
`Vector{NamedTuple}`. Empty if the corpus has no entries.
"""
function corpus_to_training_examples(corpus, prover_kind::Symbol)
    examples = NamedTuple[]
    entries = corpus.entries
    modules = corpus.modules
    adapter = corpus.adapter

    for entry in entries
        name = get(entry, "name", "")
        qualified = get(entry, "qualified", name)
        kind = get(entry, "kind", "Function")
        statement = get(entry, "statement", "")
        proof = get(entry, "proof", nothing)
        module_idx = get(entry, "module_idx", 0) + 1  # Rust 0-based → Julia 1-based
        deps = String.(get(entry, "dependencies", String[]))
        hazards = get(entry, "axiom_usage", Dict{String,Any}())

        # Module context: imports + module name.
        mod_imports = if 1 <= module_idx <= length(modules)
            String.(get(modules[module_idx], "imports", String[]))
        else
            String[]
        end
        mod_name = if 1 <= module_idx <= length(modules)
            String(get(modules[module_idx], "name", ""))
        else
            ""
        end

        proof_state_fields = (
            goal = statement,
            context = mod_imports,
            hypotheses = String[],
            available_premises = deps,
            proof_depth = 0,
            metadata = Dict{String,Any}(
                "adapter" => adapter,
                "module" => mod_name,
                "kind" => string(kind),
                "line" => get(entry, "line", 0),
                "qualified" => qualified,
            ),
        )

        # One candidate-premise row per dependency. Statement column is
        # left empty here; the consumer can join against
        # `corpus.by_qualified` to resolve full statements before
        # constructing `Premise(...)` values.
        cand_rows = NamedTuple[]
        for dep in deps
            push!(cand_rows, (
                name = dep,
                statement = "",
                frequency_score = 0.0f0,
                relevance_score = 1.0f0,
            ))
        end

        relevant_indices = collect(1:length(cand_rows))

        push!(examples, (
            proof_state_fields = proof_state_fields,
            candidate_premise_field_rows = cand_rows,
            relevant_indices = relevant_indices,
            prover_symbol = prover_kind,
            adapter = adapter,
            qualified = qualified,
            hazards = hazards,
            proof = proof,
        ))
    end

    return examples
end

"""
    corpus_stats(corpus) -> NamedTuple

Summary counts over a loaded corpus. Returns
`(:n_modules, :n_entries, :n_with_hazards, :adapter, :per_kind)`.

`:per_kind` is a `Dict{String, Int}` over the `DeclKind` variants
(Function, Data, Record, Postulate, Module). `:n_with_hazards` counts
entries whose `axiom_usage` has any flag set (postulate, believe_me,
assert_total, admitted, sorry, trustme) OR a non-empty `other` list.

Mirrors `src/rust/corpus/mod.rs::Corpus::stats` but in Julia-native
shape.
"""
function corpus_stats(corpus)
    per_kind = Dict{String,Int}()
    n_hazards = 0

    for entry in corpus.entries
        kind = string(get(entry, "kind", "Function"))
        per_kind[kind] = get(per_kind, kind, 0) + 1
        hz = get(entry, "axiom_usage", Dict{String,Any}())
        if _has_hazard(hz)
            n_hazards += 1
        end
    end

    return (
        n_modules = length(corpus.modules),
        n_entries = length(corpus.entries),
        n_with_hazards = n_hazards,
        adapter = corpus.adapter,
        per_kind = per_kind,
    )
end

"""
    merge_corpora(corpora::Vector{NamedTuple}) -> NamedTuple

Concatenate multiple loaded corpora into a single union. Preserves
`(adapter, qualified)` uniqueness: if two corpora carry the same
`(adapter, qualified)` pair, only the FIRST is retained (caller can
sort the input order to control precedence).

Returns a NamedTuple in the same shape as `load_corpus_json` output,
with:
- `:root` = `""` (no single root anymore)
- `:adapter` = `"merged:<a>,<b>,…"`
- `:modules`, `:entries` re-concatenated with `module_idx` rewritten
  to point at the new combined `modules` vector
- `:by_name`, `:by_qualified`, `:dependents` rebuilt over the combined
  entries

Counterpart to `src/rust/corpus/mod.rs::Corpus::reindex` for the
post-merge bookkeeping.
"""
function merge_corpora(corpora::Vector)
    seen = Set{Tuple{String,String}}()
    out_modules = Any[]
    out_entries = Any[]
    by_name = Dict{String,Vector{Int}}()
    by_qualified = Dict{String,Int}()
    dependents = Dict{String,Vector{Int}}()
    adapters = String[]

    for corpus in corpora
        adapter = corpus.adapter
        push!(adapters, adapter)
        module_offset = length(out_modules)
        # Copy modules; `entries` indices on the module side are
        # rewritten below as we copy entries.
        for m in corpus.modules
            new_m = copy(m)
            new_m["entries"] = Int[]  # rebuilt below
            push!(out_modules, new_m)
        end
        for entry in corpus.entries
            qualified = String(get(entry, "qualified", ""))
            key = (adapter, qualified)
            if key in seen
                continue
            end
            push!(seen, key)
            new_entry = copy(entry)
            new_entry["module_idx"] = get(entry, "module_idx", 0) + module_offset
            push!(out_entries, new_entry)
            new_idx = length(out_entries)  # 1-based

            name = String(get(entry, "name", ""))
            push!(get!(by_name, name, Int[]), new_idx)
            by_qualified[qualified] = new_idx

            # Track which module this entry now belongs to (1-based for
            # Julia consumers; the original 0-based field still lives
            # on the entry itself).
            mi = new_entry["module_idx"] + 1
            if 1 <= mi <= length(out_modules)
                push!(out_modules[mi]["entries"], new_idx - 1)  # keep 0-based on the wire
            end

            for dep in String.(get(entry, "dependencies", String[]))
                push!(get!(dependents, dep, Int[]), new_idx)
            end
        end
    end

    return (
        root = "",
        adapter = "merged:" * join(adapters, ","),
        modules = out_modules,
        entries = out_entries,
        by_name = by_name,
        by_qualified = by_qualified,
        dependents = dependents,
        source_path = "",
    )
end

# ----------------------------------------------------------------------
# Internal helpers
# ----------------------------------------------------------------------

"""
    _has_hazard(axiom_usage) -> Bool

Mirror of `src/rust/corpus/mod.rs::AxiomUsage::any`. Returns `true`
if ANY hazard flag is set OR the free-form `other` list is non-empty.
"""
function _has_hazard(hz)
    if !(hz isa AbstractDict)
        return false
    end
    for k in ("postulate", "believe_me", "assert_total",
              "admitted", "sorry", "trustme")
        if get(hz, k, false) === true
            return true
        end
    end
    other = get(hz, "other", String[])
    return !isempty(other)
end

# ----------------------------------------------------------------------
# Manual smoke test
# ----------------------------------------------------------------------

"""
    corpus_loader_test() -> Bool

Manual smoke test (NOT a runtime test — does not register with any
`@testset` framework). Synthesises a small Corpus JSON string, round-
trips it through `load_corpus_json`, `corpus_to_training_examples`,
`corpus_stats`, and `merge_corpora`, and returns `true` if every
invariant holds.

Run by hand: `julia -e 'include("src/julia/corpus_loader.jl"); using .CorpusLoader; @assert corpus_loader_test()'`.
"""
function corpus_loader_test()
    json_str = """
    {
      "root": "/fake/root",
      "adapter": "test_adapter",
      "modules": [
        {"name": "Foo.Bar", "path": "Foo/Bar.idr",
         "options": [], "imports": ["Prelude"], "entries": [0, 1]}
      ],
      "entries": [
        {"name": "thm1", "qualified": "Foo.Bar.thm1",
         "module_idx": 0, "kind": "Function",
         "statement": "thm1 : Nat -> Nat", "proof": "thm1 n = n",
         "line": 10, "dependencies": ["Nat"],
         "axiom_usage": {"postulate": false, "believe_me": false,
                         "assert_total": false, "admitted": false,
                         "sorry": false, "trustme": false, "other": []}},
        {"name": "thm2", "qualified": "Foo.Bar.thm2",
         "module_idx": 0, "kind": "Postulate",
         "statement": "thm2 : Bool", "proof": null,
         "line": 20, "dependencies": ["thm1"],
         "axiom_usage": {"postulate": true, "believe_me": false,
                         "assert_total": false, "admitted": false,
                         "sorry": false, "trustme": false, "other": []}}
      ],
      "by_name": {"thm1": [0], "thm2": [1]},
      "by_qualified": {"Foo.Bar.thm1": 0, "Foo.Bar.thm2": 1},
      "dependents": {"Nat": [0], "thm1": [1]}
    }
    """

    # Round-trip via a temp file so we exercise the file-read path.
    tmp = tempname() * ".json"
    open(tmp, "w") do io
        write(io, json_str)
    end
    corpus = load_corpus_json(tmp)
    rm(tmp; force=true)

    @assert corpus.adapter == "test_adapter"
    @assert length(corpus.entries) == 2
    @assert length(corpus.modules) == 1

    examples = corpus_to_training_examples(corpus, :idris2)
    @assert length(examples) == 2
    @assert examples[1].adapter == "test_adapter"
    @assert examples[1].prover_symbol === :idris2
    @assert examples[1].proof_state_fields.goal == "thm1 : Nat -> Nat"
    @assert examples[2].hazards["postulate"] === true

    stats = corpus_stats(corpus)
    @assert stats.n_modules == 1
    @assert stats.n_entries == 2
    @assert stats.n_with_hazards == 1
    @assert stats.per_kind["Function"] == 1
    @assert stats.per_kind["Postulate"] == 1

    merged = merge_corpora([corpus, corpus])
    # Dedup on (adapter, qualified) keeps only the first copy.
    @assert length(merged.entries) == 2
    @assert startswith(merged.adapter, "merged:")

    return true
end

end # module CorpusLoader
