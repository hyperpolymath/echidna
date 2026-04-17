# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# corpus_loader.jl — Single authoritative pass over per-prover JSONL.
#
# All metrics share one in-memory index keyed by prover → Vector{Record}.
# This avoids N× re-reading the 286K-proof corpus across eight metrics.

module CorpusLoader

using JSON3

export load_corpus, CorpusRecord, CorpusIndex, PER_PROVER_FILES

# Same list merge_corpus.jl consumes. Intentionally excludes aggregates.
const PER_PROVER_FILES = [
    "proof_states_mathlib4_max.jsonl",
    "proof_states_coqgym_max.jsonl",
    "proof_states_smtlib.jsonl",
    "proof_states_metamath.jsonl",
    "proof_states_hol_light.jsonl",
    "proof_states_hol4.jsonl",
    "proof_states_acl2.jsonl",
    "proof_states_pvs.jsonl",
    "proof_states_why3.jsonl",
    "proof_states_dafny.jsonl",
    "proof_states_fstar.jsonl",
    "proof_states_idris2.jsonl",
    "proof_states_mizar.jsonl",
    "proof_states_nuprl.jsonl",
    "proof_states_minlog.jsonl",
    "proof_states_twelf.jsonl",
    "proof_states_imandra.jsonl",
    "proof_states_minizinc.jsonl",
    "proof_states_afp.jsonl",
    "proof_states_agda.jsonl",
    "proof_states_typechecker_ecosystem.jsonl",
]

struct CorpusRecord
    id::Int
    prover::String
    theorem::String
    goal::String
    context::Vector{String}
    tactic_proof::String
    source::String
end

const CorpusIndex = Dict{String, Vector{CorpusRecord}}

function _string_vec(v)::Vector{String}
    v isa AbstractVector || return String[]
    out = String[]
    for x in v
        x isa AbstractString && push!(out, String(x))
    end
    return out
end

function _coerce(rec::AbstractDict)::CorpusRecord
    CorpusRecord(
        Int(get(rec, "id", 0)),
        String(get(rec, "prover", "unknown")),
        String(get(rec, "theorem", "")),
        String(get(rec, "goal", "")),
        _string_vec(get(rec, "context", String[])),
        String(get(rec, "tactic_proof", "")),
        String(get(rec, "source", "")),
    )
end

"""
    load_corpus(training_dir) -> CorpusIndex

Read every authoritative per-prover JSONL under `training_dir`.
Returns a dict mapping prover name → records. Missing files are skipped.
"""
function load_corpus(training_dir::AbstractString)::CorpusIndex
    idx = CorpusIndex()
    for fname in PER_PROVER_FILES
        path = joinpath(training_dir, fname)
        isfile(path) || continue
        open(path, "r") do fh
            for line in eachline(fh)
                s = strip(line)
                isempty(s) && continue
                try
                    rec = JSON3.read(s, Dict{String,Any})
                    cr = _coerce(rec)
                    bucket = get!(idx, cr.prover, CorpusRecord[])
                    push!(bucket, cr)
                catch
                end
            end
        end
    end
    return idx
end

end
