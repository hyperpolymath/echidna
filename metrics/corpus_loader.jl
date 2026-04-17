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

# TPTP is stored in A2ML/TOML-like blocks, not JSONL. It carries
# Vampire / EProver / SPASS records and must be parsed by a separate
# path in load_corpus.
const TPTP_A2ML = "proof_states_tptp.a2ml"

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
    # Parse TPTP's A2ML block format separately.
    tptp_path = joinpath(training_dir, TPTP_A2ML)
    if isfile(tptp_path)
        for cr in _parse_tptp_a2ml(tptp_path)
            bucket = get!(idx, cr.prover, CorpusRecord[])
            push!(bucket, cr)
        end
    end
    return idx
end

# Minimal A2ML parser for `[[proof-state]] … key = "value"` blocks.
# Each block becomes one CorpusRecord. Unknown keys are ignored.
function _parse_tptp_a2ml(path::AbstractString)::Vector{CorpusRecord}
    out = CorpusRecord[]
    current = Dict{String, Any}()
    in_block = false
    function flush!()
        if in_block && !isempty(current)
            id_raw = get(current, "id", "0")
            id_val = id_raw isa Integer ? Int(id_raw) :
                     something(tryparse(Int, String(id_raw)), 0)
            push!(out, CorpusRecord(
                id_val,
                String(get(current, "prover", "unknown")),
                String(get(current, "theorem", "")),
                String(get(current, "goal", "")),
                String[],
                String(get(current, "proof_steps", "")),
                String(get(current, "source", "TPTP")),
            ))
        end
        empty!(current)
    end
    open(path, "r") do fh
        for line in eachline(fh)
            s = strip(line)
            (isempty(s) || startswith(s, "#")) && continue
            if s == "[[proof-state]]"
                flush!()
                in_block = true
                continue
            end
            if startswith(s, "[") && s != "[[proof-state]]"
                flush!()
                in_block = false
                continue
            end
            in_block || continue
            eq = findfirst('=', s)
            eq === nothing && continue
            k = strip(s[1:prevind(s, eq)])
            v = strip(s[nextind(s, eq):end])
            if startswith(v, "\"") && endswith(v, "\"") && length(v) >= 2
                v = v[nextind(v, firstindex(v)):prevind(v, lastindex(v))]
            end
            current[String(k)] = v
        end
        flush!()
    end
    return out
end

end
