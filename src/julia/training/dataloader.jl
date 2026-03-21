# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# training/dataloader.jl
#
# JSONL → TrainingExample data loading pipeline for ECHIDNA.
# Reads proof_states, premises, and tactics JSONL files, joins them by
# proof_id, and produces TrainingExample batches for the Flux training loop.

using JSON3
using Random
using Logging

# ============================================================================
# Raw data records (match JSONL schema)
# ============================================================================

"""Raw proof state from JSONL — fields match the file format."""
struct RawProofState
    id::Int
    prover::String
    theorem::String
    goal::String
    context::Vector{String}
    tactic_proof::String    # full tactic proof (if available)
    source::String          # corpus source
end

"""Raw premise usage from JSONL — which premises were used in a proof."""
struct RawPremise
    proof_id::Int
    premise::String
    prover::String
    theorem::String
    source::String
end

"""Raw tactic step from JSONL — individual tactic applications."""
struct RawTactic
    proof_id::Int
    step::Int
    tactic::String
    prover::String
    tactic_type::String
end

# ============================================================================
# JSONL parsing
# ============================================================================

"""Parse a prover string to ProverType enum, returning nothing for unknown provers."""
function safe_parse_prover(prover_str::String)::Union{ProverType, Nothing}
    prover_map = Dict(
        "lean" => LEAN, "Lean" => LEAN,
        "coq" => COQ, "Coq" => COQ,
        "rocq" => ROCQ, "Rocq" => ROCQ,
        "agda" => AGDA, "Agda" => AGDA,
        "isabelle" => ISABELLE, "Isabelle" => ISABELLE,
        "z3" => Z3, "Z3" => Z3,
        "cvc5" => CVC5, "CVC5" => CVC5,
        "metamath" => METAMATH, "Metamath" => METAMATH,
        "hol_light" => HOL_LIGHT, "HOL Light" => HOL_LIGHT, "HOLLight" => HOL_LIGHT,
        "mizar" => MIZAR, "Mizar" => MIZAR,
        "pvs" => PVS, "PVS" => PVS,
        "acl2" => ACL2, "ACL2" => ACL2,
        "hol4" => HOL4, "HOL4" => HOL4,
        "idris2" => IDRIS2, "Idris2" => IDRIS2,
        "vampire" => VAMPIRE, "Vampire" => VAMPIRE,
        "eprover" => EPROVER, "E" => EPROVER, "EProver" => EPROVER,
        "spass" => SPASS, "SPASS" => SPASS,
        "alt-ergo" => ALT_ERGO, "Alt-Ergo" => ALT_ERGO, "AltErgo" => ALT_ERGO,
        "dafny" => LEAN, "Dafny" => LEAN,  # Dafny mapped to LEAN for now
        "fstar" => LEAN, "F*" => LEAN,     # F* mapped to LEAN for now
        "smtlib" => Z3, "SMT-LIB" => Z3,   # SMT-LIB mapped to Z3
    )
    return get(prover_map, prover_str, nothing)
end

"""
    load_jsonl_proof_states(path::String; max_records::Int=0)

Load proof states from a JSONL file. Set max_records=0 for unlimited.
"""
function load_jsonl_proof_states(path::String; max_records::Int=0)
    records = RawProofState[]
    isfile(path) || return records

    open(path, "r") do io
        for line in eachline(io)
            isempty(strip(line)) && continue
            try
                obj = JSON3.read(line)
                push!(records, RawProofState(
                    get(obj, :id, 0),
                    get(obj, :prover, ""),
                    get(obj, :theorem, ""),
                    get(obj, :goal, ""),
                    String.(get(obj, :context, String[])),
                    string(get(obj, :tactic_proof, "")),
                    string(get(obj, :source, ""))
                ))
            catch e
                # Skip malformed lines
                continue
            end
            max_records > 0 && length(records) >= max_records && break
        end
    end

    @info "Loaded $(length(records)) proof states from $path"
    return records
end

"""
    load_jsonl_premises(path::String; max_records::Int=0)

Load premise usage records from a JSONL file.
"""
function load_jsonl_premises(path::String; max_records::Int=0)
    records = RawPremise[]
    isfile(path) || return records

    open(path, "r") do io
        for line in eachline(io)
            isempty(strip(line)) && continue
            try
                obj = JSON3.read(line)
                push!(records, RawPremise(
                    get(obj, :proof_id, 0),
                    get(obj, :premise, ""),
                    get(obj, :prover, ""),
                    get(obj, :theorem, ""),
                    string(get(obj, :source, ""))
                ))
            catch
                continue
            end
            max_records > 0 && length(records) >= max_records && break
        end
    end

    @info "Loaded $(length(records)) premise records from $path"
    return records
end

"""
    load_jsonl_tactics(path::String; max_records::Int=0)

Load tactic step records from a JSONL file.
"""
function load_jsonl_tactics(path::String; max_records::Int=0)
    records = RawTactic[]
    isfile(path) || return records

    open(path, "r") do io
        for line in eachline(io)
            isempty(strip(line)) && continue
            try
                obj = JSON3.read(line)
                push!(records, RawTactic(
                    get(obj, :proof_id, 0),
                    get(obj, :step, 1),
                    get(obj, :tactic, ""),
                    get(obj, :prover, ""),
                    string(get(obj, :tactic_type, ""))
                ))
            catch
                continue
            end
            max_records > 0 && length(records) >= max_records && break
        end
    end

    @info "Loaded $(length(records)) tactic records from $path"
    return records
end

# ============================================================================
# Join records into TrainingExamples
# ============================================================================

"""
    build_premise_index(premises::Vector{RawPremise})

Group premises by proof_id for fast lookup.
Returns Dict{Int, Vector{String}} mapping proof_id → premise names.
"""
function build_premise_index(premises::Vector{RawPremise})
    index = Dict{Int, Vector{String}}()
    for p in premises
        if !haskey(index, p.proof_id)
            index[p.proof_id] = String[]
        end
        push!(index[p.proof_id], p.premise)
    end
    return index
end

"""
    build_training_examples(proof_states::Vector{RawProofState},
                            premise_index::Dict{Int, Vector{String}};
                            all_premises_pool::Vector{String}=String[],
                            num_negatives::Int=20)

Convert raw records into TrainingExamples by joining proof states with
their used premises, and sampling negative (unused) premises.

Arguments:
- proof_states: loaded proof state records
- premise_index: proof_id → used premise names
- all_premises_pool: global pool of all known premise names (for negatives)
- num_negatives: number of negative premises to sample per example
"""
function build_training_examples(proof_states::Vector{RawProofState},
                                  premise_index::Dict{Int, Vector{String}};
                                  all_premises_pool::Vector{String}=String[],
                                  num_negatives::Int=20)
    examples = TrainingExample[]

    # If no global pool provided, collect all unique premises
    if isempty(all_premises_pool)
        all_premises_pool = unique(vcat(values(premise_index)...))
    end

    premises_set = Set(all_premises_pool)

    for ps in proof_states
        prover = safe_parse_prover(ps.prover)
        prover === nothing && continue

        # Get premises actually used in this proof
        used_names = get(premise_index, ps.id, String[])
        isempty(used_names) && continue

        # Build candidate premise list: positives + sampled negatives
        positive_premises = Premise[]
        for name in used_names
            push!(positive_premises, Premise(name, "", prover, nothing, 1.0f0, 1.0f0))
        end

        # Sample negative premises (not used in this proof)
        negative_names = setdiff(all_premises_pool, used_names)
        num_neg = min(num_negatives, length(negative_names))
        sampled_negatives = num_neg > 0 ? sample(collect(negative_names), num_neg; replace=false) : String[]

        negative_premises = Premise[]
        for name in sampled_negatives
            push!(negative_premises, Premise(name, "", prover, nothing, 0.0f0, 0.0f0))
        end

        # Combine: positives first, then negatives
        all_candidates = vcat(positive_premises, negative_premises)
        relevant_indices = collect(1:length(positive_premises))

        # Shuffle candidates (but track which are relevant)
        perm = randperm(length(all_candidates))
        all_candidates = all_candidates[perm]
        # Update relevant_indices to match new positions
        inv_perm = invperm(perm)
        relevant_indices = [inv_perm[i] for i in relevant_indices]

        # Build proof state
        proof_state = ProofState(
            prover,
            ps.goal,
            ps.context,
            String[],                # hypotheses (extracted from context if available)
            [c.name for c in all_candidates],
            0,
            Dict{String, Any}("theorem" => ps.theorem, "source" => ps.source)
        )

        push!(examples, TrainingExample(proof_state, all_candidates, relevant_indices, prover))
    end

    @info "Built $(length(examples)) training examples from $(length(proof_states)) proof states"
    return examples
end

# ============================================================================
# Build vocabulary from training data
# ============================================================================

"""
    build_vocabulary_from_data(proof_states::Vector{RawProofState};
                               min_freq::Int=2, max_vocab::Int=50000)

Build a ProverVocabulary from proof state goals and contexts.
"""
function build_vocabulary_from_data(proof_states::Vector{RawProofState};
                                    min_freq::Int=2, max_vocab::Int=50000)
    # Collect all text
    corpus = String[]
    for ps in proof_states
        push!(corpus, ps.goal)
        append!(corpus, ps.context)
    end

    return create_vocabulary(corpus; min_freq=min_freq, max_vocab=max_vocab)
end

# ============================================================================
# Main data loading entry point
# ============================================================================

"""
    load_training_data(data_dir::String; train_split::Float32=0.8f0,
                       max_proof_states::Int=0, num_negatives::Int=20)

Load JSONL training data, join records, split into train/val datasets.

Looks for these files in data_dir:
- proof_states_UNIFIED.jsonl (or proof_states.jsonl as fallback)
- premises.jsonl (or premises_COMPLETE.jsonl)
- tactics.jsonl (or tactics_COMPLETE.jsonl)

Returns (train_data::TrainingDataset, val_data::TrainingDataset, vocab::ProverVocabulary)
"""
function load_training_data(data_dir::String; train_split::Float32=0.8f0,
                            max_proof_states::Int=0, num_negatives::Int=20)
    @info "Loading training data from $data_dir"

    # Find best available files
    ps_file = if isfile(joinpath(data_dir, "proof_states_UNIFIED.jsonl"))
        joinpath(data_dir, "proof_states_UNIFIED.jsonl")
    elseif isfile(joinpath(data_dir, "proof_states_COMPLETE.jsonl"))
        joinpath(data_dir, "proof_states_COMPLETE.jsonl")
    else
        joinpath(data_dir, "proof_states.jsonl")
    end

    prem_file = if isfile(joinpath(data_dir, "premises_COMPLETE.jsonl"))
        joinpath(data_dir, "premises_COMPLETE.jsonl")
    else
        joinpath(data_dir, "premises.jsonl")
    end

    @info "Using proof states: $ps_file"
    @info "Using premises: $prem_file"

    # Load raw records
    proof_states = load_jsonl_proof_states(ps_file; max_records=max_proof_states)
    premises = load_jsonl_premises(prem_file)

    if isempty(proof_states)
        @warn "No proof states loaded — returning empty datasets"
        vocab = create_vocabulary(String[])
        return TrainingDataset(TrainingExample[]), TrainingDataset(TrainingExample[]), vocab
    end

    # Build vocabulary from proof state goals
    @info "Building vocabulary..."
    vocab = build_vocabulary_from_data(proof_states)
    @info "Vocabulary size: $(vocab.vocab_size)"

    # Join premises with proof states
    premise_index = build_premise_index(premises)
    all_premise_names = unique([p.premise for p in premises])
    @info "Unique premises: $(length(all_premise_names))"

    # Build training examples
    examples = build_training_examples(proof_states, premise_index;
                                        all_premises_pool=all_premise_names,
                                        num_negatives=num_negatives)

    if isempty(examples)
        @warn "No valid training examples built"
        return TrainingDataset(TrainingExample[]), TrainingDataset(TrainingExample[]), vocab
    end

    # Shuffle and split
    shuffle!(examples)
    split_idx = round(Int, length(examples) * train_split)

    train_examples = examples[1:split_idx]
    val_examples = examples[split_idx+1:end]

    train_data = TrainingDataset(train_examples, batch_size=get_config().batch_size, shuffle=true)
    val_data = TrainingDataset(val_examples, batch_size=get_config().batch_size, shuffle=false)

    @info "Training set: $(length(train_examples)) examples"
    @info "Validation set: $(length(val_examples)) examples"
    @info "Data loading complete"

    return train_data, val_data, vocab
end

export load_jsonl_proof_states, load_jsonl_premises, load_jsonl_tactics
export build_premise_index, build_training_examples
export build_vocabulary_from_data, load_training_data
