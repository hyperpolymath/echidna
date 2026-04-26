# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
# SPDX-License-Identifier: PMPL-1.0-or-later

"""
Training Data Extraction for ECHIDNA v1.3

Extracts training data from proof examples for neural model training:
- Proof states (goals + context)
- Tactic sequences
- Premise usage patterns
"""

using Dates

# Output directory for training data
const TRAINING_DATA_DIR = "training_data"

# Proof file patterns by prover
const PROOF_PATTERNS = Dict(
    "Lean" => r"theorem|lemma|def|example",
    "Coq" => r"Theorem|Lemma|Definition|Example",
    "Agda" => r"[A-Za-z][A-Za-z0-9]*\s*:\s*",
    "Isabelle" => r"theorem|lemma|definition",
    "Z3" => r"\(assert|\(check-sat",
    "CVC5" => r"\(assert|\(check-sat",
    "Metamath" => r"\$p",
    "HOLLight" => r"let.*=.*prove",
    "Mizar" => r"theorem|definition",
    "ACL2" => r"\(defthm|\(defun",
    "PVS" => r"LEMMA|THEOREM",
    "HOL4" => r"val.*=.*prove|store_thm"
)

# Tactic patterns by prover
const TACTIC_PATTERNS = Dict(
    "Lean" => r"(intro|apply|rw|simp|exact|refine|induction|cases|split|trivial|assumption)",
    "Coq" => r"(intros?|apply|rewrite|simpl|reflexivity|exact|refine|induction|destruct|split|trivial|assumption)",
    "Agda" => r"(refl|cong|trans|sym|subst)",
    "Isabelle" => r"(by\s+\w+|using|apply|simp|auto|blast|fast|force)",
    "Z3" => r"(assert|check-sat|get-model|push|pop)",
    "ACL2" => r"(induct|expand|generalize|:use|:in-theory)",
    "PVS" => r"(grind|assert|skolem|inst|lemma|rewrite)",
    "HOL4" => r"(_TAC|REWRITE_TAC|ASM_REWRITE_TAC|INDUCT_TAC|Cases_on|Induct)"
)

struct ProofExample
    prover::String
    file::String
    theorem_name::String
    goal::String
    tactics::Vector{String}
    premises::Vector{String}
    success::Bool
end

"""
    extract_from_file(prover::String, filepath::String) -> Vector{ProofExample}

Extract proof examples from a single file.
"""
function extract_from_file(prover::String, filepath::String)::Vector{ProofExample}
    examples = ProofExample[]

    content = try
        read(filepath, String)
    catch e
        @warn "Could not read file: $filepath" exception=e
        return examples
    end

    # Different extraction strategies per prover
    if prover == "Lean"
        examples = extract_lean_proofs(filepath, content)
    elseif prover == "Coq"
        examples = extract_coq_proofs(filepath, content)
    elseif prover == "ACL2"
        examples = extract_acl2_proofs(filepath, content)
    elseif prover == "PVS"
        examples = extract_pvs_proofs(filepath, content)
    elseif prover == "HOL4"
        examples = extract_hol4_proofs(filepath, content)
    elseif prover == "Isabelle"
        examples = extract_isabelle_proofs(filepath, content)
    elseif prover == "Agda"
        examples = extract_agda_proofs(filepath, content)
    elseif prover == "Idris2"
        examples = extract_idris2_proofs(filepath, content)
    elseif prover == "Mizar"
        examples = extract_mizar_proofs(filepath, content)
    elseif prover == "TLAPS"
        examples = extract_tlaps_proofs(filepath, content)
    elseif prover == "Why3"
        examples = extract_why3_proofs(filepath, content)
    elseif prover == "F*"
        examples = extract_fstar_proofs(filepath, content)
    else
        # Generic extraction for other provers
        examples = extract_generic_proofs(prover, filepath, content)
    end

    return examples
end

"""
Extract Lean proofs (most detailed tactic information)
"""
function extract_lean_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Match theorem/lemma declarations
    for m in eachmatch(r"(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_]*)\s*([^:]*):([^:=]+):=\s*by\s*([^\n]+)"s, content)
        theorem_name = m.captures[2]
        goal = strip(m.captures[4])
        tactic_block = m.captures[5]

        # Extract individual tactics
        tactics = [strip(t) for t in split(tactic_block, r"<;>|;|\n") if !isempty(strip(t))]

        # Extract premise usage (apply, rw with theorem names)
        premises = String[]
        for tactic in tactics
            if occursin(r"apply|rw", tactic)
                premise_match = match(r"(apply|rw)\s+([A-Za-z_][A-Za-z0-9_\.]*)", tactic)
                if premise_match !== nothing
                    push!(premises, premise_match.captures[2])
                end
            end
        end

        push!(examples, ProofExample(
            "Lean",
            filepath,
            theorem_name,
            goal,
            tactics,
            unique(premises),
            true
        ))
    end

    return examples
end

"""
Extract Coq proofs
"""
function extract_coq_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Match Theorem...Qed blocks
    for m in eachmatch(r"(Theorem|Lemma)\s+([A-Za-z_][A-Za-z0-9_]*)\s*:([^.]+)\.\s*Proof\.(.*?)Qed\."s, content)
        theorem_name = m.captures[2]
        goal = strip(m.captures[3])
        proof_script = m.captures[4]

        # Extract tactics
        tactics = [strip(t) for t in split(proof_script, '.') if !isempty(strip(t)) && !occursin(r"^\s*$", t)]

        # Extract premises
        premises = String[]
        for tactic in tactics
            for premise_match in eachmatch(r"(apply|rewrite|exact)\s+([A-Za-z_][A-Za-z0-9_]*)", tactic)
                push!(premises, premise_match.captures[2])
            end
        end

        push!(examples, ProofExample(
            "Coq",
            filepath,
            theorem_name,
            goal,
            tactics,
            unique(premises),
            true
        ))
    end

    return examples
end

"""
Extract ACL2 proofs (defthm with hints)
"""
function extract_acl2_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Match (defthm name formula ...)
    for m in eachmatch(r"\(defthm\s+([A-Za-z_][A-Za-z0-9_-]*)\s+(.*?)(?:\)|:hints)"s, content)
        theorem_name = m.captures[1]
        formula = strip(m.captures[2])

        # Extract hints (tactics in ACL2)
        hints = String[]
        hint_block = match(r":hints\s*\((.*?)\)"s, content[m.offset:end])
        if hint_block !== nothing
            push!(hints, strip(hint_block.captures[1]))
        end

        # Extract premises from :use, :in-theory, :enable, :disable clauses
        premises = String[]
        try
            # Pattern: :use (:instance theorem-name ...) or :use theorem-name
            for use_match in eachmatch(r":use\s*\(?:?instance\s+([a-z][a-z0-9\-]*)", hint_block !== nothing ? hint_block.captures[1] : "")
                push!(premises, use_match.captures[1])
            end
            # Pattern: :enable theorem-name or :in-theory (enable theorem-name)
            for enable_match in eachmatch(r":(?:in-theory\s*\(|enable\s+)([a-z][a-z0-9\-]*)", hint_block !== nothing ? hint_block.captures[1] : "")
                push!(premises, enable_match.captures[1])
            end
        catch
            # If regex fails, leave premises empty
        end

        push!(examples, ProofExample(
            "ACL2",
            filepath,
            theorem_name,
            formula,
            hints,
            unique(premises),
            true
        ))
    end

    return examples
end

"""
Extract PVS proofs
"""
function extract_pvs_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Match LEMMA/THEOREM
    for m in eachmatch(r"(LEMMA|THEOREM)\s+([A-Za-z_][A-Za-z0-9_]*)\s*:(.*?)(?:PROOF|END)"s, content)
        theorem_name = m.captures[2]
        formula = strip(m.captures[3])

        # PVS tactics are complex - extract strategy names
        tactics = String["grind"]  # Default PVS strategy

        push!(examples, ProofExample(
            "PVS",
            filepath,
            theorem_name,
            formula,
            tactics,
            String[],
            true
        ))
    end

    return examples
end

"""
Extract Isabelle/HOL proofs
"""
function extract_isabelle_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Match theorem/lemma declarations with proof blocks
    for m in eachmatch(r"(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_\"]*)\s*:([^=]+)=\s*(.+?)(?:\n(?:theorem|lemma|end|definition)|\Z)"s, content)
        theorem_name = m.captures[2]
        goal = strip(m.captures[3])
        proof_block = m.captures[4]

        # Extract tactics from proof
        tactics = [strip(t) for t in split(proof_block, r"<;>|;|\n") if !isempty(strip(t))]

        # Extract premises: using, metis, apply (rule), apply (erule), apply (drule), apply (frule)
        premises = String[]
        try
            for tactic in tactics
                # Pattern: using theorem_name or metis theorem_name1 theorem_name2
                for premise_match in eachmatch(r"(?:using|metis|rule|erule|drule|frule)\s+([A-Za-z_][A-Za-z0-9_\.]*)", tactic)
                    push!(premises, premise_match.captures[1])
                end
                # Pattern: apply (rule theorem_name) or by (metis theorem_name)
                if occursin(r"apply\s*\((?:rule|erule|drule|frule)", tactic)
                    for rule_match in eachmatch(r"apply\s*\((?:rule|erule|drule|frule)\s+([A-Za-z_][A-Za-z0-9_\.]*)", tactic)
                        push!(premises, rule_match.captures[1])
                    end
                end
            end
        catch
            # If regex fails, continue with empty premises
        end

        push!(examples, ProofExample(
            "Isabelle",
            filepath,
            theorem_name,
            goal,
            tactics,
            unique(premises),
            true
        ))
    end

    return examples
end

"""
Extract Agda proofs (qualified names and definition references)
"""
function extract_agda_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Match function/theorem declarations with where clauses
    for m in eachmatch(r"([A-Za-z_][A-Za-z0-9_]*)\s*:\s*([^\s=]+(?:\s*→[^\s=]+)*)\s*(?:where|=)"s, content)
        theorem_name = m.captures[1]
        goal = strip(m.captures[2])

        # Extract qualified names (e.g., Relation.Binary.PropositionalEquality.refl)
        premises = String[]
        try
            for qual_match in eachmatch(r"([A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)+)", content[m.offset:min(m.offset+500, end)])
                push!(premises, qual_match.captures[1])
            end
        catch
            # Continue with empty premises
        end

        tactics = String["where"]  # Agda uses where clauses

        push!(examples, ProofExample(
            "Agda",
            filepath,
            theorem_name,
            goal,
            tactics,
            unique(premises),
            true
        ))
    end

    return examples
end

"""
Extract Idris2 proofs (similar to Lean: exact, apply, with patterns)
"""
function extract_idris2_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Match theorem/lemma declarations
    for m in eachmatch(r"(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_]*)\s*:([^:=]+):=\s*by\s*(.+?)(?:\n\n|\n(?:theorem|lemma)|\Z)"s, content)
        theorem_name = m.captures[2]
        goal = strip(m.captures[3])
        proof_block = m.captures[4]

        # Extract tactics
        tactics = [strip(t) for t in split(proof_block, r"<;>|;|\n") if !isempty(strip(t))]

        # Extract premises: exact theorem_name, apply theorem_name, with theorem_name
        premises = String[]
        try
            for tactic in tactics
                for premise_match in eachmatch(r"(?:exact|apply|with)\s+([A-Za-z_][A-Za-z0-9_\.]*)", tactic)
                    push!(premises, premise_match.captures[1])
                end
            end
        catch
            # Continue with empty premises
        end

        push!(examples, ProofExample(
            "Idris2",
            filepath,
            theorem_name,
            goal,
            tactics,
            unique(premises),
            true
        ))
    end

    return examples
end

"""
Extract Mizar proofs (THEOREM references with justifications)
"""
function extract_mizar_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Match theorem/definition declarations
    for m in eachmatch(r"(theorem|definition)\s+([A-Z_][A-Z0-9_]*)\s*:([^;]+);"s, content)
        theorem_name = m.captures[2]
        goal = strip(m.captures[3])

        # Extract premises from "by THEOREM_NAME:1" and "from SCHEME_NAME(...)" patterns
        premises = String[]
        try
            for by_match in eachmatch(r"by\s+([A-Z_][A-Z0-9_]*(?::[0-9]+)?)", goal)
                push!(premises, by_match.captures[1])
            end
            for from_match in eachmatch(r"from\s+([A-Z_][A-Z0-9_]*)", goal)
                push!(premises, from_match.captures[1])
            end
        catch
            # Continue with empty premises
        end

        push!(examples, ProofExample(
            "Mizar",
            filepath,
            theorem_name,
            goal,
            String["by"],  # Mizar proofs use "by" justifications
            unique(premises),
            true
        ))
    end

    return examples
end

"""
Extract TLAPS (TLA+) proofs
"""
function extract_tlaps_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Match theorem declarations
    for m in eachmatch(r"(THEOREM|LEMMA)\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?:==|<=>)\s*(.+?)(?:\n(?:THEOREM|LEMMA|PROOF)|\Z)"s, content)
        theorem_name = m.captures[2]
        goal = strip(m.captures[3])

        # Extract premises from <1>1 BY DEF theorem_name and PROVE ... BY theorem_name
        premises = String[]
        try
            for by_match in eachmatch(r"BY(?:\s+DEF)?\s+([A-Za-z_][A-Za-z0-9_]*)", goal)
                push!(premises, by_match.captures[1])
            end
            for prove_match in eachmatch(r"PROVE\s+[^B]*BY\s+([A-Za-z_][A-Za-z0-9_]*)", goal)
                push!(premises, prove_match.captures[1])
            end
        catch
            # Continue with empty premises
        end

        push!(examples, ProofExample(
            "TLAPS",
            filepath,
            theorem_name,
            goal,
            String["BY"],
            unique(premises),
            true
        ))
    end

    return examples
end

"""
Extract Why3 proofs (use/import and by clauses)
"""
function extract_why3_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Match lemma/theorem declarations
    for m in eachmatch(r"(lemma|theorem)\s+([a-z_][a-z0-9_]*)\s*:(.+?)(?:proof|by|end)"is, content)
        theorem_name = m.captures[2]
        goal = strip(m.captures[3])

        # Extract premises from "use import module_name" and "by <term>"
        premises = String[]
        try
            for use_match in eachmatch(r"use\s+(?:import\s+)?([A-Za-z_][A-Za-z0-9_\.]*)", goal)
                push!(premises, use_match.captures[1])
            end
        catch
            # Continue with empty premises
        end

        push!(examples, ProofExample(
            "Why3",
            filepath,
            theorem_name,
            goal,
            String["by"],
            unique(premises),
            true
        ))
    end

    return examples
end

"""
Extract F* proofs (by and using clauses with lemma names)
"""
function extract_fstar_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Match val/lemma declarations
    for m in eachmatch(r"(?:val|lemma)\s+([a-z_][a-z0-9_]*)\s*:(.+?)(?:=|by)"is, content)
        theorem_name = m.captures[1]
        goal = strip(m.captures[2])

        # Extract premises from "by lemma_name" and "using lemma_name"
        premises = String[]
        try
            for premise_match in eachmatch(r"(?:by|using)\s+([A-Za-z_][A-Za-z0-9_\.]*)", goal)
                push!(premises, premise_match.captures[1])
            end
        catch
            # Continue with empty premises
        end

        push!(examples, ProofExample(
            "F*",
            filepath,
            theorem_name,
            goal,
            String["by"],
            unique(premises),
            true
        ))
    end

    return examples
end

"""
Extract HOL4 proofs (with premise extraction from tactic brackets)
"""
function extract_hol4_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Match store_thm or prove calls
    for m in eachmatch(r"(store_thm|prove)\s*\(\s*[`\"]([^`\"]*)[`\"],\s*`([^`]*)`\s*,\s*(.+?)\)"s, content)
        theorem_name = strip(m.captures[2])
        goal = strip(m.captures[3])
        tactic_block = m.captures[4]

        # Extract tactics (simplified)
        tactics = [strip(t) for t in split(tactic_block, r">>|THEN") if !isempty(strip(t))]
        if isempty(tactics)
            tactics = String["REWRITE_TAC"]
        end

        # Extract premises from tactic arguments: metis_tac [theorem1, theorem2], rw [theorem1], fs [theorem1]
        premises = String[]
        try
            for tactic_match in eachmatch(r"\b(?:metis_tac|rw|fs|simp_tac|METIS_TAC)\s*\[([^\]]+)\]", tactic_block)
                # Extract individual theorem names from bracket contents
                bracket_content = tactic_match.captures[1]
                for item in split(bracket_content, r",\s*")
                    item = strip(item)
                    # Extract theorem name (remove any type annotations or arguments)
                    if !isempty(item)
                        theorem_ref = match(r"([A-Za-z_][A-Za-z0-9_\.]*)", item)
                        if theorem_ref !== nothing
                            push!(premises, theorem_ref.captures[1])
                        end
                    end
                end
            end
        catch
            # Continue with empty premises
        end

        push!(examples, ProofExample(
            "HOL4",
            filepath,
            theorem_name,
            goal,
            tactics,
            unique(premises),
            true
        ))
    end

    return examples
end

"""
Generic proof extraction (for simpler provers)
"""
function extract_generic_proofs(prover::String, filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Count statements as "proofs" for basic extraction
    pattern = get(PROOF_PATTERNS, prover, r"")
    if pattern != r""
        matches = collect(eachmatch(pattern, content))
        if !isempty(matches)
            push!(examples, ProofExample(
                prover,
                filepath,
                "generic_example",
                "extracted_from_$prover",
                String["auto"],
                String[],
                true
            ))
        end
    end

    return examples
end

"""
    extract_all_proofs(proofs_dir::String = "proofs") -> Vector{ProofExample}

Extract proofs from all example files.
"""
function extract_all_proofs(proofs_dir::String = "proofs")::Vector{ProofExample}
    all_examples = ProofExample[]

    prover_dirs = Dict(
        "Lean" => "lean",
        "Coq" => "coq",
        "Agda" => "agda",
        "Isabelle" => "isabelle",
        "Z3" => "z3",
        "CVC5" => "cvc5",
        "Metamath" => "metamath",
        "HOLLight" => "hol_light",
        "Mizar" => "mizar",
        "ACL2" => "acl2",
        "PVS" => "pvs",
        "HOL4" => "hol4"
    )

    for (prover, dir) in prover_dirs
        prover_path = joinpath(proofs_dir, dir)
        if isdir(prover_path)
            @info "Extracting from $prover..."
            files = filter(f -> !endswith(f, ".md") && !endswith(f, "README"), readdir(prover_path, join=true))

            for file in files
                examples = extract_from_file(prover, file)
                append!(all_examples, examples)
                @info "  $file: $(length(examples)) examples"
            end
        end
    end

    return all_examples
end

"""
Helper function to escape JSON strings
"""
function json_escape(s::String)::String
    s = replace(s, "\\" => "\\\\")
    s = replace(s, "\"" => "\\\"")
    s = replace(s, "\n" => "\\n")
    s = replace(s, "\r" => "\\r")
    s = replace(s, "\t" => "\\t")
    return s
end

"""
Convert array to JSON string
"""
function array_to_json(arr::Vector{String})::String
    items = ["\"$(json_escape(item))\"" for item in arr]
    return "[" * join(items, ",") * "]"
end

"""
    save_training_data(examples::Vector{ProofExample}, output_dir::String)

Save extracted examples as JSONL files for training.
"""
function save_training_data(examples::Vector{ProofExample}, output_dir::String = TRAINING_DATA_DIR)
    mkpath(output_dir)

    # Save proof states
    open(joinpath(output_dir, "proof_states.jsonl"), "w") do io
        for (i, ex) in enumerate(examples)
            line = "{\"id\":$i,\"prover\":\"$(ex.prover)\",\"theorem\":\"$(json_escape(ex.theorem_name))\",\"goal\":\"$(json_escape(ex.goal))\",\"context\":$(array_to_json(ex.premises))}"
            println(io, line)
        end
    end

    # Save tactic sequences
    open(joinpath(output_dir, "tactics.jsonl"), "w") do io
        for (i, ex) in enumerate(examples)
            for (step, tactic) in enumerate(ex.tactics)
                line = "{\"proof_id\":$i,\"step\":$step,\"tactic\":\"$(json_escape(tactic))\",\"prover\":\"$(ex.prover)\"}"
                println(io, line)
            end
        end
    end

    # Save premise usage
    open(joinpath(output_dir, "premises.jsonl"), "w") do io
        for (i, ex) in enumerate(examples)
            for premise in ex.premises
                line = "{\"proof_id\":$i,\"premise\":\"$(json_escape(premise))\",\"prover\":\"$(ex.prover)\",\"theorem\":\"$(json_escape(ex.theorem_name))\"}"
                println(io, line)
            end
        end
    end

    # Save summary statistics
    open(joinpath(output_dir, "stats.json"), "w") do io
        prover_counts = Dict(
            prover => count(ex -> ex.prover == prover, examples)
            for prover in unique([ex.prover for ex in examples])
        )

        counts_json = join(["\"$k\":$v" for (k, v) in prover_counts], ",")

        stats = """{
  "total_proofs": $(length(examples)),
  "total_tactics": $(sum(length(ex.tactics) for ex in examples)),
  "total_premises": $(sum(length(ex.premises) for ex in examples)),
  "proofs_by_prover": {$counts_json},
  "extracted_at": "$(Dates.now())"
}"""
        println(io, stats)
    end

    @info "Training data saved to $output_dir"
    @info "  - proof_states.jsonl: $(length(examples)) proof states"
    @info "  - tactics.jsonl: $(sum(length(ex.tactics) for ex in examples)) tactic applications"
    @info "  - premises.jsonl: $(sum(length(ex.premises) for ex in examples)) premise usages"
end

"""
    main()

Main entry point - extract training data from all proof examples.
"""
function main()
    @info "ECHIDNA Training Data Extraction v1.3"
    @info "======================================"

    # Extract proofs
    examples = extract_all_proofs()

    @info "\nExtraction Summary:"
    @info "  Total examples: $(length(examples))"
    for prover in sort(unique([ex.prover for ex in examples]))
        count = sum(ex -> ex.prover == prover, examples)
        @info "    $prover: $count"
    end

    # Save training data
    save_training_data(examples)

    @info "\n✓ Training data extraction complete!"
    return examples
end

# Run if executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
