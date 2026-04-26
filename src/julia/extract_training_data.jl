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
    elseif prover in ["Z3", "CVC5", "Alt-Ergo", "OpenSMT", "SMTRat"]
        examples = extract_smtlib_proofs(filepath, content)
    elseif prover in ["Vampire", "Eprover", "SPASS", "Prover9", "Zipperposition"]
        examples = extract_tptp_proofs(filepath, content)
    elseif prover == "Dafny"
        examples = extract_dafny_proofs(filepath, content)
    elseif prover == "Lean3"
        examples = extract_lean3_proofs(filepath, content)
    elseif prover in ["HOLLight", "HOL Light"]
        examples = extract_hol_light_proofs(filepath, content)
    elseif prover == "Metamath"
        examples = extract_metamath_proofs(filepath, content)
    elseif prover == "Tamarin"
        examples = extract_tamarin_proofs(filepath, content)
    elseif prover == "ProVerif"
        examples = extract_proverif_proofs(filepath, content)
    elseif prover == "Boogie"
        examples = extract_boogie_proofs(filepath, content)
    elseif prover in ["Viper", "ViperTool"]
        examples = extract_viper_proofs(filepath, content)
    elseif prover in ["MiniZinc", "Chuffed", "GLPK", "SCIP", "ORTools"]
        examples = extract_minizinc_proofs(filepath, content)
    elseif prover in ["Twelf", "TWELf"]
        examples = extract_twelf_proofs(filepath, content)
    elseif prover in ["Abella"]
        examples = extract_abella_proofs(filepath, content)
    elseif prover == "Matita"
        examples = extract_matita_proofs(filepath, content)
    elseif prover == "Dedukti"
        examples = extract_dedukti_proofs(filepath, content)
    elseif prover == "Arend"
        examples = extract_arend_proofs(filepath, content)
    elseif prover == "Minlog"
        examples = extract_minlog_proofs(filepath, content)
    elseif prover in ["LambdaProlog", "Lambda Prolog", "Teyjus"]
        examples = extract_lambda_prolog_proofs(filepath, content)
    elseif prover == "Alloy"
        examples = extract_alloy_proofs(filepath, content)
    elseif prover in ["NuSMV", "nuXmv"]
        examples = extract_nusmv_proofs(filepath, content)
    elseif prover in ["Spin", "Promela"]
        examples = extract_spin_proofs(filepath, content)
    elseif prover == "CBMC"
        examples = extract_cbmc_proofs(filepath, content)
    elseif prover in ["SeaHorn", "Seahorn"]
        examples = extract_seahorn_proofs(filepath, content)
    elseif prover in ["UPPAAL", "Uppaal"]
        examples = extract_uppaal_proofs(filepath, content)
    elseif prover in ["Cameleer", "Gospel"]
        examples = extract_cameleer_proofs(filepath, content)
    elseif prover == "Mercury"
        examples = extract_mercury_proofs(filepath, content)
    elseif prover in ["Naproche", "SAD"]
        examples = extract_naproche_proofs(filepath, content)
    elseif prover == "OpenTheory"
        examples = extract_opentheory_proofs(filepath, content)
    elseif prover == "NuPRL"
        examples = extract_nuprl_proofs(filepath, content)
    elseif prover in ["Imandra"]
        examples = extract_imandra_proofs(filepath, content)
    elseif prover in ["ProofPower", "Proof Power"]
        examples = extract_proofpower_proofs(filepath, content)
    elseif prover in ["ACL2s", "ACL2-Sedan"]
        examples = extract_acl2s_proofs(filepath, content)
    elseif prover in ["Kissat", "DIMACS", "SAT"]
        examples = extract_kissat_proofs(filepath, content)
    elseif prover in ["Athena"]
        examples = extract_athena_proofs(filepath, content)
    elseif prover in ["FramaC", "Frama-C", "ACSL"]
        examples = extract_framac_proofs(filepath, content)
    elseif prover in ["Eprime", "Essence", "EssencePrime"]
        examples = extract_eprime_proofs(filepath, content)
    elseif prover in ["Albatross"]
        examples = extract_albatross_proofs(filepath, content)
    elseif prover in ["HOL", "HOLZero", "ProofPowerHOL"]
        examples = extract_hol_proofs(filepath, content)
    elseif prover in ["Rocq"]
        examples = extract_coq_proofs(filepath, content)
    elseif prover in ["GPUVerify", "GPU", "gpu-verify"]
        examples = extract_gpuverify_proofs(filepath, content)
    elseif prover == "Faial"
        examples = extract_faial_proofs(filepath, content)
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
Extract SMT-LIB 2 proofs (.smt2 files — Z3, CVC5, Alt-Ergo, OpenSMT, SMTRat, etc.)

Handles named assertions `(assert (! <expr> :named <name>))`, `define-fun`
definitions, and `check-sat` proof obligations. Tactics are empty because
SMT solvers are push-button (no tactic language).
"""
function extract_smtlib_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Collect named assertions: (assert (! <expr> :named <name>))
    named_assertions = String[]
    try
        for m in eachmatch(r"\(assert\s+\(!\s+(.+?)\s+:named\s+(\w+)\s*\)\s*\)"s, content)
            push!(named_assertions, m.captures[2])
        end
    catch
        # Malformed SMT-LIB — continue with empty
    end

    # Extract define-fun declarations as goals
    try
        for m in eachmatch(r"\(define-fun\s+(\w+)\s+\(([^)]*)\)\s+(\S+)\s+(.*?)\)"s, content)
            fun_name   = m.captures[1]
            return_ty  = m.captures[3]
            body       = strip(m.captures[4])
            push!(examples, ProofExample(
                "Z3",
                filepath,
                fun_name,
                "(define-fun $fun_name : $return_ty)",
                String[],
                unique(named_assertions),
                true
            ))
        end
    catch
        # Skip malformed define-fun blocks
    end

    # Each check-sat paired with the preceding named assertions forms a proof obligation
    try
        if occursin(r"\(check-sat\)", content) && !isempty(named_assertions)
            push!(examples, ProofExample(
                "Z3",
                filepath,
                "check_sat_obligation",
                "(check-sat)",
                String[],
                unique(named_assertions),
                true
            ))
        end
    catch
        # Continue on error
    end

    return examples
end

"""
Extract TPTP format proofs (.tptp, .p files — Vampire, E Prover, SPASS, Prover9, Zipperposition, etc.)

Handles `fof(name, role, formula)` and `cnf(name, role, formula)` declarations.
Conjectures become goals; axioms and hypotheses become premises. Tactics are empty
because ATP provers are push-button.
"""
function extract_tptp_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Collect all axiom/hypothesis names as premises
    premise_names = String[]
    try
        for m in eachmatch(r"(?:fof|cnf)\s*\(\s*(\w+)\s*,\s*(axiom|hypothesis|lemma)\s*,"s, content)
            push!(premise_names, m.captures[1])
        end
    catch
        # Continue with empty premises
    end

    # Extract conjectures / negated_conjectures as goals
    try
        for m in eachmatch(r"(fof|cnf)\s*\(\s*(\w+)\s*,\s*(conjecture|negated_conjecture)\s*,\s*(.*?)\)\s*\."s, content)
            formula_kind = m.captures[1]
            thm_name     = m.captures[2]
            role         = m.captures[3]
            formula      = strip(m.captures[4])
            push!(examples, ProofExample(
                "Vampire",
                filepath,
                thm_name,
                "[$formula_kind/$role] $formula",
                String[],
                unique(premise_names),
                true
            ))
        end
    catch
        # Skip malformed declarations
    end

    return examples
end

"""
Extract Dafny proofs (.dfy files)

Handles `method`, `lemma`, and `function` declarations. `ensures` clauses
become goals; `requires` clauses become premises. Supported tactics:
`calc`, `assert`, `forall`, `decreases`.
"""
function extract_dafny_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Match method / lemma / function declaration blocks up to the opening brace
    try
        for m in eachmatch(r"(method|lemma|function)\s+(\w+)\s*\([^)]*\)([^{]*)\{"s, content)
            decl_kind  = m.captures[1]
            decl_name  = m.captures[2]
            spec_block = m.captures[3]  # requires / ensures clauses

            # Extract ensures clauses as goals
            goals = String[]
            for em in eachmatch(r"ensures\s+(.+?)(?=ensures|requires|modifies|reads|decreases|\{|\n\n)"s, spec_block)
                push!(goals, strip(em.captures[1]))
            end

            # Extract requires clauses as premises
            premises = String[]
            try
                for rm in eachmatch(r"requires\s+(.+?)(?=ensures|requires|modifies|reads|decreases|\{|\n\n)"s, spec_block)
                    push!(premises, strip(rm.captures[1]))
                end
            catch
                # Continue
            end

            # Extract tactic keywords from the body (approximate — look ahead in content)
            tactics = String[]
            try
                for kw in ("calc", "assert", "forall", "decreases")
                    if occursin(Regex("\\b$kw\\b"), content[m.offset:min(m.offset+2000, lastindex(content))])
                        push!(tactics, kw)
                    end
                end
            catch
                # Leave tactics empty
            end

            goal_str = isempty(goals) ? "$(decl_kind)_$(decl_name)" : join(goals, " && ")
            push!(examples, ProofExample(
                "Dafny",
                filepath,
                decl_name,
                goal_str,
                tactics,
                unique(premises),
                true
            ))
        end
    catch
        # Skip malformed declarations
    end

    return examples
end

"""
Extract Lean 3 proofs (.lean files using Lean 3 conventions)

Lean 3 uses lowercase `import mathlib` (vs Lean 4's `import Mathlib`).
Handles `theorem`/`lemma` declarations with `have` premises and standard
Lean 3 tactics.
"""
function extract_lean3_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Heuristic: Lean 3 imports use lowercase module names
    is_lean3 = occursin(r"\bimport\s+mathlib\b", content) ||
               occursin(r"\bimport\s+tactic\b", content) ||
               occursin(r"\bimport\s+data\.", content)

    if !is_lean3
        return examples
    end

    # Match theorem / lemma declarations — Lean 3 style: `:= begin ... end` or `:= by ...`
    try
        for m in eachmatch(r"(theorem|lemma)\s+(\w+)\s*([^:]*):([^:=]+):=\s*(?:begin|by)\s+(.+?)(?:\nend\b|\n(?:theorem|lemma)|\Z)"s, content)
            theorem_name = m.captures[2]
            goal         = strip(m.captures[4])
            proof_block  = m.captures[5]

            # Extract individual tactics
            tactics = [strip(t) for t in split(proof_block, r"<;>|,\s*\n|\n") if !isempty(strip(t))]

            # Extract have-premises: `have h : type := proof`
            premises = String[]
            try
                for hm in eachmatch(r"have\s+(\w+)\s*:", proof_block)
                    push!(premises, hm.captures[1])
                end
                # Also extract apply/rw references
                for tactic in tactics
                    pm = match(r"(?:apply|rw|exact)\s+([A-Za-z_][A-Za-z0-9_\.]*)", tactic)
                    if pm !== nothing
                        push!(premises, pm.captures[1])
                    end
                end
            catch
                # Continue
            end

            push!(examples, ProofExample(
                "Lean3",
                filepath,
                theorem_name,
                goal,
                tactics,
                unique(premises),
                true
            ))
        end
    catch
        # Skip malformed declarations
    end

    return examples
end

"""
Extract HOL Light proofs (.ml files)

Handles `prove(goal, tactic)` calls and `let name = prove(...)` bindings.
Premises are extracted from `ASSUME <term>` and `MP <thm1> <thm2>` patterns.
Recognised tactics: `REWRITE_TAC`, `MESON_TAC`, `ARITH_TAC`,
`REAL_ARITH_TAC`, `SIMP_TAC`, `ASM_SIMP_TAC`.
"""
function extract_hol_light_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Match: let name = prove(`goal`, tactic_block)
    try
        for m in eachmatch(r"let\s+(\w+)\s*=\s*prove\s*\(\s*`([^`]*)`\s*,\s*(.+?)\)"s, content)
            thm_name     = m.captures[1]
            goal         = strip(m.captures[2])
            tactic_block = m.captures[3]

            # Extract tactic names
            tactics = String[]
            for tac in ("REWRITE_TAC", "MESON_TAC", "ARITH_TAC", "REAL_ARITH_TAC", "SIMP_TAC", "ASM_SIMP_TAC")
                if occursin(tac, tactic_block)
                    push!(tactics, tac)
                end
            end

            # Extract premises from ASSUME and MP patterns
            premises = String[]
            try
                for am in eachmatch(r"ASSUME\s+`([^`]+)`", tactic_block)
                    push!(premises, strip(am.captures[1]))
                end
                for mm in eachmatch(r"MP\s+(\w+)\s+(\w+)", tactic_block)
                    push!(premises, mm.captures[1])
                    push!(premises, mm.captures[2])
                end
                # Also collect theorem names passed to tactic lists: [SOME_LEMMA; ...]
                for lm in eachmatch(r"\[([A-Z_][A-Z0-9_]*(?:;\s*[A-Z_][A-Z0-9_]*)*)\]", tactic_block)
                    for name in split(lm.captures[1], r";\s*")
                        push!(premises, strip(name))
                    end
                end
            catch
                # Continue
            end

            push!(examples, ProofExample(
                "HOLLight",
                filepath,
                thm_name,
                goal,
                isempty(tactics) ? String["MESON_TAC"] : tactics,
                unique(premises),
                true
            ))
        end
    catch
        # Skip malformed prove() calls
    end

    return examples
end

"""
Extract Metamath proofs (.mm files)

Handles `\$p label \$= proof_steps \$.` provable assertions and
`\$a label \$= ... \$.` axiom assertions. The label before `\$p` is the
theorem name; referenced step labels become premises.
"""
function extract_metamath_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Collect all axiom labels for premise lookup
    axiom_labels = String[]
    try
        for m in eachmatch(r"(\w+)\s+\\\$a\s+(.*?)\\\$\."s, content)
            push!(axiom_labels, m.captures[1])
        end
    catch
        # Continue
    end

    # Extract provable assertions: label $p formula $= steps $.
    try
        for m in eachmatch(r"(\w+)\s+\\\$p\s+(.*?)\\\$=\s+(.*?)\\\$\."s, content)
            thm_label  = m.captures[1]
            formula    = strip(m.captures[2])
            proof_steps = strip(m.captures[3])

            # Premises = step labels that appear in axiom_labels
            step_tokens = split(proof_steps, r"\s+")
            premises = filter(t -> t in axiom_labels, step_tokens)

            # Also include any referenced theorem labels (non-whitespace tokens)
            all_referenced = unique(filter(!isempty, step_tokens))

            push!(examples, ProofExample(
                "Metamath",
                filepath,
                thm_label,
                formula,
                String[],
                unique(vcat(premises, all_referenced)),
                true
            ))
        end
    catch
        # Skip malformed assertions
    end

    return examples
end

"""
Extract Tamarin prover security proofs (.spthy files)

Handles `lemma <name>: <formula>` blocks and `rule <name>` declarations.
Lemma formulas (after quantifiers like `All`, `Ex`, `==>`) are goals;
rule names referenced in proof terms are premises. Recognised tactics:
`solve`, `simplify`, `induction`, `contradiction`.
"""
function extract_tamarin_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Collect rule names as potential premises
    rule_names = String[]
    try
        for m in eachmatch(r"\brule\s+(\w+)\s*:", content)
            push!(rule_names, m.captures[1])
        end
    catch
        # Continue
    end

    # Extract lemma blocks
    try
        for m in eachmatch(r"\blemma\s+(\w+)\s*(?:\[[^\]]*\])?\s*:\s*(.*?)(?=\blemma\b|\bend\b|\Z)"s, content)
            lemma_name = m.captures[1]
            lemma_body = strip(m.captures[2])

            # Goal is the formula (trim proof block if present)
            goal_match = match(r"(.*?)(?:\bproof\b|\Z)"s, lemma_body)
            goal = goal_match !== nothing ? strip(goal_match.captures[1]) : lemma_body

            # Premises: rule names referenced anywhere in the lemma body
            premises = String[]
            try
                for rn in rule_names
                    if occursin(rn, lemma_body)
                        push!(premises, rn)
                    end
                end
            catch
                # Continue
            end

            # Tactic keywords present in the proof block
            tactics = String[]
            proof_block_match = match(r"\bproof\b(.*?)(?=\blemma\b|\bend\b|\Z)"s, lemma_body)
            if proof_block_match !== nothing
                for tac in ("solve", "simplify", "induction", "contradiction")
                    if occursin(tac, proof_block_match.captures[1])
                        push!(tactics, tac)
                    end
                end
            end

            push!(examples, ProofExample(
                "Tamarin",
                filepath,
                lemma_name,
                goal,
                tactics,
                unique(premises),
                true
            ))
        end
    catch
        # Skip malformed lemma blocks
    end

    return examples
end

"""
Extract ProVerif security proofs (.pv files)

Handles `query <formula>` declarations as goals, `let <name> = <process>`
definitions, and `event <name>` declarations as premises. The query
formula is the proof goal; referenced event names and let-bindings form
the premises.
"""
function extract_proverif_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Collect event declarations as premises
    event_names = String[]
    try
        for m in eachmatch(r"\bevent\s+(\w+)\s*(?:\([^)]*\))?\s*\.", content)
            push!(event_names, m.captures[1])
        end
    catch
        # Continue
    end

    # Collect let-binding names as additional premises
    let_names = String[]
    try
        for m in eachmatch(r"\blet\s+(\w+)\s*=", content)
            push!(let_names, m.captures[1])
        end
    catch
        # Continue
    end

    # Extract query declarations as proof goals
    try
        for m in eachmatch(r"\bquery\s+(.*?)(?=\bquery\b|\bprocess\b|\Z)"s, content)
            query_body = strip(m.captures[1])
            # Use a synthetic theorem name based on position
            thm_name = "query_$(length(examples) + 1)"

            # Premises: event and let names referenced in the query
            premises = String[]
            for en in event_names
                if occursin(en, query_body)
                    push!(premises, en)
                end
            end
            for ln in let_names
                if occursin(ln, query_body)
                    push!(premises, ln)
                end
            end

            push!(examples, ProofExample(
                "ProVerif",
                filepath,
                thm_name,
                query_body,
                String[],
                unique(premises),
                true
            ))
        end
    catch
        # Skip malformed query blocks
    end

    return examples
end

"""
Extract Boogie intermediate verification language proofs (.bpl files)

Handles `procedure <name>(...)` declarations. `ensures` clauses become
goals; `requires` clauses become premises. Tactics are empty because
Boogie is auto-active (Z3-backed, no tactic language).
"""
function extract_boogie_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    try
        for m in eachmatch(r"\bprocedure\s+(\w+)\s*\(([^)]*)\)([^{]*)\{"s, content)
            proc_name  = m.captures[1]
            spec_block = m.captures[3]

            # ensures clauses → goals
            goals = String[]
            try
                for em in eachmatch(r"\bensures\s+(.+?)(?=ensures|requires|modifies|\{|;)"s, spec_block)
                    push!(goals, strip(em.captures[1]))
                end
            catch
                # Continue
            end

            # requires clauses → premises
            premises = String[]
            try
                for rm in eachmatch(r"\brequires\s+(.+?)(?=ensures|requires|modifies|\{|;)"s, spec_block)
                    push!(premises, strip(rm.captures[1]))
                end
            catch
                # Continue
            end

            goal_str = isempty(goals) ? "procedure_$proc_name" : join(goals, " && ")
            push!(examples, ProofExample(
                "Boogie",
                filepath,
                proc_name,
                goal_str,
                String[],
                unique(premises),
                true
            ))
        end
    catch
        # Skip malformed procedure declarations
    end

    return examples
end

"""
Extract Viper (Viper Verification Infrastructure) proofs (.vpr files)

Handles `method <name>(...)` declarations. `ensures` clauses become
goals; `requires` clauses and loop `invariant` expressions are premises.
Tactics are empty (Viper is auto-active via Z3/Carbon/Silicon).
"""
function extract_viper_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    try
        for m in eachmatch(r"\bmethod\s+(\w+)\s*\(([^)]*)\)([^{]*)\{"s, content)
            method_name = m.captures[1]
            spec_block  = m.captures[3]

            # ensures → goals
            goals = String[]
            try
                for em in eachmatch(r"\bensures\s+(.+?)(?=ensures|requires|returns|\{)"s, spec_block)
                    push!(goals, strip(em.captures[1]))
                end
            catch
                # Continue
            end

            # requires → premises
            premises = String[]
            try
                for rm in eachmatch(r"\brequires\s+(.+?)(?=ensures|requires|returns|\{)"s, spec_block)
                    push!(premises, strip(rm.captures[1]))
                end
            catch
                # Continue
            end

            # invariant inside while loops (scan body region in content)
            try
                body_region = content[m.offset:min(m.offset + 3000, lastindex(content))]
                for im in eachmatch(r"\binvariant\s+(.+?)(?=invariant|while|if|assert|\})"s, body_region)
                    push!(goals, "invariant: " * strip(im.captures[1]))
                end
            catch
                # Continue
            end

            goal_str = isempty(goals) ? "method_$method_name" : join(goals, " && ")
            push!(examples, ProofExample(
                "Viper",
                filepath,
                method_name,
                goal_str,
                String[],
                unique(premises),
                true
            ))
        end
    catch
        # Skip malformed method declarations
    end

    return examples
end

"""
Extract MiniZinc / constraint programming proof obligations (.mzn files)

Handles `constraint <expr>` declarations as axioms (premises), the
`solve minimize/maximize/satisfy` directive as the proof goal, and
`predicate <name>(...)` declarations as named premises. Tactics are
empty (constraint solver — no tactic language).
"""
function extract_minizinc_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Collect constraint expressions as axioms (premises)
    constraints = String[]
    try
        for m in eachmatch(r"\bconstraint\s+(.+?)(?=constraint|solve|predicate|;|\Z)"s, content)
            push!(constraints, strip(m.captures[1]))
        end
    catch
        # Continue
    end

    # Collect predicate names as named premises
    predicate_names = String[]
    try
        for m in eachmatch(r"\bpredicate\s+(\w+)\s*\(", content)
            push!(predicate_names, m.captures[1])
        end
    catch
        # Continue
    end

    # The solve directive is the proof goal
    try
        for m in eachmatch(r"\bsolve\s+(minimize|maximize|satisfy)\s*([^;]*);?"s, content)
            objective = m.captures[1]
            target    = strip(m.captures[2])
            goal_str  = isempty(target) ? "solve_$objective" : "solve $objective $target"

            push!(examples, ProofExample(
                "MiniZinc",
                filepath,
                "solve_objective",
                goal_str,
                String[],
                unique(vcat(predicate_names, constraints)),
                true
            ))
        end
    catch
        # Continue
    end

    # If no solve directive found but constraints exist, emit a single fallback example
    if isempty(examples) && !isempty(constraints)
        push!(examples, ProofExample(
            "MiniZinc",
            filepath,
            "constraint_model",
            "constraint_satisfaction",
            String[],
            unique(vcat(predicate_names, constraints)),
            true
        ))
    end

    return examples
end

"""
Extract Twelf logical framework proofs (.elf, .twelf files)

Handles `<name> : <type> = <term>.` declarations. Type families ending
in `type` are propositions (goals); the `= <term>` part provides named
references that become premises (simple identifier extraction).
"""
function extract_twelf_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    try
        for m in eachmatch(r"(\w+)\s*:\s*(.+?)\s*=\s*(.+?)\s*\."s, content)
            decl_name = m.captures[1]
            type_expr = strip(m.captures[2])
            term_expr = strip(m.captures[3])

            # Identify goals: type families whose type is `type`
            is_goal = endswith(type_expr, "type") || occursin(r"\btype\b", type_expr)

            # Extract referenced names from the term (simple identifier scan)
            premises = String[]
            try
                for pm in eachmatch(r"\b([a-z][A-Za-z0-9_/-]*)\b", term_expr)
                    candidate = pm.captures[1]
                    # Skip Twelf keywords and short tokens
                    if candidate ∉ ("type", "kind", "prop", "of", "in", "fn", "let", "val") && length(candidate) > 1
                        push!(premises, candidate)
                    end
                end
            catch
                # Continue
            end

            push!(examples, ProofExample(
                "Twelf",
                filepath,
                decl_name,
                is_goal ? "[$type_expr]" : type_expr,
                String[],
                unique(premises),
                true
            ))
        end
    catch
        # Skip malformed declarations
    end

    return examples
end

"""
Extract Abella interactive theorem prover proofs (.thm files)

Handles `Theorem name : formula.` declarations. Proof steps following
`by ...` are parsed as tactics. Premises come from `apply H with ...`
hypothesis references inside proof blocks.
"""
function extract_abella_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    try
        # Match Theorem name : formula. by tactic_block.
        for m in eachmatch(r"(?:Theorem|Lemma)\s+(\w+)\s*:\s*(.+?)\.\s*by\s+(.*?)\."s, content)
            thm_name   = m.captures[1]
            formula    = strip(m.captures[2])
            proof_body = m.captures[3]

            # Split tactic steps on whitespace sequences between keywords
            tactics = String[]
            try
                for t in split(proof_body, r"\s*\.\s*|\s*;\s*")
                    s = strip(t)
                    if !isempty(s)
                        push!(tactics, s)
                    end
                end
            catch
                # Continue with empty tactics
            end

            # Premises: hypothesis names referenced via `apply H with ...`
            premises = String[]
            try
                for pm in eachmatch(r"apply\s+(\w+)(?:\s+with\s+\w+\s*=\s*\w+)*", proof_body)
                    push!(premises, pm.captures[1])
                end
            catch
                # Continue with empty premises
            end

            push!(examples, ProofExample(
                "Abella",
                filepath,
                thm_name,
                formula,
                tactics,
                unique(premises),
                true
            ))
        end
    catch
        # Skip malformed declarations
    end

    return examples
end

"""
Extract Matita interactive theorem prover proofs (.ma files)

Handles `theorem name: statement ≝ proof.`, `lemma`, and `definition`
declarations. The statement (before ≝) is the goal. Premises come from
`apply`, `exact`, and `rewrite` targets in the proof body.
"""
function extract_matita_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    try
        # Match theorem/lemma/definition ... : statement ≝ proof.
        # ≝ is Unicode U+225D (definition equals)
        for m in eachmatch(r"(?:theorem|lemma|definition)\s+(\w+)\s*(?:\([^)]*\))?\s*:\s*(.+?)\s*(?:≝|:=)\s*(.*?)\.\s*$"ms, content)
            decl_name  = m.captures[1]
            statement  = strip(m.captures[2])
            proof_body = m.captures[3]

            # Tactics: apply, exact, rewrite, elim, intro keywords
            tactics = String[]
            try
                for tm in eachmatch(r"\b(apply|exact|rewrite|elim|intro|assumption|reflexivity|transitivity)\b", proof_body)
                    push!(tactics, tm.captures[1])
                end
                unique!(tactics)
            catch
                # Continue
            end

            # Premises: identifiers following apply / exact / rewrite
            premises = String[]
            try
                for pm in eachmatch(r"(?:apply|exact|rewrite)\s+(\w+)", proof_body)
                    push!(premises, pm.captures[1])
                end
            catch
                # Continue
            end

            push!(examples, ProofExample(
                "Matita",
                filepath,
                decl_name,
                statement,
                tactics,
                unique(premises),
                true
            ))
        end
    catch
        # Skip malformed declarations
    end

    return examples
end

"""
Extract Dedukti logical framework proofs (.dk files)

Every top-level declaration `name : type.` is a potential theorem.
The type expression is the goal. Premises are identifiers referenced
inside the type expression (simple identifier scan, keywords excluded).
"""
function extract_dedukti_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Dedukti keywords to skip when scanning for premise identifiers
    dk_keywords = Set(["Type", "Kind", "def", "thm", "injective", "private", "protected"])

    try
        # Top-level: identifier followed by : then type expression ending with .
        for m in eachmatch(r"^([A-Za-z_]\w*)\s*:\s*(.+?)\s*\."m, content)
            decl_name = m.captures[1]
            type_expr = strip(m.captures[2])

            # Skip lines that look like rule/rewrite definitions (use =>)
            occursin(r"=>|:=", type_expr) && continue

            # Premises: all identifiers appearing in the type expression
            premises = String[]
            try
                for pm in eachmatch(r"\b([A-Za-z_]\w*)\b", type_expr)
                    candidate = pm.captures[1]
                    if candidate ∉ dk_keywords && length(candidate) > 1 && candidate != decl_name
                        push!(premises, candidate)
                    end
                end
            catch
                # Continue
            end

            push!(examples, ProofExample(
                "Dedukti",
                filepath,
                decl_name,
                type_expr,
                String[],
                unique(premises),
                true
            ))
        end
    catch
        # Skip malformed declarations
    end

    return examples
end

"""
Extract Arend theorem prover proofs (.ard files)

Handles `\\func name ... : ReturnType \\where { ... }` and
`\\lemma name ... : Prop` declarations. The return type / Prop is the
goal. Import module names are collected as premises.
"""
function extract_arend_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Collect \\import module names as premises (file-level)
    import_premises = String[]
    try
        for im in eachmatch(r"\\import\s+([\w.]+)", content)
            push!(import_premises, im.captures[1])
        end
    catch
        # Continue
    end

    try
        # Match \func or \lemma declarations with a return type
        for m in eachmatch(r"\\(?:func|lemma)\s+(\w+)[^:]*:\s*(.+?)(?=\\where|\{|\\func|\\lemma|\\data|\Z)"s, content)
            decl_name   = m.captures[1]
            return_type = strip(m.captures[2])

            push!(examples, ProofExample(
                "Arend",
                filepath,
                decl_name,
                return_type,
                String[],
                unique(import_premises),
                true
            ))
        end
    catch
        # Skip malformed declarations
    end

    return examples
end

"""
Extract Minlog proof assistant proofs (SML-based .sml files)

Handles `add-theorem "name" formula` calls as goals and
`use-theorem "name"` calls as premise references. Common tactic keywords
(`simp`, `elim`, `intro`, `auto`, `norm`) are collected as tactics.
"""
function extract_minlog_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Collect use-theorem references as premises
    used_theorems = String[]
    try
        for um in eachmatch(r"use-theorem\s+\"([^\"]+)\"", content)
            push!(used_theorems, um.captures[1])
        end
    catch
        # Continue
    end

    # Common Minlog tactic keywords present in proof scripts
    tactic_kws = ["simp", "elim", "intro", "auto", "norm"]
    tactics = filter(kw -> occursin(Regex("\\b$kw\\b"), content), tactic_kws)

    try
        for m in eachmatch(r"add-theorem\s+\"([^\"]+)\"\s+(.+?)(?=add-theorem|$)"s, content)
            thm_name = m.captures[1]
            formula  = strip(m.captures[2])
            # Trim trailing SML punctuation
            formula  = replace(formula, r"[;)]+$" => "")

            push!(examples, ProofExample(
                "Minlog",
                filepath,
                thm_name,
                formula,
                tactics,
                unique(used_theorems),
                true
            ))
        end
    catch
        # Skip malformed declarations
    end

    return examples
end

"""
Extract Lambda Prolog / Teyjus proofs (.lp, .mod files)

Handles `theorem Name :- Body.` clauses where the head predicate is the
goal and body predicates (comma-separated) are premises. Also detects
module declarations via `:- module Name, [exports].`.
"""
function extract_lambda_prolog_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    try
        # Match theorem/lemma head :- body.
        for m in eachmatch(r"(?:theorem|lemma)\s+(\w+)\s*:-\s*(.*?)\."s, content)
            pred_name = m.captures[1]
            body      = m.captures[2]

            # Premises: comma-separated predicates in the body
            premises = String[]
            try
                for part in split(body, ',')
                    s = strip(part)
                    # Extract the functor name (before any '(')
                    head_match = match(r"^([A-Za-z_]\w*)", s)
                    if head_match !== nothing && !isempty(head_match.captures[1])
                        push!(premises, head_match.captures[1])
                    end
                end
            catch
                # Continue
            end

            push!(examples, ProofExample(
                "LambdaProlog",
                filepath,
                pred_name,
                "theorem $pred_name",
                String[],
                unique(premises),
                true
            ))
        end
    catch
        # Skip malformed clauses
    end

    # Also capture standard Prolog-style named clauses: Name :- Cond1, Cond2.
    try
        for m in eachmatch(r"^([a-z]\w*)\s*(?:\([^)]*\))?\s*:-\s*(.*?)\."ms, content)
            head_name = m.captures[1]
            # Skip already-matched theorem/lemma pattern
            head_name in ("theorem", "lemma", "module", "use_module", "ensure_loaded") && continue
            body = m.captures[2]

            premises = String[]
            try
                for part in split(body, ',')
                    s = strip(part)
                    hm = match(r"^([A-Za-z_]\w*)", s)
                    if hm !== nothing && !isempty(hm.captures[1])
                        push!(premises, hm.captures[1])
                    end
                end
            catch
                # Continue
            end

            push!(examples, ProofExample(
                "LambdaProlog",
                filepath,
                head_name,
                "clause $head_name",
                String[],
                unique(premises),
                true
            ))
        end
    catch
        # Skip malformed clauses
    end

    return examples
end

"""
Extract Alloy model checker specifications (.als files)

`assert AssertName { ... }` blocks → goals. `pred PredName { ... }` and
`fact FactName { ... }` declarations provide named premises. `check`
commands confirm verified assertions.
"""
function extract_alloy_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Collect predicate names as premises
    pred_names = String[]
    try
        for pm in eachmatch(r"\bpred\s+(\w+)\s*(?:\[[^\]]*\])?\s*\{", content)
            push!(pred_names, pm.captures[1])
        end
    catch
        # Continue
    end

    # Collect fact names as premises
    fact_names = String[]
    try
        for fm in eachmatch(r"\bfact\s+(\w+)\s*\{", content)
            push!(fact_names, fm.captures[1])
        end
    catch
        # Continue
    end

    all_premises = unique(vcat(pred_names, fact_names))

    try
        # Each assert declaration is a proof goal
        for m in eachmatch(r"\bassert\s+(\w+)\s*\{([^}]*)\}"s, content)
            assert_name = m.captures[1]
            formula     = strip(m.captures[2])

            push!(examples, ProofExample(
                "Alloy",
                filepath,
                assert_name,
                formula,
                String[],
                unique(all_premises),
                true
            ))
        end
    catch
        # Skip malformed assert blocks
    end

    # If no assert blocks, emit one example per `check` command
    if isempty(examples)
        try
            for cm in eachmatch(r"\bcheck\s+(\w+)", content)
                push!(examples, ProofExample(
                    "Alloy",
                    filepath,
                    cm.captures[1],
                    "check $(cm.captures[1])",
                    String[],
                    unique(all_premises),
                    true
                ))
            end
        catch
            # Continue
        end
    end

    return examples
end

"""
Extract NuSMV / nuXmv model checker verification obligations (.smv files)

`LTLSPEC formula` and `CTLSPEC formula` lines → goals (the formula).
`INVARSPEC formula` → invariant as goal. `DEFINE name := expr` named
expressions are collected as premises.
"""
function extract_nusmv_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Collect DEFINE names as premises
    define_names = String[]
    try
        for dm in eachmatch(r"\bDEFINE\b[^\n]*\b(\w+)\s*:=", content)
            push!(define_names, dm.captures[1])
        end
    catch
        # Continue
    end

    spec_count = Ref(0)

    try
        # LTLSPEC
        for m in eachmatch(r"\bLTLSPEC\b\s*(.+?)(?=\n(?:LTLSPEC|CTLSPEC|INVARSPEC|INIT|TRANS|MODULE|\Z))"s, content)
            spec_count[] += 1
            formula = strip(m.captures[1])
            push!(examples, ProofExample(
                "NuSMV",
                filepath,
                "ltlspec_$(spec_count[])",
                "LTLSPEC $formula",
                String[],
                unique(define_names),
                true
            ))
        end
    catch
        # Continue
    end

    try
        # CTLSPEC
        for m in eachmatch(r"\bCTLSPEC\b\s*(.+?)(?=\n(?:LTLSPEC|CTLSPEC|INVARSPEC|INIT|TRANS|MODULE|\Z))"s, content)
            spec_count[] += 1
            formula = strip(m.captures[1])
            push!(examples, ProofExample(
                "NuSMV",
                filepath,
                "ctlspec_$(spec_count[])",
                "CTLSPEC $formula",
                String[],
                unique(define_names),
                true
            ))
        end
    catch
        # Continue
    end

    try
        # INVARSPEC
        for m in eachmatch(r"\bINVARSPEC\b\s*(.+?)(?=\n)"s, content)
            spec_count[] += 1
            formula = strip(m.captures[1])
            push!(examples, ProofExample(
                "NuSMV",
                filepath,
                "invarspec_$(spec_count[])",
                "INVARSPEC $formula",
                String[],
                unique(define_names),
                true
            ))
        end
    catch
        # Continue
    end

    return examples
end

"""
Extract Spin / Promela model checker proofs (.pml files)

`ltl propname { formula }` → goals (the LTL formula). `assert(condition)`
inside proctypes → goals. `proctype Name(...)` names are collected as
premises.
"""
function extract_spin_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Collect proctype names as premises
    proc_names = String[]
    try
        for pm in eachmatch(r"\bproctype\s+(\w+)\s*\(", content)
            push!(proc_names, pm.captures[1])
        end
    catch
        # Continue
    end

    try
        # LTL properties: ltl propname { formula }
        for m in eachmatch(r"\bltl\s+(\w+)\s*\{([^}]*)\}"s, content)
            prop_name = m.captures[1]
            formula   = strip(m.captures[2])
            push!(examples, ProofExample(
                "Spin",
                filepath,
                prop_name,
                "ltl $formula",
                String[],
                unique(proc_names),
                true
            ))
        end
    catch
        # Skip malformed ltl blocks
    end

    try
        # assert(condition) inside proctypes
        for m in eachmatch(r"\bassert\s*\(([^)]+)\)", content)
            cond = strip(m.captures[1])
            push!(examples, ProofExample(
                "Spin",
                filepath,
                "assert",
                "assert($cond)",
                String[],
                unique(proc_names),
                true
            ))
        end
    catch
        # Skip malformed assert calls
    end

    return examples
end

"""
Extract CBMC bounded model checker proof annotations (annotated C files)

`__CPROVER_assert(condition, "message")` → goal (condition + message).
`__CPROVER_assume(condition)` → premise (assumed condition).
`__CPROVER_requires` / `__CPROVER_ensures` → pre/post-conditions.
"""
function extract_cbmc_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Collect __CPROVER_assume conditions as premises
    assumptions = String[]
    try
        for am in eachmatch(r"__CPROVER_assume\s*\(([^)]+)\)", content)
            push!(assumptions, strip(am.captures[1]))
        end
    catch
        # Continue
    end

    # Collect __CPROVER_requires clauses as premises
    try
        for rm in eachmatch(r"__CPROVER_requires\s*\(([^)]+)\)", content)
            push!(assumptions, "requires: " * strip(rm.captures[1]))
        end
    catch
        # Continue
    end

    assert_count = Ref(0)

    try
        # __CPROVER_assert(condition, "message")
        for m in eachmatch(r"__CPROVER_assert\s*\(\s*([^,]+),\s*\"([^\"]*)\"\s*\)", content)
            assert_count[] += 1
            cond    = strip(m.captures[1])
            message = m.captures[2]
            push!(examples, ProofExample(
                "CBMC",
                filepath,
                "assert_$(assert_count[])",
                "$cond /* $message */",
                String[],
                unique(assumptions),
                true
            ))
        end
    catch
        # Skip malformed assertions
    end

    try
        # __CPROVER_ensures clauses as goals (if no assert found)
        for m in eachmatch(r"__CPROVER_ensures\s*\(([^)]+)\)", content)
            assert_count[] += 1
            ensures = strip(m.captures[1])
            push!(examples, ProofExample(
                "CBMC",
                filepath,
                "ensures_$(assert_count[])",
                "ensures: $ensures",
                String[],
                unique(assumptions),
                true
            ))
        end
    catch
        # Continue
    end

    return examples
end

"""
Extract SeaHorn verification framework proof obligations (.c files)

`sassert(condition)` / `sea_assert(condition)` / `__VERIFIER_assert(condition)`
→ goals. `sassume(condition)` / `__VERIFIER_assume(condition)` → premises.
"""
function extract_seahorn_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Collect assume conditions as premises
    assumptions = String[]
    try
        for am in eachmatch(r"(?:sassume|__VERIFIER_assume)\s*\(([^)]+)\)", content)
            push!(assumptions, strip(am.captures[1]))
        end
    catch
        # Continue
    end

    assert_count = Ref(0)

    try
        for m in eachmatch(r"(?:sassert|sea_assert|__VERIFIER_assert)\s*\(([^)]+)\)", content)
            assert_count[] += 1
            cond = strip(m.captures[1])
            push!(examples, ProofExample(
                "SeaHorn",
                filepath,
                "assert_$(assert_count[])",
                cond,
                String[],
                unique(assumptions),
                true
            ))
        end
    catch
        # Skip malformed assertions
    end

    return examples
end

"""
Extract UPPAAL timed automata verification properties (.xml snippet files)

Uses regex-based XML extraction (no full XML parser needed). `<formula>`
elements → goals. `<location ... name="...">` name attributes → state
names collected as premises.
"""
function extract_uppaal_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Collect location names as premises
    location_names = String[]
    try
        for lm in eachmatch(r"<location[^>]*\bname\s*=\s*\"([^\"]+)\"", content)
            push!(location_names, lm.captures[1])
        end
    catch
        # Continue
    end

    formula_count = Ref(0)

    try
        # Extract <formula>...</formula> elements
        for m in eachmatch(r"<formula>\s*(.*?)\s*</formula>"s, content)
            formula_count[] += 1
            formula = strip(m.captures[1])
            push!(examples, ProofExample(
                "UPPAAL",
                filepath,
                "formula_$(formula_count[])",
                formula,
                String[],
                unique(location_names),
                true
            ))
        end
    catch
        # Skip malformed XML
    end

    # Fallback: extract property queries from non-XML .q files (plain text)
    if isempty(examples)
        try
            for m in eachmatch(r"^\s*(A\[\]|E\[\]|A<>|E<>|-->)\s*(.+)$"m, content)
                formula_count[] += 1
                formula = strip(m.captures[1] * " " * m.captures[2])
                push!(examples, ProofExample(
                    "UPPAAL",
                    filepath,
                    "query_$(formula_count[])",
                    formula,
                    String[],
                    unique(location_names),
                    true
                ))
            end
        catch
            # Continue
        end
    end

    return examples
end

"""
Extract Cameleer / Gospel annotated OCaml proofs (.ml files with Gospel specs)

`(*@ function_spec ... @*)` annotation blocks → spec text as goal.
`(*@ requires <cond> @*)` → premises. `(*@ ensures <cond> @*)` → goals.
"""
function extract_cameleer_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    try
        # Match Gospel annotation blocks (*@ ... @*)
        for m in eachmatch(r"\(\*@\s*(.*?)\s*@\*\)"s, content)
            annotation = m.captures[1]

            # Collect requires clauses as premises
            premises = String[]
            try
                for rm in eachmatch(r"requires\s+(.+?)(?=requires|ensures|variant|diverges|\z)"s, annotation)
                    push!(premises, strip(rm.captures[1]))
                end
            catch
                # Continue
            end

            # Collect ensures clauses as goals
            goals = String[]
            try
                for em in eachmatch(r"ensures\s+(.+?)(?=requires|ensures|variant|diverges|\z)"s, annotation)
                    push!(goals, strip(em.captures[1]))
                end
            catch
                # Continue
            end

            # Determine theorem name from preceding OCaml function definition
            thm_name = "gospel_spec"
            try
                # Look back in content for the nearest `let name` before this annotation
                offset = m.offset
                prefix = content[max(1, offset - 200):offset]
                fn_match = match(r"let\s+(\w+)\s*(?:[:=(\[]|$)", prefix)
                if fn_match !== nothing
                    thm_name = fn_match.captures[1]
                end
            catch
                # Continue with default name
            end

            goal_str = isempty(goals) ? strip(annotation) : join(goals, " ∧ ")
            push!(examples, ProofExample(
                "Cameleer",
                filepath,
                thm_name,
                goal_str,
                String[],
                unique(premises),
                true
            ))
        end
    catch
        # Skip malformed annotations
    end

    return examples
end

"""
Extract Mercury logic programming proofs (.m files)

`:- pred name(types) is det/semidet/nondet.` declarations → goals.
`:- mode name(in, out) is det.` → mode declarations. Predicate names
referenced in clause bodies are collected as premises.
"""
function extract_mercury_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    try
        # Match :- pred name(ArgTypes) is Determinism.
        for m in eachmatch(r":-\s*pred\s+(\w+)\s*\(([^)]*)\)\s+is\s+(\w+)\s*\.", content)
            pred_name   = m.captures[1]
            arg_types   = strip(m.captures[2])
            determinism = m.captures[3]

            # Premises: referenced predicate names in clause heads/bodies for this predicate
            premises = String[]
            try
                # Scan for calls to other predicates in clauses with matching head
                # (look for `pred_name(...) :- ... Body.` patterns)
                clause_pat = Regex("$(pred_name)\\s*\\([^)]*\\)\\s*:-\\s*(.*?)\\.", "s")
                for cm in eachmatch(clause_pat, content)
                    for pm in eachmatch(r"\b([a-z]\w*)\s*\(", cm.captures[1])
                        candidate = pm.captures[1]
                        candidate ∉ ("is", "if", "then", "else", "not") && push!(premises, candidate)
                    end
                end
            catch
                # Continue
            end

            push!(examples, ProofExample(
                "Mercury",
                filepath,
                pred_name,
                "pred $pred_name($arg_types) is $determinism",
                String[],
                unique(premises),
                true
            ))
        end
    catch
        # Skip malformed declarations
    end

    return examples
end

"""
Extract Naproche-SAD natural language proof checker proofs (.ftl, .tex files)

`Theorem name. <statement>` and `Lemma name. <statement>` → goals.
`Proof.` ... `Qed.` blocks contain proof steps. `By <lemma_name>` → premise names.
"""
function extract_naproche_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    try
        # Match Theorem/Lemma name. statement. Proof. ... Qed.
        for m in eachmatch(r"(?:Theorem|Lemma)\s+(\w+)\.\s*(.+?)\s*Proof\.(.*?)Qed\."s, content)
            thm_name   = m.captures[1]
            statement  = strip(m.captures[2])
            proof_body = m.captures[3]

            # Tactics: collect sentences in proof body as steps
            tactics = String[]
            try
                for step in split(proof_body, r"\.\s+")
                    s = strip(step)
                    isempty(s) || push!(tactics, s)
                end
            catch
                # Continue
            end

            # Premises: names cited via "By <name>" patterns
            premises = String[]
            try
                for pm in eachmatch(r"\bBy\s+(\w+)", proof_body)
                    push!(premises, pm.captures[1])
                end
                # Also catch "by <name>" (lowercase)
                for pm in eachmatch(r"\bby\s+([A-Z]\w*)", proof_body)
                    push!(premises, pm.captures[1])
                end
            catch
                # Continue
            end

            push!(examples, ProofExample(
                "Naproche",
                filepath,
                thm_name,
                statement,
                tactics,
                unique(premises),
                true
            ))
        end
    catch
        # Skip malformed blocks
    end

    return examples
end

"""
Extract OpenTheory article format proofs (.art files)

Each non-comment line is a stack machine operation. `thm` pops a proof
from the stack. Quoted strings `"name"` appearing before `thm` are
treated as theorem names. `ref "name"` references are premises.
"""
function extract_opentheory_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Collect all ref "name" references as premises
    all_refs = String[]
    try
        for rm in eachmatch(r"^ref\s+\"([^\"]+)\""m, content)
            push!(all_refs, rm.captures[1])
        end
    catch
        # Continue
    end

    thm_count = Ref(0)

    try
        # Find thm lines and work backwards for the most recent quoted name
        lines = split(content, '\n')
        last_name = Ref("")
        for line in lines
            stripped = strip(line)
            stripped == "" && continue
            startswith(stripped, '#') && continue  # comment

            # Track quoted string tokens as potential theorem names
            nm = match(r"^\"([^\"]+)\"$", stripped)
            if nm !== nothing
                last_name[] = nm.captures[1]
            end

            if stripped == "thm"
                thm_count[] += 1
                name = isempty(last_name[]) ? "thm_$(thm_count[])" : last_name[]
                push!(examples, ProofExample(
                    "OpenTheory",
                    filepath,
                    name,
                    "thm $name",
                    String[],
                    unique(all_refs),
                    true
                ))
                last_name[] = ""  # Reset after consuming
            end
        end
    catch
        # Skip malformed article
    end

    return examples
end

"""
Extract NuPRL proof development system proofs (.nuprl files)

`THEOREM name == formula` → goal. `LEMMA name == formula` → lemma premise.
`BY <tactic>` → tactic steps inside proof blocks.
"""
function extract_nuprl_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Collect lemma names as premises
    lemma_names = String[]
    try
        for lm in eachmatch(r"\bLEMMA\s+(\w+)\s*==", content)
            push!(lemma_names, lm.captures[1])
        end
    catch
        # Continue
    end

    try
        for m in eachmatch(r"\bTHEOREM\s+(\w+)\s*==\s*(.+?)(?=\bTHEOREM\b|\bLEMMA\b|\Z)"s, content)
            thm_name   = m.captures[1]
            rest       = m.captures[2]

            # The formula is everything before the first BY
            formula = rest
            tactic_block = ""
            by_idx = findfirst(r"\bBY\b", rest)
            if by_idx !== nothing
                formula      = strip(rest[1:first(by_idx)-1])
                tactic_block = rest[last(by_idx)+1:end]
            else
                formula = strip(rest)
            end

            # Collect BY tactic lines
            tactics = String[]
            try
                for tm in eachmatch(r"\bBY\s+(.+?)(?=\bBY\b|\Z)"s, tactic_block)
                    push!(tactics, strip(tm.captures[1]))
                end
            catch
                # Continue
            end

            push!(examples, ProofExample(
                "NuPRL",
                filepath,
                thm_name,
                formula,
                tactics,
                unique(lemma_names),
                true
            ))
        end
    catch
        # Skip malformed declarations
    end

    return examples
end

"""
Extract Imandra verification platform proofs (.iml files)

`theorem name : formula = ...` → goal. `instance () = verify (fun ...) [@@auto]`
→ verification target. `[@@blast]`, `[@@rewrite]`, `[@@induct]` annotations
→ tactics. `let name = ...` bindings → premises.
"""
function extract_imandra_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Collect let-binding names as premises
    let_names = String[]
    try
        for lm in eachmatch(r"\blet\s+(\w+)\s*=", content)
            push!(let_names, lm.captures[1])
        end
    catch
        # Continue
    end

    # Collect tactic annotations present in the file
    tactic_annotations = String[]
    for ann in ("@@auto", "@@blast", "@@rewrite", "@@induct")
        if occursin(ann, content)
            push!(tactic_annotations, ann)
        end
    end

    try
        # theorem name : formula = ...
        for m in eachmatch(r"\btheorem\s+(\w+)\s*:\s*(.+?)\s*=", content)
            thm_name = m.captures[1]
            formula  = strip(m.captures[2])
            push!(examples, ProofExample(
                "Imandra",
                filepath,
                thm_name,
                formula,
                tactic_annotations,
                unique(let_names),
                true
            ))
        end
    catch
        # Continue
    end

    try
        # instance () = verify (fun ...) [@@auto] style
        for m in eachmatch(r"\binstance\s*\(\s*\)\s*=\s*verify\s*\((.+?)\)\s*(?:\[@@\w+\])*"s, content)
            body = strip(m.captures[1])
            push!(examples, ProofExample(
                "Imandra",
                filepath,
                "verify_instance",
                "verify($body)",
                tactic_annotations,
                unique(let_names),
                true
            ))
        end
    catch
        # Continue
    end

    return examples
end

"""
Extract ProofPower (SML-based LCF-style) proofs

`val _ = prove_thm("name", goal_term, tac_list)` → goal. `set_goal([], term)`
→ goal term. `a tactic_name` calls → tactic steps.
"""
function extract_proofpower_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    try
        # prove_thm("name", goal_term, tac_list)
        for m in eachmatch(r"prove_thm\s*\(\s*\"([^\"]+)\"\s*,\s*([^,]+),\s*(.+?)\)"s, content)
            thm_name  = m.captures[1]
            goal_term = strip(m.captures[2])
            tac_list  = m.captures[3]

            # Extract tactic names from tac_list (identifiers ending in _TAC or known names)
            tactics = String[]
            try
                for tm in eachmatch(r"\b(\w+_TAC|REWRITE_TAC|ASM_REWRITE_TAC|INDUCT_TAC|STRIP_TAC|CONJ_TAC|EQ_TAC|ACCEPT_TAC)\b", tac_list)
                    push!(tactics, tm.captures[1])
                end
            catch
                # Continue
            end

            push!(examples, ProofExample(
                "ProofPower",
                filepath,
                thm_name,
                goal_term,
                unique(tactics),
                String[],
                true
            ))
        end
    catch
        # Skip malformed prove_thm calls
    end

    try
        # set_goal([], term)
        for m in eachmatch(r"set_goal\s*\(\s*\[\s*\]\s*,\s*(.+?)\s*\)"s, content)
            goal_term = strip(m.captures[1])

            # Collect subsequent `a tac` calls as tactics
            tactics = String[]
            try
                for tm in eachmatch(r"\ba\s+(\w+)", content[m.offset:min(m.offset+1000, lastindex(content))])
                    push!(tactics, tm.captures[1])
                end
            catch
                # Continue
            end

            push!(examples, ProofExample(
                "ProofPower",
                filepath,
                "set_goal_obligation",
                goal_term,
                unique(tactics),
                String[],
                true
            ))
        end
    catch
        # Skip malformed set_goal calls
    end

    return examples
end

"""
Extract ACL2s (ACL2 Sedan) theorem prover proofs

Extends the ACL2 extractor with additional ACL2s-specific forms:
`defthm`, `deflem`, and `(test? <form>)` patterns. Test obligations
from `test?` are emitted as goals alongside standard `defthm` theorems.
"""
function extract_acl2s_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Collect standard defthm / deflem declarations (same as ACL2)
    try
        for m in eachmatch(r"\((?:defthm|deflem)\s+([A-Za-z_][A-Za-z0-9_-]*)\s+(.*?)(?:\)|:hints)"s, content)
            theorem_name = m.captures[1]
            formula      = strip(m.captures[2])

            # Extract :hints block
            hints = String[]
            hint_block = match(r":hints\s*\((.*?)\)"s, content[m.offset:end])
            if hint_block !== nothing
                push!(hints, strip(hint_block.captures[1]))
            end

            # Premises from :use / :enable / :in-theory
            premises = String[]
            try
                hint_src = hint_block !== nothing ? hint_block.captures[1] : ""
                for um in eachmatch(r":use\s*\(?:?instance\s+([a-z][a-z0-9\-]*)", hint_src)
                    push!(premises, um.captures[1])
                end
                for em in eachmatch(r":(?:in-theory\s*\(|enable\s+)([a-z][a-z0-9\-]*)", hint_src)
                    push!(premises, em.captures[1])
                end
            catch
                # Continue
            end

            push!(examples, ProofExample(
                "ACL2s",
                filepath,
                theorem_name,
                formula,
                hints,
                unique(premises),
                true
            ))
        end
    catch
        # Skip malformed defthm/deflem
    end

    try
        # ACL2s-specific: (test? <form>) → test obligation as goal
        for m in eachmatch(r"\(test\?\s+(.*?)\)"s, content)
            test_form = strip(m.captures[1])
            push!(examples, ProofExample(
                "ACL2s",
                filepath,
                "test_obligation",
                "(test? $test_form)",
                String[],
                String[],
                true
            ))
        end
    catch
        # Skip malformed test? forms
    end

    return examples
end

"""
Extract Kissat / DIMACS CNF SAT problems

Parses DIMACS CNF format used by Kissat and other SAT solvers:
- `p cnf <nvars> <nclauses>` header → goal summarising the instance
- Clause lines (space-separated integers ending in `0`) → clause premises
- `c assert: <msg>` comment lines → named assertion premises
- No tactics (push-button SAT solving)
"""
function extract_kissat_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    goal     = ""
    premises = String[]
    clauses  = 0

    # Parse header: p cnf <nvars> <nclauses>
    try
        hm = match(r"^p\s+cnf\s+(\d+)\s+(\d+)"m, content)
        if hm !== nothing
            nvars    = hm.captures[1]
            nclauses = hm.captures[2]
            clauses  = parse(Int, nclauses)
            goal     = "cnf_satisfiability: $(nvars) vars, $(nclauses) clauses"
        end
    catch
        # Malformed header — leave goal empty
    end

    # Skip files without a CNF header
    isempty(goal) && return examples

    # Clause lines: one or more integers ending with 0
    try
        for m in eachmatch(r"^((?:-?\d+\s+)+-?\d+\s+0)\s*$"m, content)
            clause_str = strip(m.captures[1])
            # Remove trailing 0 for a cleaner premise string
            lits = join(filter(!=(0), parse.(Int, split(clause_str))), " ")
            isempty(lits) || push!(premises, lits)
        end
    catch
        # Continue
    end

    # Named assertions from `c assert: <msg>` comments
    try
        for m in eachmatch(r"^c\s+assert:\s*(.+)$"m, content)
            push!(premises, strip(m.captures[1]))
        end
    catch
        # Continue
    end

    push!(examples, ProofExample(
        "Kissat",
        filepath,
        "cnf_instance",
        goal,
        String[],          # No tactics — SAT is push-button
        unique(premises),
        true
    ))

    return examples
end

"""
Extract Athena proofs

Handles Athena natural-deduction proof scripts:
- `conclude <name> <formula>` → goal is formula, name is theorem name
- `(!claim <formula>)` → anonymous goal
- `assume <name> := <formula>` → named premise
- `by-induction` / `induct-on` → induction tactics
- `(!mp <lemma1> <lemma2>)` → premises from lemma names
"""
function extract_athena_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Collect file-level assume premises
    global_premises = String[]
    try
        for m in eachmatch(r"assume\s+(\w+)\s*:=\s*(.+?)(?:\s*\n|\s+(?:conclude|by-|induct))"s, content)
            push!(global_premises, m.captures[1])
        end
    catch
        # Continue
    end

    # Collect induction tactics present in the file
    tactics = String[]
    occursin(r"\bby-induction\b", content)  && push!(tactics, "by-induction")
    occursin(r"\binduct-on\b",    content)  && push!(tactics, "induct-on")

    # Collect (!mp lemma1 lemma2) premises
    mp_premises = String[]
    try
        for m in eachmatch(r"\(!mp\s+(\w+)\s+(\w+)\)", content)
            push!(mp_premises, m.captures[1])
            push!(mp_premises, m.captures[2])
        end
    catch
        # Continue
    end

    all_premises = unique(vcat(global_premises, mp_premises))

    # conclude <name> <formula>
    try
        for m in eachmatch(r"\bconclude\s+(\w+)\s+(.+?)(?=\n|\bconclude\b|\(\!)"s, content)
            thm_name = m.captures[1]
            formula  = strip(m.captures[2])
            push!(examples, ProofExample(
                "Athena",
                filepath,
                thm_name,
                formula,
                tactics,
                all_premises,
                true
            ))
        end
    catch
        # Continue
    end

    # Anonymous (!claim <formula>) goals
    try
        for m in eachmatch(r"\(!claim\s+(.+?)\)"s, content)
            formula = strip(m.captures[1])
            push!(examples, ProofExample(
                "Athena",
                filepath,
                "claim",
                formula,
                tactics,
                all_premises,
                true
            ))
        end
    catch
        # Continue
    end

    return examples
end

"""
Extract Frama-C / ACSL proof annotations

Parses C source files annotated with ACSL (ANSI/ISO C Specification Language):
- `/*@ requires <cond>; */` → precondition premise
- `/*@ ensures <cond>; */` → postcondition goal
- `/*@ invariant <cond>; */` → loop invariant goal
- `/*@ assigns <locs>; */` → assignment clause (informational premise)
- `/*@ lemma <name>: <formula>; */` → named lemma goal
"""
function extract_framac_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Collect requires clauses as premises
    premises = String[]
    try
        for m in eachmatch(r"/\*@\s*requires\s+([^;]+);\s*\*/"s, content)
            push!(premises, strip(m.captures[1]))
        end
    catch
        # Continue
    end

    # assigns clauses are informational premises
    try
        for m in eachmatch(r"/\*@\s*assigns\s+([^;]+);\s*\*/"s, content)
            push!(premises, "assigns: " * strip(m.captures[1]))
        end
    catch
        # Continue
    end

    all_premises = unique(premises)

    # ensures clauses → postcondition goals
    try
        for m in eachmatch(r"/\*@\s*ensures\s+([^;]+);\s*\*/"s, content)
            cond = strip(m.captures[1])
            push!(examples, ProofExample(
                "FramaC",
                filepath,
                "postcondition",
                cond,
                String[],
                all_premises,
                true
            ))
        end
    catch
        # Continue
    end

    # invariant clauses → loop invariant goals
    try
        for m in eachmatch(r"/\*@\s*invariant\s+([^;]+);\s*\*/"s, content)
            inv = strip(m.captures[1])
            push!(examples, ProofExample(
                "FramaC",
                filepath,
                "loop_invariant",
                inv,
                String[],
                all_premises,
                true
            ))
        end
    catch
        # Continue
    end

    # lemma <name>: <formula>; → named lemma goals
    try
        for m in eachmatch(r"/\*@\s*lemma\s+(\w+)\s*:\s*([^;]+);\s*\*/"s, content)
            lemma_name = m.captures[1]
            formula    = strip(m.captures[2])
            push!(examples, ProofExample(
                "FramaC",
                filepath,
                lemma_name,
                formula,
                String[],
                all_premises,
                true
            ))
        end
    catch
        # Continue
    end

    return examples
end

"""
Extract Essence Prime (.eprime) constraint-satisfaction problems

Parses Essence Prime files used by Savile Row and related CP solvers:
- `given <param>: <type>` declarations → parameter names as premises
- `find <var>: <domain>` declarations → variable names as premises
- `such that <constraint>` → constraint expressions as goals
- `maximising <expr>` / `minimising <expr>` → optimisation objective goal
"""
function extract_eprime_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # given parameter declarations → premises
    param_premises = String[]
    try
        for m in eachmatch(r"\bgiven\s+(\w+)\s*:\s*(.+?)(?=\n|\bgiven\b|\bfind\b|\bsuch\b)"s, content)
            push!(param_premises, m.captures[1])
        end
    catch
        # Continue
    end

    # find variable declarations → premises
    var_premises = String[]
    try
        for m in eachmatch(r"\bfind\s+(\w+)\s*:\s*(.+?)(?=\n|\bfind\b|\bsuch\b|\bmaxi)"s, content)
            push!(var_premises, m.captures[1])
        end
    catch
        # Continue
    end

    all_premises = unique(vcat(param_premises, var_premises))

    # such that ... blocks → constraint goals
    try
        for m in eachmatch(r"\bsuch\s+that\b\s*\n((?:[^\n]+\n?)+?)(?=\n\n|\bmaxi|\bmini|\z)"s, content)
            block = strip(m.captures[1])
            for constraint in split(block, r",\s*\n|,\s*(?=\S)")
                c = strip(constraint)
                isempty(c) && continue
                push!(examples, ProofExample(
                    "Eprime",
                    filepath,
                    "constraint",
                    c,
                    String[],
                    all_premises,
                    true
                ))
            end
        end
    catch
        # Continue
    end

    # maximising / minimising → objective goal
    try
        for m in eachmatch(r"\b(maximising|minimising)\s+(.+?)(?=\n|\z)"s, content)
            direction = m.captures[1]
            expr      = strip(m.captures[2])
            push!(examples, ProofExample(
                "Eprime",
                filepath,
                "$(direction)_objective",
                "$(direction): $(expr)",
                String[],
                all_premises,
                true
            ))
        end
    catch
        # Continue
    end

    return examples
end

"""
Extract Albatross (.al) proofs

Handles the Albatross theorem prover (an Eiffel-inspired verifier):
- `theorem <name> (args): <rettype>` declarations → goal is rettype
- `require <formula>` → precondition premise
- `ensure <formula>` → postcondition goal
- `proof` ... `end` blocks: `via <name>` → premise name; bare tactic identifiers
"""
function extract_albatross_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    try
        # theorem name (...): rettype  ...  end
        for m in eachmatch(r"\btheorem\s+(\w+)\s*(?:\([^)]*\))?\s*:\s*(.+?)\b(?:require|proof|end)"s, content)
            thm_name = m.captures[1]
            rettype  = strip(m.captures[2])

            # Find the body between the theorem header and its `end`
            body_start = m.offset + length(m.match)
            body_end   = findnext("end", content, body_start)
            body       = body_end === nothing ? "" : content[body_start:first(body_end)-1]

            # require clauses → premises
            req_premises = String[]
            try
                for rm in eachmatch(r"\brequire\s+(.+?)(?=\n|\brequire\b|\bensure\b|\bproof\b)"s, body)
                    push!(req_premises, strip(rm.captures[1]))
                end
            catch
                # Continue
            end

            # via <name> in proof block → premises
            via_premises = String[]
            try
                for vm in eachmatch(r"\bvia\s+(\w+)", body)
                    push!(via_premises, vm.captures[1])
                end
            catch
                # Continue
            end

            # bare tactic identifiers (lines with single word inside proof block)
            tactics = String[]
            try
                for line in split(body, '\n')
                    s = strip(line)
                    if !isempty(s) && match(r"^\w+$", s) !== nothing
                        push!(tactics, s)
                    end
                end
            catch
                # Continue
            end

            # ensure clauses → goals (one ProofExample per postcondition)
            ensure_goals = String[]
            try
                for em in eachmatch(r"\bensure\s+(.+?)(?=\n|\bensure\b|\bend\b)"s, body)
                    push!(ensure_goals, strip(em.captures[1]))
                end
            catch
                # Continue
            end

            all_premises = unique(vcat(req_premises, via_premises))

            if !isempty(ensure_goals)
                for g in ensure_goals
                    push!(examples, ProofExample(
                        "Albatross",
                        filepath,
                        thm_name,
                        g,
                        tactics,
                        all_premises,
                        true
                    ))
                end
            else
                push!(examples, ProofExample(
                    "Albatross",
                    filepath,
                    thm_name,
                    rettype,
                    tactics,
                    all_premises,
                    true
                ))
            end
        end
    catch
        # Skip malformed theorem blocks
    end

    return examples
end

"""
Extract generic HOL proofs (HOL Zero, ProofPower HOL)

Delegates to `extract_hol_light_proofs` — HOL Zero and ProofPower HOL share
the same LCF-style SML surface syntax as HOL Light:
- `val thm = TAC_PROOF((asl, goal), tactic_list)` → goal term
- `ASSUME_TAC thm_name` → premise name
- `REWRITE_RULE`, `CONV_RULE`, `MATCH_MP` → tactic strings

Any HOL-family pattern not matched by the HOL Light extractor is handled
generically so the caller always gets a `ProofExample[]` (never throws).
"""
function extract_hol_proofs(filepath::String, content::String)::Vector{ProofExample}
    # Delegate to the HOL Light extractor — identical syntax family
    examples = try
        extract_hol_light_proofs(filepath, content)
    catch
        ProofExample[]
    end

    # Supplement: TAC_PROOF((asl, goal), tac) form used in HOL Zero
    try
        for m in eachmatch(r"\bTAC_PROOF\s*\(\s*\(\s*\[([^\]]*)\]\s*,\s*`([^`]+)`\s*\)\s*,\s*(.+?)\)"s, content)
            asl_str  = m.captures[1]
            goal     = strip(m.captures[2])
            tac_body = m.captures[3]

            # Premises from ASSUME_TAC calls in the tactic body
            assume_premises = String[]
            try
                for am in eachmatch(r"ASSUME_TAC\s+(\w+)", tac_body)
                    push!(assume_premises, am.captures[1])
                end
            catch; end

            # Tactic names from REWRITE_RULE / CONV_RULE / MATCH_MP
            tactics = String[]
            try
                for tm in eachmatch(r"\b(REWRITE_RULE|CONV_RULE|MATCH_MP|ONCE_REWRITE_RULE)\b", tac_body)
                    push!(tactics, tm.captures[1])
                end
            catch; end

            push!(examples, ProofExample(
                "HOL",
                filepath,
                "tac_proof",
                goal,
                unique(tactics),
                unique(assume_premises),
                true
            ))
        end
    catch
        # Continue
    end

    return examples
end

"""
    extract_gpuverify_proofs(filepath, content) -> Vector{ProofExample}

Extract kernel verification goals from CUDA/OpenCL source files.

Each `__global__ void <name>` (CUDA) or `__kernel void <name>` (OpenCL)
function becomes one ProofExample goal. Pre/post conditions expressed via
`__requires` and `__ensures` annotations become premises.  `__syncthreads`
calls are collected as tactics since they are the canonical barrier primitive.

Corpus: GPUVerify testsuite and Rodinia/PolyBench-GPU CUDA benchmarks.
"""
function extract_gpuverify_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Detect dialect (CUDA vs OpenCL)
    is_cuda  = occursin("__global__", content)
    is_opencl = occursin("__kernel", content)
    prover_name = "GPUVerify"

    # Extract __requires and __ensures annotations as premises
    premises = String[]
    for m in eachmatch(r"__(requires|ensures)\s*\(([^)]+)\)", content)
        push!(premises, string(m.captures[1], "(", m.captures[2], ")"))
    end

    # Collect __syncthreads() calls as proof tactics
    tactics = String[]
    if occursin("__syncthreads()", content)
        push!(tactics, "__syncthreads()")
    end
    if occursin("barrier(CLK_LOCAL_MEM_FENCE)", content)
        push!(tactics, "barrier(CLK_LOCAL_MEM_FENCE)")
    end
    if isempty(tactics)
        push!(tactics, "auto")
    end

    # Match CUDA kernel declarations: __global__ void name(
    if is_cuda
        for m in eachmatch(r"__global__\s+void\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(", content)
            kernel_name = m.captures[1]
            push!(examples, ProofExample(
                prover_name,
                filepath,
                kernel_name,
                "race_free($kernel_name)",
                copy(tactics),
                copy(premises),
                true
            ))
        end
    end

    # Match OpenCL kernel declarations: __kernel void name(
    if is_opencl
        for m in eachmatch(r"__kernel\s+void\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(", content)
            kernel_name = m.captures[1]
            push!(examples, ProofExample(
                prover_name,
                filepath,
                kernel_name,
                "race_free($kernel_name)",
                copy(tactics),
                copy(premises),
                true
            ))
        end
    end

    # Fallback: no recognised kernel declarations found
    if isempty(examples)
        push!(examples, ProofExample(
            prover_name,
            filepath,
            "unknown_kernel",
            "race_free(unknown)",
            tactics,
            premises,
            true
        ))
    end

    return examples
end

"""
    extract_faial_proofs(filepath, content) -> Vector{ProofExample}

Extract data-race freedom goals from CUDA source files for the Faial
access-pattern analyser.

Each `__global__ void <name>` kernel becomes one ProofExample.
`__shared__` variable declarations are extracted as premises — shared
memory is the primary race surface Faial reasons about.
Synchronisation primitives (`__syncthreads`, `atomicAdd`, `atomicCAS`)
are collected as tactics.

Corpus: Faial tests/ directory and any CUDA kernel corpus.
"""
function extract_faial_proofs(filepath::String, content::String)::Vector{ProofExample}
    examples = ProofExample[]

    # Collect __shared__ declarations as premises (race surface)
    premises = String[]
    for line in split(content, '\n')
        trimmed = strip(line)
        if occursin("__shared__", trimmed)
            push!(premises, trimmed)
        end
    end

    # Collect synchronisation calls as tactics
    tactics = String[]
    if occursin("__syncthreads()", content)
        push!(tactics, "__syncthreads()")
    end
    for m in eachmatch(r"(atomicAdd|atomicCAS|atomicExch)\s*\(", content)
        push!(tactics, string(m.captures[1]))
    end
    if isempty(tactics)
        push!(tactics, "auto")
    end
    tactics = unique(tactics)

    # Match CUDA __global__ kernel declarations
    for m in eachmatch(r"__global__\s+void\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(", content)
        kernel_name = m.captures[1]
        push!(examples, ProofExample(
            "Faial",
            filepath,
            kernel_name,
            "data_race_free($kernel_name)",
            copy(tactics),
            copy(premises),
            true
        ))
    end

    # Fallback
    if isempty(examples)
        push!(examples, ProofExample(
            "Faial",
            filepath,
            "unknown_kernel",
            "data_race_free(unknown)",
            tactics,
            premises,
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
