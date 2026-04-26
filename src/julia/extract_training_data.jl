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
