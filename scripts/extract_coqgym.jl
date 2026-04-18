#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
#
# Extract proofs from the CoqGym corpus and convert to ECHIDNA training
# format.
#
# Historical note (2026-04-18): the previous version of this extractor
# had three compounding bugs that capped output at 14 records despite a
# 235 MB CoqGym corpus on disk:
#
#   1. `first(v_files, 100)` hard-coded cap — CoqGym ships ~ 40 K .v
#      files, so we were sampling 0.25 % of the input.
#   2. Proof-end regex was `Q\.` — Coq proofs terminate with `Qed.`,
#      `Defined.`, `Admitted.`, or `Abort.`, not `Q.`.
#   3. Theorem pattern matched only `Theorem` — Coq has a dozen
#      equivalent introduction forms (`Lemma`, `Proposition`,
#      `Corollary`, `Fact`, `Remark`, `Example`, `Instance`,
#      `Definition`, `Fixpoint`, `CoFixpoint`).
#
# All three are fixed below. See echidna#13 for the audit trail.

using JSON3

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

const COQGYM_DIR = "external_corpora/CoqGym"
const OUTPUT_DIR = "training_data"
const PROOF_STATES_FILE = joinpath(OUTPUT_DIR, "proof_states_coqgym.jsonl")
const TACTICS_FILE = joinpath(OUTPUT_DIR, "tactics_coqgym.jsonl")
const PREMISES_FILE = joinpath(OUTPUT_DIR, "premises_coqgym.jsonl")
const STATS_FILE = joinpath(OUTPUT_DIR, "stats_coqgym.json")

# Start ID after existing Metamath band (Metamath ends at 47165 + original
# CoqGym reservation 108 = 47273 → CoqGym starts at 47274). Kept stable so
# downstream merge tools don't need to be taught new bands.
const START_ID = 47274

# Coq theorem-introduction forms. Any of these followed by a name and a
# `:` starts a statement that ends at the next top-level `.` and is
# followed by a proof block (unless it's a Definition with `:=`, which
# we detect separately).
const THEOREM_KEYWORDS = [
    "Theorem", "Lemma", "Proposition", "Corollary", "Fact",
    "Remark", "Example", "Instance",
]

# Proof terminators. A proof block runs from `Proof.` to one of these.
const PROOF_TERMINATORS_PAT =
    r"\b(?:Qed|Defined|Admitted|Abort|Save)\s*\."

# Tactic-ish tokens for Coq: identifiers at semicolon / period / bullet
# boundaries. Kept permissive; downstream training can re-filter.
const COQ_TACTIC_PAT = r"(?:^|[.;|\-\+\*])\s*([a-zA-Z_][a-zA-Z0-9_']{0,60})"

# ---------------------------------------------------------------------------
# Parsing
# ---------------------------------------------------------------------------

"""
    strip_coq_comments(text) -> String

Remove Coq comments `(* ... *)` with proper nesting support.
"""
function strip_coq_comments(text::AbstractString)::String
    out = IOBuffer()
    depth = 0
    i = firstindex(text)
    lastidx = lastindex(text)
    while i <= lastidx
        if depth == 0 && i < lastidx && text[i] == '(' && text[nextind(text, i)] == '*'
            depth = 1
            i = nextind(text, nextind(text, i))
        elseif depth > 0 && i < lastidx && text[i] == '(' && text[nextind(text, i)] == '*'
            depth += 1
            i = nextind(text, nextind(text, i))
        elseif depth > 0 && i < lastidx && text[i] == '*' && text[nextind(text, i)] == ')'
            depth -= 1
            i = nextind(text, nextind(text, i))
        elseif depth == 0
            print(out, text[i])
            i = nextind(text, i)
        else
            i = nextind(text, i)
        end
    end
    return String(take!(out))
end

"""
    find_statement_end(text, start) -> Int

Return the index of the `.` that terminates a Coq statement starting at
`start`, skipping dots inside (), [], {}, and string literals. Returns
`0` if no terminator is found.
"""
function find_statement_end(text::AbstractString, start::Int)::Int
    depth_paren = 0
    depth_brack = 0
    depth_brace = 0
    in_string = false
    i = start
    lastidx = lastindex(text)
    while i <= lastidx
        ch = text[i]
        if in_string
            if ch == '"'
                in_string = false
            end
        elseif ch == '"'
            in_string = true
        elseif ch == '('
            depth_paren += 1
        elseif ch == ')'
            depth_paren -= 1
        elseif ch == '['
            depth_brack += 1
        elseif ch == ']'
            depth_brack -= 1
        elseif ch == '{'
            depth_brace += 1
        elseif ch == '}'
            depth_brace -= 1
        elseif ch == '.' && depth_paren == 0 && depth_brack == 0 && depth_brace == 0
            # Must be followed by whitespace or end-of-file to count as a
            # statement terminator (avoids module-path dots like
            # `List.length`).
            if i == lastidx || isspace(text[nextind(text, i)])
                return i
            end
        end
        i = nextind(text, i)
    end
    return 0
end

"""
    extract_tactics(proof_body) -> Vector{String}

Pull plausible tactic names out of a proof body. Deduplicated,
order-preserving, capped at 60 entries.
"""
function extract_tactics(proof_body::AbstractString)::Vector{String}
    seen = Set{String}()
    ordered = String[]
    for m in eachmatch(COQ_TACTIC_PAT, proof_body)
        t = String(m.captures[1])
        # Skip obvious non-tactics — capitalised idents are almost always
        # constructor names / module aliases, not tactics.
        isempty(t) && continue
        startswith(t, r"[A-Z]") && continue
        t == "Proof" && continue
        t == "Qed" && continue
        t == "Defined" && continue
        t == "Admitted" && continue
        t == "Abort" && continue
        if t ∉ seen
            push!(seen, t)
            push!(ordered, t)
            length(ordered) >= 60 && break
        end
    end
    return ordered
end

"""
    parse_coq_file(filepath) -> Tuple{Vector,Vector,Vector}

Parse a single Coq source file and return (theorems, tactic-rows,
premise-rows). `theorems` carries the inner data without IDs — IDs are
assigned after all files are processed.
"""
function parse_coq_file(filepath::String)
    content = try
        read(filepath, String)
    catch
        return Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]
    end
    cleaned = strip_coq_comments(content)

    theorems = Dict{String,Any}[]
    tactics = Dict{String,Any}[]
    premises = Dict{String,Any}[]

    keyword_alt = join(THEOREM_KEYWORDS, "|")
    # Match `<keyword> <name>` at the start of a statement. We capture
    # the name, then scan forward for the statement terminator and proof
    # body manually.
    intro_pat = Regex("\\b($(keyword_alt))\\s+([A-Za-z_][A-Za-z0-9_']*)")

    source_rel = replace(filepath, COQGYM_DIR => "CoqGym")

    for m in eachmatch(intro_pat, cleaned)
        stmt_start = m.offset + length(m.match)
        # Require a `:` before the statement end to distinguish theorem
        # introductions from `Definition name := ...` style.
        colon_idx = findnext(':', cleaned, stmt_start)
        stmt_end = find_statement_end(cleaned, stmt_start)
        if stmt_end == 0 || colon_idx === nothing || colon_idx > stmt_end
            continue
        end
        name = String(m.captures[2])
        goal = strip(cleaned[colon_idx+1 : stmt_end-1])
        goal = replace(goal, r"\s+" => " ")

        # Look for `Proof.` shortly after the statement and capture the
        # proof body up to the next terminator.
        proof_anchor = findnext("Proof.", cleaned, nextind(cleaned, stmt_end))
        proof_body = ""
        if proof_anchor !== nothing && proof_anchor.start - stmt_end < 200
            body_start = last(proof_anchor) + 1
            term_m = match(PROOF_TERMINATORS_PAT, cleaned, body_start)
            if term_m !== nothing
                proof_body = cleaned[body_start : term_m.offset - 1]
            end
        end

        push!(theorems, Dict{String,Any}(
            "theorem" => name,
            "goal" => first(goal, 4000),
            "proof_body" => first(strip(proof_body), 8000),
            "source" => source_rel,
        ))

        if !isempty(proof_body)
            tactic_list = extract_tactics(proof_body)
            for (step, t) in enumerate(tactic_list)
                push!(tactics, Dict{String,Any}(
                    "proof_index" => length(theorems),
                    "step" => step,
                    "tactic" => t,
                    "prover" => "Coq",
                ))
            end
            # Premises: names mentioned in `intros a b c.` or
            # `intro h.` patterns.
            for hm in eachmatch(r"\bintros?\s+([A-Za-z_][A-Za-z0-9_'\s]*?)\.", proof_body)
                for name2 in split(strip(hm.captures[1]))
                    push!(premises, Dict{String,Any}(
                        "proof_index" => length(theorems),
                        "premise" => String(name2),
                        "prover" => "Coq",
                        "theorem" => name,
                    ))
                end
            end
        end
    end

    return theorems, tactics, premises
end

# ---------------------------------------------------------------------------
# Pipeline
# ---------------------------------------------------------------------------

function extract_coqgym_proofs()
    # Widening (2026-04-18): walk CoqGym + sibling Coq-family corpora.
    # Each sibling is a separate repository root that also ships .v
    # files — CompCert (verified C compiler), bedrock2 (verified
    # low-level code), hott-coq (homotopy type theory Coq book).
    roots = String[]
    base = joinpath(COQGYM_DIR, "coq_projects")
    isdir(base) && push!(roots, base)
    for sibling in ("CompCert", "bedrock2", "hott-coq",
                    "mathcomp-analysis", "interaction-trees",
                    "category-theory")
        p = joinpath(dirname(COQGYM_DIR), sibling)
        isdir(p) && push!(roots, p)
    end
    if isempty(roots)
        println("CoqGym + Coq-family corpora not found")
        return Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]
    end

    v_files = String[]
    for root in roots
        for (rr, _dirs, files) in walkdir(root)
            for f in files
                endswith(f, ".v") && push!(v_files, joinpath(rr, f))
            end
        end
    end
    println("Found $(length(v_files)) .v files across $(length(roots)) Coq-family root(s)")

    all_theorems = Dict{String,Any}[]
    all_tactics = Dict{String,Any}[]
    all_premises = Dict{String,Any}[]

    processed = 0
    for vf in v_files
        thms, tacs, prems = try
            parse_coq_file(vf)
        catch e
            Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]
        end
        # Re-key tactics/premises onto the global theorem ID we will
        # assign below.
        base_offset = length(all_theorems)
        for t in tacs
            t["proof_index"] = base_offset + t["proof_index"]
        end
        for p in prems
            p["proof_index"] = base_offset + p["proof_index"]
        end
        append!(all_theorems, thms)
        append!(all_tactics, tacs)
        append!(all_premises, prems)
        processed += 1
        if processed % 2000 == 0
            println("  processed $(processed)/$(length(v_files)) files — running theorem count: $(length(all_theorems))")
        end
    end

    # Assign stable IDs now that we have the full ordering.
    current_id = START_ID
    proof_states = Dict{String,Any}[]
    id_for_index = Dict{Int,Int}()
    for (idx, thm) in enumerate(all_theorems)
        id_for_index[idx] = current_id
        push!(proof_states, Dict{String,Any}(
            "id" => current_id,
            "prover" => "Coq",
            "theorem" => thm["theorem"],
            "goal" => thm["goal"],
            "context" => Any[],
            "proof_body" => thm["proof_body"],
            "source" => thm["source"],
        ))
        current_id += 1
    end
    # Rewrite proof_index → proof_id in tactics / premises.
    tactics = Dict{String,Any}[]
    for t in all_tactics
        push!(tactics, Dict{String,Any}(
            "proof_id" => id_for_index[t["proof_index"]],
            "step" => t["step"],
            "tactic" => t["tactic"],
            "prover" => "Coq",
        ))
    end
    premises = Dict{String,Any}[]
    for p in all_premises
        push!(premises, Dict{String,Any}(
            "proof_id" => id_for_index[p["proof_index"]],
            "premise" => p["premise"],
            "prover" => "Coq",
            "theorem" => p["theorem"],
        ))
    end

    return proof_states, tactics, premises
end

function save_extracted_data(proof_states::Vector, tactics::Vector, premises::Vector)
    mkpath(OUTPUT_DIR)

    open(PROOF_STATES_FILE, "w") do f
        for state in proof_states
            println(f, JSON3.write(state))
        end
    end
    open(TACTICS_FILE, "w") do f
        for t in tactics
            println(f, JSON3.write(t))
        end
    end
    open(PREMISES_FILE, "w") do f
        for p in premises
            println(f, JSON3.write(p))
        end
    end

    stats = Dict{String,Any}(
        "source" => "CoqGym",
        "extraction_date" => string(now()),
        "proof_states_count" => length(proof_states),
        "tactics_count" => length(tactics),
        "premises_count" => length(premises),
        "start_id" => START_ID,
        "end_id" => isempty(proof_states) ? START_ID : START_ID + length(proof_states) - 1,
    )
    open(STATS_FILE, "w") do f
        JSON3.pretty(f, stats)
    end

    println("Saved $(length(proof_states)) proof states -> $(PROOF_STATES_FILE)")
    println("Saved $(length(tactics)) tactics       -> $(TACTICS_FILE)")
    println("Saved $(length(premises)) premises     -> $(PREMISES_FILE)")
    println("Saved stats                 -> $(STATS_FILE)")
end

using Dates

function main()
    println("ECHIDNA CoqGym Extraction (rewritten 2026-04-18)")
    println("=" ^ 50)

    proof_states, tactics, premises = extract_coqgym_proofs()

    if isempty(proof_states)
        println("No proofs extracted from CoqGym")
        return
    end

    save_extracted_data(proof_states, tactics, premises)

    println()
    println("Extraction Summary:")
    println("  Proofs:    $(length(proof_states))")
    println("  Tactics:   $(length(tactics))")
    println("  Premises:  $(length(premises))")
    println("  ID Range:  $(START_ID) – $(START_ID + length(proof_states) - 1)")
end

if abspath(PROGRAM_FILE) == abspath(@__FILE__)
    main()
end
