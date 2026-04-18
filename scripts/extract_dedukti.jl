#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# Extract proofs from Dedukti / Lambdapi corpora. Dedukti is the universal
# λΠ-modulo translation target — translated proofs from Coq, HOL Light,
# Matita, HOL4, Agda all land here. That makes it the most structurally
# diverse corpus available: a single module can hold proofs originating
# from several upstream systems.
#
# Vendor sources (any subset):
#   - https://github.com/Deducteam/Libraries (cross-prover encoded libraries)
#   - https://github.com/Deducteam/lambdapi examples
#   - https://github.com/Deducteam/personoj (Matita encoding)
#
# Expected layout: external_corpora/dedukti/{library}/*.dk

using JSON3, Dates

const DEDUKTI_DIR = "external_corpora/dedukti"
const OUTPUT_DIR = "training_data"
const PROOF_STATES_FILE = joinpath(OUTPUT_DIR, "proof_states_dedukti.jsonl")
const TACTICS_FILE = joinpath(OUTPUT_DIR, "tactics_dedukti.jsonl")
const PREMISES_FILE = joinpath(OUTPUT_DIR, "premises_dedukti.jsonl")
const STATS_FILE = joinpath(OUTPUT_DIR, "stats_dedukti.json")
const START_ID = 700_000

function extract_dedukti_proofs()
    proof_states = Dict{String,Any}[]
    tactics = Dict{String,Any}[]
    premises = Dict{String,Any}[]
    current_id = START_ID

    if !isdir(DEDUKTI_DIR)
        println("Dedukti corpus directory not found: $DEDUKTI_DIR")
        println("Clone any of:")
        println("  git clone https://github.com/Deducteam/Libraries $DEDUKTI_DIR")
        println("  git clone https://github.com/Deducteam/lambdapi $DEDUKTI_DIR/lambdapi")
        return proof_states, tactics, premises
    end

    dk_files = String[]
    for (root, _, files) in walkdir(DEDUKTI_DIR)
        for f in files
            (endswith(f, ".dk") || endswith(f, ".lp")) && push!(dk_files, joinpath(root, f))
        end
    end
    println("Found $(length(dk_files)) Dedukti/Lambdapi files")

    # Dedukti declarations: `NAME : TYPE.` or `def NAME : TYPE := TERM.`
    # Lambdapi: `symbol NAME : TYPE;` / `theorem NAME : TYPE begin … end;`
    #
    # Widening (2026-04-18): original only matched def|symbol|theorem.
    # Actual Dedukti/Lambdapi vocabulary is richer:
    #   - constant : prop-constant declarations
    #   - injective : injective symbol declarations
    #   - opaque : opaque symbol declarations
    #   - rule : rewrite-rule declarations
    #   - definition : alternative of def
    #   - inductive : inductive-type declarations
    # Also accept plain `NAME : TYPE.` (without leading keyword) which
    # is the base Dedukti form for any well-typed constant.
    kw_decl_pattern = r"(?:def|definition|symbol|theorem|constant|injective|opaque|inductive)(?:\s+(?:\{[^}]*\}|\[[^\]]*\]))?\s+([a-zA-Z0-9_.']+)\s*:\s*(.*?)\s*(?::=|\bbegin\b|;|\.)"s
    # Plain declaration at top level: name followed by `:` then type
    # then `.` or `;` terminator. Requires it to be on its own line.
    plain_decl_pattern = r"(?:^|\n)\s*([a-zA-Z_][a-zA-Z0-9_.']*)\s*:\s*((?:(?!:=).)*?)\.(?=\s|\z)"s
    rule_pattern = r"rule\s+(.+?)\s*-->\s*(.+?)\s*(?:;|\.)"s
    require_pattern = r"require\s+([a-zA-Z0-9_.]+)"

    for f in dk_files
        content = try
            read(f, String)
        catch
            continue
        end
        rel = relpath(f, DEDUKTI_DIR)
        # Each pattern wrapped in try/catch — Dedukti files can be
        # huge (translated HOL/Coq libraries) and some regexes may
        # catastrophically backtrack.
        matches = try
            collect(eachmatch(require_pattern, content))
        catch; Any[] end
        for m in matches
            push!(premises, Dict{String,Any}(
                "source_file" => rel,
                "requires" => m.captures[1],
                "prover" => "Dedukti",
            ))
        end
        matches = try
            collect(eachmatch(kw_decl_pattern, content))
        catch; Any[] end
        seen_names = Set{String}()
        for m in matches
            name = strip(m.captures[1])
            type_ = first(strip(m.captures[2]), 1500)
            if !isempty(name) && !isempty(type_) && name ∉ seen_names
                push!(seen_names, name)
                push!(proof_states, Dict{String,Any}(
                    "id" => current_id,
                    "prover" => "Dedukti",
                    "source_file" => rel,
                    "theorem" => name,
                    "goal" => type_,
                    "context" => Any[],
                ))
                current_id += 1
            end
        end
        matches = try
            collect(eachmatch(plain_decl_pattern, content))
        catch; Any[] end
        for m in matches
            name = strip(m.captures[1])
            type_ = first(strip(m.captures[2]), 1500)
            # Skip obvious false positives — short type-like keywords
            # that are themselves Dedukti syntax, and names we already
            # captured with the keyword form.
            name in ("Type", "def", "symbol", "theorem", "rule",
                     "require", "open", "begin", "end") && continue
            if !isempty(name) && !isempty(type_) && name ∉ seen_names
                push!(seen_names, name)
                push!(proof_states, Dict{String,Any}(
                    "id" => current_id,
                    "prover" => "Dedukti",
                    "source_file" => rel,
                    "theorem" => name,
                    "goal" => type_,
                    "context" => Any[],
                ))
                current_id += 1
            end
        end
        matches = try
            collect(eachmatch(rule_pattern, content))
        catch; Any[] end
        for (i, m) in enumerate(matches)
            lhs = first(strip(m.captures[1]), 600)
            rhs = first(strip(m.captures[2]), 600)
            (isempty(lhs) || isempty(rhs)) && continue
            push!(proof_states, Dict{String,Any}(
                "id" => current_id,
                "prover" => "Dedukti",
                "source_file" => rel,
                "theorem" => "rule_$(i)",
                "goal" => "$(lhs) --> $(rhs)",
                "kind" => "rewrite_rule",
                "context" => Any[],
            ))
            current_id += 1
        end
    end
    return proof_states, tactics, premises
end

function save_extracted_data(ps, ts, pm)
    mkpath(OUTPUT_DIR)
    open(PROOF_STATES_FILE, "w") do f; for s in ps; println(f, JSON3.write(s)); end; end
    open(TACTICS_FILE, "w") do f; for t in ts; println(f, JSON3.write(t)); end; end
    open(PREMISES_FILE, "w") do f; for p in pm; println(f, JSON3.write(p)); end; end
    stats = Dict{String,Any}(
        "source" => "Deducteam/Libraries + lambdapi examples",
        "prover" => "Dedukti", "extraction_date" => string(Dates.today()),
        "proof_states_count" => length(ps), "tactics_count" => length(ts),
        "premises_count" => length(pm), "start_id" => START_ID,
        "end_id" => isempty(ps) ? START_ID : START_ID + length(ps) - 1)
    open(STATS_FILE, "w") do f; JSON3.pretty(f, stats); end
    println("Saved $(length(ps)) proof states, $(length(ts)) tactics, $(length(pm)) premises")
end

function main()
    println("ECHIDNA Dedukti (λΠ-modulo) Extraction"); println("=" ^ 40)
    ps, ts, pm = extract_dedukti_proofs()
    isempty(ps) ? println("No proofs extracted.") : save_extracted_data(ps, ts, pm)
end

if abspath(PROGRAM_FILE) == @__FILE__; main(); end
