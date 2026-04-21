#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# Extract verification conditions from Boogie .bpl files.
# Vendor: https://github.com/boogie-org/boogie Test/ directory + any
# Dafny-generated .bpl dumps, any VCC / Chalice test suites.

using JSON3, Dates

const BOOGIE_DIR = "external_corpora/boogie"
const OUTPUT_DIR = "training_data"
const PROOF_STATES_FILE = joinpath(OUTPUT_DIR, "proof_states_boogie.jsonl")
const TACTICS_FILE = joinpath(OUTPUT_DIR, "tactics_boogie.jsonl")
const PREMISES_FILE = joinpath(OUTPUT_DIR, "premises_boogie.jsonl")
const STATS_FILE = joinpath(OUTPUT_DIR, "stats_boogie.json")
const START_ID = 1_100_000

function extract_boogie_programs()
    proof_states = Dict{String,Any}[]; tactics = Dict{String,Any}[]; premises = Dict{String,Any}[]
    current_id = START_ID

    if !isdir(BOOGIE_DIR)
        println("Boogie corpus not found: $BOOGIE_DIR")
        println("Clone: git clone https://github.com/boogie-org/boogie $BOOGIE_DIR")
        return proof_states, tactics, premises
    end

    bpl_files = String[]
    for (root, _, files) in walkdir(BOOGIE_DIR)
        for f in files
            endswith(f, ".bpl") && push!(bpl_files, joinpath(root, f))
        end
    end
    println("Found $(length(bpl_files)) Boogie .bpl files")

    # Widening (2026-04-18): previous extractor only matched
    # `procedure`, leaving implementations, functions, axioms,
    # constants and type declarations on the floor. Boogie files
    # typically carry 3-5× more of those than of `procedure`
    # declarations, so the gate was the main limiter.
    #
    # Attributes like `{:extern}` or `{:inline 1}` may precede the
    # name in all forms.
    attr = "(?:\\{:[^}]*\\}\\s*)*"
    proc_pattern = Regex(
        "procedure\\s+$(attr)([a-zA-Z0-9_.]+)\\s*" *
        "\\([^)]*\\)\\s*(?:returns\\s*\\([^)]*\\))?\\s*(.*?)(?:\\{|;)", "s")
    impl_pattern = Regex(
        "implementation\\s+$(attr)([a-zA-Z0-9_.]+)\\s*" *
        "\\([^)]*\\)\\s*(?:returns\\s*\\([^)]*\\))?\\s*(.*?)\\{", "s")
    func_pattern = Regex(
        "function\\s+$(attr)([a-zA-Z0-9_.]+)\\s*" *
        "\\([^)]*\\)\\s*(?:returns\\s*\\([^)]*\\))?\\s*(.*?)(?:\\{|;)", "s")
    axiom_pattern = r"axiom\s+(?:\{:[^}]*\}\s*)*(.*?);"s
    const_pattern = r"const\s+(?:unique\s+)?(?:\{:[^}]*\}\s*)*([a-zA-Z0-9_.]+)\s*:\s*([^;]+);"
    type_pattern = r"type\s+(?:\{:[^}]*\}\s*)*([a-zA-Z0-9_.]+)\s*(?:<[^>]*>\s*)?(?:=([^;]+))?;"

    # Boogie premise patterns: requires/ensures/modifies + called procedure names
    boogie_hyp_patterns = [
        r"\brequires\s+([a-zA-Z][a-zA-Z0-9_.]*)\b",
        r"\bensures\s+([a-zA-Z][a-zA-Z0-9_.]*)\b",
        r"\binvariant\s+([a-zA-Z][a-zA-Z0-9_.]*)\b",
        r"\bcall\s+([a-zA-Z][a-zA-Z0-9_.]*)\b",
    ]

    for f in bpl_files
        content = try
            read(f, String)
        catch
            continue
        end
        rel = relpath(f, BOOGIE_DIR)
        # Each regex wrapped in try/catch so a pathological file
        # skips that pattern rather than aborting the whole run.
        matches = try
            collect(eachmatch(proc_pattern, content))
        catch; Any[] end
        for m in matches
            name = strip(m.captures[1])
            contract = first(strip(m.captures[2]), 2000)
            isempty(name) && continue
            push!(proof_states, Dict{String,Any}(
                "id" => current_id, "prover" => "Boogie",
                "kind" => "procedure",
                "source_file" => rel,
                "theorem" => name, "goal" => contract,
                "context" => Any[]))
            for hyp_pattern in boogie_hyp_patterns
                for hm in eachmatch(hyp_pattern, contract)
                    h = strip(hm.captures[1])
                    !isempty(h) && length(h) < 50 && push!(premises, Dict{String,Any}(
                        "proof_id"=>current_id, "premise"=>h,
                        "prover"=>"Boogie", "theorem"=>name, "source"=>"boogie"))
                end
            end
            current_id += 1
        end
        matches = try
            collect(eachmatch(impl_pattern, content))
        catch; Any[] end
        for m in matches
            name = strip(m.captures[1])
            body_head = first(strip(m.captures[2]), 2000)
            isempty(name) && continue
            push!(proof_states, Dict{String,Any}(
                "id" => current_id, "prover" => "Boogie",
                "kind" => "implementation",
                "source_file" => rel,
                "theorem" => name, "goal" => body_head,
                "context" => Any[]))
            current_id += 1
        end
        matches = try
            collect(eachmatch(func_pattern, content))
        catch; Any[] end
        for m in matches
            name = strip(m.captures[1])
            sig = first(strip(m.captures[2]), 2000)
            isempty(name) && continue
            push!(proof_states, Dict{String,Any}(
                "id" => current_id, "prover" => "Boogie",
                "kind" => "function",
                "source_file" => rel,
                "theorem" => name, "goal" => sig,
                "context" => Any[]))
            current_id += 1
        end
        matches = try
            collect(eachmatch(axiom_pattern, content))
        catch; Any[] end
        for (i, m) in enumerate(matches)
            body = first(strip(m.captures[1]), 2000)
            isempty(body) && continue
            push!(proof_states, Dict{String,Any}(
                "id" => current_id, "prover" => "Boogie",
                "kind" => "axiom",
                "source_file" => rel,
                "theorem" => "axiom_$(i)", "goal" => body,
                "context" => Any[]))
            current_id += 1
        end
        matches = try
            collect(eachmatch(const_pattern, content))
        catch; Any[] end
        for m in matches
            name = strip(m.captures[1])
            ty = first(strip(m.captures[2]), 400)
            isempty(name) && continue
            push!(proof_states, Dict{String,Any}(
                "id" => current_id, "prover" => "Boogie",
                "kind" => "const",
                "source_file" => rel,
                "theorem" => name, "goal" => ty,
                "context" => Any[]))
            current_id += 1
        end
        matches = try
            collect(eachmatch(type_pattern, content))
        catch; Any[] end
        for m in matches
            name = strip(m.captures[1])
            rhs_raw = m.captures[2] === nothing ? "" : strip(m.captures[2])
            isempty(name) && continue
            push!(proof_states, Dict{String,Any}(
                "id" => current_id, "prover" => "Boogie",
                "kind" => "type",
                "source_file" => rel,
                "theorem" => name,
                "goal" => isempty(rhs_raw) ? "type $(name)" : first(rhs_raw, 400),
                "context" => Any[]))
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
        "source" => "boogie-org/boogie Test/", "prover" => "Boogie",
        "extraction_date" => string(Dates.today()),
        "proof_states_count" => length(ps), "tactics_count" => length(ts),
        "premises_count" => length(pm), "start_id" => START_ID,
        "end_id" => isempty(ps) ? START_ID : START_ID + length(ps) - 1)
    open(STATS_FILE, "w") do f; JSON3.pretty(f, stats); end
    println("Saved $(length(ps)) proof states")
end

function main()
    println("ECHIDNA Boogie (intermediate verification language) Extraction")
    println("=" ^ 60)
    ps, ts, pm = extract_boogie_programs()
    isempty(ps) ? println("No programs extracted.") : save_extracted_data(ps, ts, pm)
end

if abspath(PROGRAM_FILE) == @__FILE__; main(); end
