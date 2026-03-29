#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
#
# TPTP Problem Library extractor for ECHIDNA training data.
# Reads .p files from the TPTP library and extracts proof states
# for first-order ATP backends: Vampire, E Prover, SPASS.
#
# Input:  external_corpora/tptp/ (TPTP problem files)
# Output: training_data/proof_states_tptp.jsonl
#         training_data/tactics_tptp.jsonl
#         training_data/stats_tptp.json

using JSON3
using Dates

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

# ID range for TPTP-sourced proof states
const ID_BASE = 70000

# Map TPTP domain prefixes to the most natural ATP prover.
# We round-robin across all three to keep the corpus balanced.
const PROVERS = ["Vampire", "EProver", "SPASS"]

# TPTP status values that indicate a provable theorem
const PROVABLE_STATUSES = Set([
    "Theorem", "Unsatisfiable", "ContradictoryAxioms",
    "CounterSatisfiable", "Satisfiable",
])

# ---------------------------------------------------------------------------
# Parser helpers
# ---------------------------------------------------------------------------

"""
    strip_tptp_comments(text::String) -> String

Remove TPTP block comments (/% ... %/) and line comments (% ...).
"""
function strip_tptp_comments(text::String)::String
    # Block comments first
    text = replace(text, r"/%.*?%/"s => "")
    # Line comments
    text = replace(text, r"%[^\n]*" => "")
    return text
end

"""
    parse_tptp_file(filepath::String) -> Union{Dict, Nothing}

Parse a single .p TPTP problem file.

Returns a Dict with:
    name        - problem name (from filename)
    status      - SZS status annotation if present
    domain      - TPTP domain code (e.g. 'AGT', 'ALG')
    conjecture  - the conjecture formula (string) or nothing
    axioms      - list of axiom formula strings
    includes    - list of include directives
"""
function parse_tptp_file(filepath::String)
    name = splitext(basename(filepath))[1]
    domain_match = match(r"^([A-Z]+)", name)
    domain = domain_match !== nothing ? domain_match.captures[1] : "UNK"

    local raw::String
    try
        raw = read(filepath, String)
    catch
        return nothing
    end

    # Extract SZS status from header comments
    status_match_result = match(r"%\s*Status\s*:\s*(\w+)", raw)
    status = status_match_result !== nothing ? status_match_result.captures[1] : "Unknown"

    cleaned = strip_tptp_comments(raw)

    # Parse formulae: fof(...), cnf(...), tff(...), thf(...)
    formula_pat = r"(fof|cnf|tff|thf)\s*\(\s*([^,]+)\s*,\s*(\w+)\s*,\s*(.*?)\s*\)\s*\."s

    conjecture = nothing
    axioms = String[]
    includes = [m.captures[1] for m in eachmatch(r"include\(\s*'([^']+)'\s*\)", cleaned)]

    for m in eachmatch(Regex(formula_pat, "s"), cleaned)
        _lang, _fname, role, body = m.captures
        role = strip(lowercase(role))
        body = join(split(body), ' ')  # normalise whitespace

        if role == "conjecture"
            conjecture = body
        elseif role in ("axiom", "hypothesis", "lemma", "definition",
                        "assumption", "type", "plain")
            push!(axioms, body)
        end
    end

    return Dict(
        "name" => name,
        "status" => status,
        "domain" => domain,
        "conjecture" => conjecture,
        "axioms" => axioms,
        "includes" => includes,
    )
end

# ---------------------------------------------------------------------------
# Extraction pipeline
# ---------------------------------------------------------------------------

"""
    find_tptp_files(base_dir::String) -> Vector{String}

Recursively find all .p files under base_dir.
"""
function find_tptp_files(base_dir::String)::Vector{String}
    results = String[]
    for (root, _dirs, files) in walkdir(base_dir)
        for fname in files
            if endswith(fname, ".p")
                push!(results, joinpath(root, fname))
            end
        end
    end
    sort!(results)
    return results
end

"""
    extract_all(base_dir::String) -> Tuple

Extract training data from the TPTP corpus.
Returns (proof_states, tactics, stats_dict).
"""
function extract_all(base_dir::String)
    files = find_tptp_files(base_dir)
    println("Found $(length(files)) .p files in $base_dir")

    proof_states = Dict{String, Any}[]
    tactics = Dict{String, Any}[]
    prover_counts = Dict(p => 0 for p in PROVERS)
    skipped = 0
    errors = 0

    for (idx, fpath) in enumerate(files)
        parsed = parse_tptp_file(fpath)
        if parsed === nothing
            errors += 1
            continue
        end

        # We want problems that have a conjecture (something to prove)
        if parsed["conjecture"] === nothing
            skipped += 1
            continue
        end

        record_id = ID_BASE + length(proof_states)

        # Round-robin prover assignment for balanced corpus
        prover = PROVERS[(length(proof_states) % length(PROVERS)) + 1]

        # Build context from axioms (limit to first 20 to keep size sane)
        context = parsed["axioms"][1:min(20, length(parsed["axioms"]))]

        state = Dict{String, Any}(
            "id" => record_id,
            "prover" => prover,
            "theorem" => parsed["name"],
            "goal" => parsed["conjecture"],
            "context" => context,
            "source" => "TPTP",
            "status" => parsed["status"],
            "domain" => parsed["domain"],
            "proof_steps" => length(parsed["axioms"]),
        )
        push!(proof_states, state)
        prover_counts[prover] += 1

        # Tactic record: for ATP the "tactic" is running the solver
        tactic = Dict{String, Any}(
            "proof_id" => record_id,
            "step" => 1,
            "tactic" => "atp_solve_$(lowercase(prover))",
            "prover" => prover,
            "proof_text" => "% TPTP $(parsed["status"]) via $prover",
        )
        push!(tactics, tactic)

        # Progress indicator every 5000 files
        if idx % 5000 == 0
            println("  processed $idx/$(length(files)) files ...")
        end
    end

    id_range = isempty(proof_states) ? "none" : "$(ID_BASE)-$(ID_BASE + length(proof_states) - 1)"

    stats = Dict{String, Any}(
        "version" => "v2.0-tptp",
        "extraction_date" => Dates.format(now(), dateformat"yyyy-mm-ddTHH:MM:SS"),
        "total_files_scanned" => length(files),
        "total_proofs" => length(proof_states),
        "total_tactics" => length(tactics),
        "skipped_no_conjecture" => skipped,
        "read_errors" => errors,
        "prover_distribution" => prover_counts,
        "source" => "TPTP Problem Library",
        "id_range" => id_range,
    )

    return proof_states, tactics, stats
end

"""
    save_results(proof_states, tactics, stats; output_dir="training_data")

Write extraction results to JSONL / JSON files.
"""
function save_results(proof_states, tactics, stats; output_dir::String="training_data")
    mkpath(output_dir)

    open(joinpath(output_dir, "proof_states_tptp.jsonl"), "w") do fh
        for rec in proof_states
            println(fh, JSON3.write(rec))
        end
    end

    open(joinpath(output_dir, "tactics_tptp.jsonl"), "w") do fh
        for rec in tactics
            println(fh, JSON3.write(rec))
        end
    end

    open(joinpath(output_dir, "stats_tptp.json"), "w") do fh
        write(fh, JSON3.write(stats; allow_inf=true))
    end

    println("\nSaved $(length(proof_states)) proof states -> $output_dir/proof_states_tptp.jsonl")
    println("Saved $(length(tactics)) tactics        -> $output_dir/tactics_tptp.jsonl")
    println("Saved stats                        -> $output_dir/stats_tptp.json")
end

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

function main()::Int
    println("=" ^ 60)
    println("ECHIDNA TPTP Extractor")
    println("Covers: Vampire, E Prover, SPASS")
    println("=" ^ 60)

    base_dir = "external_corpora/tptp"
    if !isdir(base_dir)
        println("ERROR: Corpus directory not found: $base_dir")
        println("Download TPTP first (see CORPUS_EXPANSION_PLAN.md).")
        return 1
    end

    proof_states, tactics, stats = extract_all(base_dir)

    if isempty(proof_states)
        println("\nWARNING: No proof states extracted. Check corpus contents.")
        return 1
    end

    save_results(proof_states, tactics, stats)

    println("\nProver distribution:")
    for (prover, count) in stats["prover_distribution"]
        println("  $(rpad(prover, 12)): $count")
    end

    println("\nTotal: $(stats["total_proofs"]) proof states (ID range $(stats["id_range"]))")
    return 0
end

if abspath(PROGRAM_FILE) == @__FILE__
    exit(main())
end
