#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# Extract theorem packages from OpenTheory (https://opentheory.gilith.com/).
#
# OpenTheory is a package format for higher-order logic proofs that is
# cross-prover aligned: every package maps to encodings in HOL Light,
# HOL4, ProofPower, and Isabelle/HOL. That makes it the single highest-
# ROI corpus for triangulation work — records come out of the box with
# alignment edges to four separate prover backends.
#
# Upstream: git clone https://github.com/gilith/opentheory
# Expected path: external_corpora/opentheory/data/theories/
#   .thy  — package metadata (name, version, imports, exports)
#   .art  — theory articles (stack-based proof commands)
#
# Output:
#   training_data/proof_states_opentheory.jsonl
#   training_data/stats_opentheory.json
#
# ID range: 2_500_000+

using JSON3
using Dates

const REPO_ROOT = dirname(dirname(abspath(@__FILE__)))
const OT_ROOT = joinpath(REPO_ROOT, "external_corpora", "opentheory")
const OT_THEORIES = joinpath(OT_ROOT, "data", "theories")
const OUTPUT_DIR = joinpath(REPO_ROOT, "training_data")
const OUTPUT_FILE = joinpath(OUTPUT_DIR, "proof_states_opentheory.jsonl")
const PREMISES_FILE = joinpath(OUTPUT_DIR, "premises_opentheory.jsonl")
const STATS_FILE = joinpath(OUTPUT_DIR, "stats_opentheory.json")
const START_ID = 2_500_000

# The four HOL-family provers OpenTheory targets. Each record is
# tagged with all four under `triangulated_with` so downstream
# alignment tools don't have to re-derive them.
const ALIGNED_PROVERS = ["HOLLight", "HOL4", "Isabelle", "ProofPower"]

# ---------------------------------------------------------------------------
# Theory-package metadata parser (.thy)
# ---------------------------------------------------------------------------

"""
    parse_thy_package(path) -> Dict{String,Any}

Parse an OpenTheory `.thy` package-metadata file and return the
key/value pairs. Values are whitespace-normalised strings; a key
appearing multiple times is accumulated as a vector.
"""
function parse_thy_package(path::AbstractString)::Dict{String,Any}
    meta = Dict{String,Any}()
    content = try
        read(path, String)
    catch
        return meta
    end
    for line in eachline(IOBuffer(content))
        stripped = strip(line)
        isempty(stripped) && continue
        startswith(stripped, "#") && continue
        colon_idx = findfirst(':', stripped)
        colon_idx === nothing && continue
        key = strip(stripped[1:colon_idx-1])
        value = strip(stripped[colon_idx+1:end])
        if haskey(meta, key)
            if meta[key] isa Vector
                push!(meta[key], value)
            else
                meta[key] = Any[meta[key], value]
            end
        else
            meta[key] = value
        end
    end
    return meta
end

# ---------------------------------------------------------------------------
# Article parser (.art)
# ---------------------------------------------------------------------------

"""
    extract_thm_contexts(path) -> Vector{Dict{String,Any}}

Walk an `.art` file and emit one record per `thm` command.
OpenTheory articles are stack-based: commands appear on their own
line. `thm` is the command that commits a theorem to the article's
export list. The three most-recent string literals on the stack at
the point of `thm` typically carry the theorem's name and a hint of
its shape — we harvest them as lightweight training context.
"""
function extract_thm_contexts(path::AbstractString, package::String)::Vector{Dict{String,Any}}
    out = Dict{String,Any}[]
    lines = try
        readlines(path)
    catch
        return out
    end

    # Walk forward; maintain the last few string-literal tokens seen.
    recent_strings = String[]
    idx_in_file = 0
    for raw in lines
        line = strip(raw)
        isempty(line) && continue
        # String literal — push onto recent-strings window.
        if startswith(line, "\"") && endswith(line, "\"")
            push!(recent_strings, line[2:end-1])
            length(recent_strings) > 6 && popfirst!(recent_strings)
            continue
        end
        # Commit point.
        if line == "thm"
            idx_in_file += 1
            # Name heuristic: the longest recent string-literal that
            # looks like a dotted identifier (e.g. `Data.List.length`)
            # or a camel-case/snake identifier.
            name = ""
            goal_hint = ""
            for s in reverse(recent_strings)
                if occursin(r"^[A-Za-z][A-Za-z0-9_'.]*$", s)
                    name = s
                    break
                end
            end
            for s in reverse(recent_strings)
                if !isempty(s) && s != name && length(s) > length(goal_hint)
                    goal_hint = s
                end
            end
            isempty(name) && (name = "$(package)_thm_$(idx_in_file)")
            push!(out, Dict{String,Any}(
                "theorem" => name,
                "goal"    => goal_hint,
                "package" => package,
                "article_index" => idx_in_file,
                "context" => copy(recent_strings),
                "source"  => "opentheory/$(package)/$(basename(path))",
            ))
        end
    end
    return out
end

# ---------------------------------------------------------------------------
# Pipeline
# ---------------------------------------------------------------------------

function run_extract()
    if !isdir(OT_THEORIES)
        println("[OpenTheory] Theories not found at $(OT_THEORIES)")
        println("[OpenTheory] Clone: git clone https://github.com/gilith/opentheory external_corpora/opentheory")
        return Dict{String,Any}[], Dict{String,Any}[]
    end

    # Package-level records (one per .thy).
    packages = Dict{String,Dict{String,Any}}()
    for (root, _dirs, files) in walkdir(OT_THEORIES)
        for f in files
            endswith(f, ".thy") || continue
            name = splitext(f)[1]
            meta = parse_thy_package(joinpath(root, f))
            meta["__path"] = relpath(joinpath(root, f), OT_ROOT)
            packages[name] = meta
        end
    end
    println("[OpenTheory] Found $(length(packages)) .thy packages")

    # Article-level records (one per `thm` command per .art).
    theorem_records = Dict{String,Any}[]
    for (root, _dirs, files) in walkdir(OT_THEORIES)
        for f in files
            endswith(f, ".art") || continue
            # Derive the package name from the containing directory.
            pkg = basename(root)
            append!(theorem_records,
                extract_thm_contexts(joinpath(root, f), pkg))
        end
    end
    println("[OpenTheory] Found $(length(theorem_records)) thm-commands across articles")

    return collect(values(packages)), theorem_records
end

function save_results(packages::Vector, theorems::Vector)
    mkpath(OUTPUT_DIR)

    # Write proof states. Each theorem is emitted once with the four
    # aligned HOL-family provers listed — downstream VeriSim will
    # materialise per-prover alignment edges from this.
    current_id = START_ID
    premises_records = Dict{String,Any}[]
    open(OUTPUT_FILE, "w") do fh
        for pkg in packages
            name = get(pkg, "name", "unknown")
            desc = get(pkg, "description", "")
            rec = Dict{String,Any}(
                "id" => current_id,
                "prover" => "OpenTheory",
                "kind" => "package",
                "theorem" => name,
                "goal" => desc,
                "context" => Any[],
                "package_metadata" => pkg,
                "triangulated_with" => ALIGNED_PROVERS,
                "source" => get(pkg, "__path", "opentheory/unknown.thy"),
            )
            println(fh, JSON3.write(rec))
            # Emit premises: dotted name components from package name
            for part in split(name, '.')
                h = strip(part)
                !isempty(h) && length(h) < 50 && push!(premises_records, Dict{String,Any}(
                    "proof_id"=>current_id, "premise"=>h,
                    "prover"=>"OpenTheory", "theorem"=>name, "source"=>"opentheory"))
            end
            current_id += 1
        end
        for thm in theorems
            rec = Dict{String,Any}(
                "id" => current_id,
                "prover" => "OpenTheory",
                "kind" => "theorem",
                "theorem" => thm["theorem"],
                "goal" => thm["goal"],
                "context" => thm["context"],
                "package" => thm["package"],
                "article_index" => thm["article_index"],
                "triangulated_with" => ALIGNED_PROVERS,
                "source" => thm["source"],
            )
            println(fh, JSON3.write(rec))
            # Emit premises: identifiers from theorem name and goal hint
            for text in (thm["theorem"], thm["goal"])
                for hm in eachmatch(r"\b([A-Za-z][A-Za-z0-9_'.]{1,40})\b", text)
                    h = strip(hm.captures[1])
                    !isempty(h) && length(h) < 50 && push!(premises_records, Dict{String,Any}(
                        "proof_id"=>current_id, "premise"=>h,
                        "prover"=>"OpenTheory", "theorem"=>thm["theorem"], "source"=>"opentheory"))
                end
            end
            current_id += 1
        end
    end
    open(PREMISES_FILE, "w") do fh
        for p in premises_records; println(fh, JSON3.write(p)); end
    end

    stats = Dict{String,Any}(
        "prover"              => "OpenTheory",
        "extraction_date"     => string(Dates.today()),
        "proof_states_count"  => length(packages) + length(theorems),
        "package_count"       => length(packages),
        "theorem_count"       => length(theorems),
        "triangulated_with"   => ALIGNED_PROVERS,
        "triangulation_value" => "Pre-aligned across 4 HOL-family backends — no alignment inference required",
        "start_id"            => START_ID,
        "end_id"              => current_id - 1,
        "source"              => "gilith/opentheory data/theories/",
    )
    open(STATS_FILE, "w") do fh
        JSON3.pretty(fh, stats)
    end

    println("[OpenTheory] Saved $(length(packages)) package + $(length(theorems)) theorem records")
    println("[OpenTheory] -> $(OUTPUT_FILE)")
end

function main()
    println("ECHIDNA OpenTheory Extraction")
    println("=" ^ 40)
    packages, theorems = run_extract()
    if isempty(packages) && isempty(theorems)
        println("[OpenTheory] Nothing extracted.")
        return
    end
    save_results(packages, theorems)
end

if abspath(PROGRAM_FILE) == abspath(@__FILE__)
    main()
end
