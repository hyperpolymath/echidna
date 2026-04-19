#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract proofs / declarations / Isabelle .thy with nitpick calls from Nitpick (refutation finder).
# Vendor location: external_corpora/nitpick/
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/nitpick"
const OUT = "training_data"
const START_ID = 3_800_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    # Widening (2026-04-18): Nitpick is an Isabelle sub-tool — its
    # natural corpus is the body of Isabelle theories that actually
    # call `nitpick`. Walk external_corpora/afp/ (the Archive of
    # Formal Proofs) in addition to the dedicated Nitpick dir.
    roots = String[]
    isdir(DIR) && push!(roots, DIR)
    afp_root = joinpath(dirname(DIR), "afp")
    isdir(afp_root) && push!(roots, afp_root)
    if isempty(roots)
        println("No Nitpick-bearing corpus found.")
        println("Vendor external_corpora/afp (recommended) or external_corpora/nitpick.")
        return ps, ts, pm
    end

    files = String[]
    for root in roots
        for (rr, _, fs) in walkdir(root)
            for f in fs
                endswith(f, ".thy") && push!(files, joinpath(rr, f))
            end
        end
    end
    println("Found $(length(files)) .thy files across $(length(roots)) root(s)")

    # Widen invocation patterns: nitpick [opts], nitpick, nitpick_params,
    # refute, refute_params. Also capture the goal via the preceding
    # `lemma NAME:` or `theorem NAME:` declaration when present.
    call_pat = r"(nitpick|nitpick_params|refute|refute_params)(?:\s*\[([^\]]*)\])?"s
    lemma_before_pat = r"(?:lemma|theorem|corollary)\s+([A-Za-z0-9_']+)\s*(?:\[[^\]]*\])?\s*:\s*(?:\"([^\"]*)\"|\`([^\`]*)\`)"s

    for f in files
        c = try
            read(f, String)
        catch
            continue
        end
        rel = relpath(f, dirname(DIR))

        # Collect lemma starts with offsets.
        lemma_locs = Tuple{Int,String,String}[]
        lemma_matches = try collect(eachmatch(lemma_before_pat, c)) catch; Any[] end
        for lm in lemma_matches
            name = strip(String(lm.captures[1]))
            body_raw = lm.captures[2] !== nothing ? String(lm.captures[2]) :
                       lm.captures[3] !== nothing ? String(lm.captures[3]) : ""
            push!(lemma_locs, (lm.offset, name, body_raw))
        end
        sort!(lemma_locs, by = x -> x[1])

        matches = try collect(eachmatch(call_pat, c)) catch; Any[] end
        for (i, m) in enumerate(matches)
            kind = strip(String(m.captures[1]))
            opts = m.captures[2] === nothing ? "" : strip(String(m.captures[2]))
            # Find nearest preceding lemma for context.
            lemma_name = ""
            lemma_body = ""
            for (off, name, body) in lemma_locs
                off < m.offset || break
                lemma_name = name; lemma_body = body
            end
            theorem = isempty(lemma_name) ? "$(kind)_$(i)" : "$(lemma_name)_$(kind)"
            push!(ps, Dict{String,Any}("id"=>id, "prover"=>"nitpick",
                "source_file"=>rel, "theorem"=>theorem,
                "goal"=>first(lemma_body, 600),
                "opts"=>opts, "kind"=>kind, "context"=>Any[]))
            id += 1
        end
    end
    ps, ts, pm
end
function main()
    println("ECHIDNA Nitpick (refutation finder) Extraction"); println("=" ^ 40)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No records extracted.") : save_common(ps, ts, pm, "nitpick", START_ID, OUT)
end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
