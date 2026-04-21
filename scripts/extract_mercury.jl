#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract proofs / declarations / Mercury .m files from Mercury.
# Vendor location: external_corpora/mercury/
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/mercury"
# 2026-04-18 (echidna#12 100K push): also walk sibling mercury-lang
# clone (mercury-language/mercury — the full Mercury distribution,
# ~4 100 .m files of stdlib + runtime + compiler modules).
const EXTRA_DIRS = [
    "external_corpora/mercury-lang",
]
const OUT = "training_data"
const START_ID = 3_700_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    roots = String[]
    isdir(DIR) && push!(roots, DIR)
    for d in EXTRA_DIRS
        isdir(d) && push!(roots, d)
    end
    if isempty(roots); println("Mercury corpus not found: $DIR"); println("Vendor source into $DIR and rerun."); return ps, ts, pm; end
    files = String[]
    for root_dir in roots
        for (root, _, fs) in walkdir(root_dir); for f in fs; endswith(f, ".m") && push!(files, joinpath(root, f)); end; end
    end
    println("Found $(length(files)) .m files")
    pat = r":-\s*pred\s+([a-zA-Z0-9_]+)\((.*?)\)"s
    for f in files
        try
            c = read(f, String)
            for m in eachmatch(pat, c)
                n = length(m.captures) >= 1 ? strip(String(m.captures[1])) : ""
                g = length(m.captures) >= 2 ? strip(String(m.captures[2])) : ""
                if !isempty(n)
                    push!(ps, Dict{String,Any}("id"=>id, "prover"=>"mercury",
                        "source_file"=>relpath(f, DIR), "theorem"=>n, "goal"=>g, "context"=>Any[]))
                    # Emit premises: type names in predicate signature
                    for hm in eachmatch(r"\b([a-zA-Z_][a-zA-Z0-9_]{1,40})\b", g)
                        h = strip(hm.captures[1])
                        !isempty(h) && length(h) < 50 && push!(pm, Dict{String,Any}(
                            "proof_id"=>id, "premise"=>h,
                            "prover"=>"mercury", "theorem"=>n, "source"=>"mercury"))
                    end
                    id += 1
                end
            end
        catch e; println("Warning: $f: $e"); end
    end
    ps, ts, pm
end
function main()
    println("ECHIDNA Mercury Extraction"); println("=" ^ 40)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No records extracted.") : save_common(ps, ts, pm, "mercury", START_ID, OUT)
end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
