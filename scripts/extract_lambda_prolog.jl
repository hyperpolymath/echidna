#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract proofs / declarations / λProlog .mod files from λProlog.
# Vendor location: external_corpora/lambda_prolog/
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/lambda_prolog"
const OUT = "training_data"
const START_ID = 3_600_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    if !isdir(DIR); println("λProlog corpus not found: $DIR"); println("Vendor source into $DIR and rerun."); return ps, ts, pm; end
    files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs; endswith(f, ".mod") && push!(files, joinpath(root, f)); end; end
    println("Found $(length(files)) .mod files")
    pat = r"([a-zA-Z0-9_]+)\s+([^.:]*?)\s*:-"s
    for f in files
        try
            c = read(f, String)
            for m in eachmatch(pat, c)
                n = length(m.captures) >= 1 ? strip(String(m.captures[1])) : ""
                g = length(m.captures) >= 2 ? strip(String(m.captures[2])) : ""
                if !isempty(n)
                    push!(ps, Dict{String,Any}("id"=>id, "prover"=>"lambda_prolog",
                        "source_file"=>relpath(f, DIR), "theorem"=>n, "goal"=>g, "context"=>Any[]))
                    id += 1
                end
            end
        catch e; println("Warning: $f: $e"); end
    end
    ps, ts, pm
end
function main()
    println("ECHIDNA λProlog Extraction"); println("=" ^ 40)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No records extracted.") : save_common(ps, ts, pm, "lambda_prolog", START_ID, OUT)
end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
