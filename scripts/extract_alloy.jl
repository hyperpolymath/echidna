#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract Alloy relational-model-finder constraints from alloytools examples.
# Vendor: git clone https://github.com/AlloyTools/models external_corpora/alloy
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/alloy"; const OUT = "training_data"; const START_ID = 2_700_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    if !isdir(DIR); println("Alloy not found: $DIR"); println("Clone: git clone https://github.com/AlloyTools/models external_corpora/alloy"); return ps, ts, pm; end
    als_files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs; endswith(f, ".als") && push!(als_files, joinpath(root, f)); end; end
    println("Found $(length(als_files)) .als files")
    # Alloy: assert NAME { FORMULA }   or   check NAME for K
    pat = r"assert\s+([A-Za-z0-9_]+)\s*\{([^}]+)\}"s
    for f in als_files
        try
            c = read(f, String)
            for m in eachmatch(pat, c)
                push!(ps, Dict{String,Any}("id"=>id, "prover"=>"Alloy",
                    "source_file"=>relpath(f, DIR),
                    "theorem"=>strip(m.captures[1]), "goal"=>strip(m.captures[2]),
                    "context"=>Any[]))
                id += 1
            end
        catch e; println("Warning: $f: $e"); end
    end
    ps, ts, pm
end
function main(); println("ECHIDNA Alloy Extraction"); println("=" ^ 24)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No assertions extracted.") : save_common(ps, ts, pm, "alloy", START_ID, OUT) end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
