#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract proofs / declarations / .ath files from Athena.
# Vendor location: external_corpora/athena/
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/athena"
const OUT = "training_data"
const START_ID = 3_500_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    if !isdir(DIR); println("Athena corpus not found: $DIR"); println("Vendor source into $DIR and rerun."); return ps, ts, pm; end
    files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs; endswith(f, ".ath") && push!(files, joinpath(root, f)); end; end
    println("Found $(length(files)) .ath files")
    pat = r"define\s+([A-Za-z0-9_]+)\s*:=\s*\((.*?)\)"s
    for f in files
        try
            c = read(f, String)
            for m in eachmatch(pat, c)
                n = length(m.captures) >= 1 ? strip(String(m.captures[1])) : ""
                g = length(m.captures) >= 2 ? strip(String(m.captures[2])) : ""
                if !isempty(n)
                    push!(ps, Dict{String,Any}("id"=>id, "prover"=>"athena",
                        "source_file"=>relpath(f, DIR), "theorem"=>n, "goal"=>g, "context"=>Any[]))
                    id += 1
                end
            end
        catch e; println("Warning: $f: $e"); end
    end
    ps, ts, pm
end
function main()
    println("ECHIDNA Athena Extraction"); println("=" ^ 40)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No records extracted.") : save_common(ps, ts, pm, "athena", START_ID, OUT)
end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
