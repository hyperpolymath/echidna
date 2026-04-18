#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract proofs / declarations / .ard files from Arend.
# Vendor location: external_corpora/arend/
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/arend"
const OUT = "training_data"
const START_ID = 3_400_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    if !isdir(DIR); println("Arend corpus not found: $DIR"); println("Vendor source into $DIR and rerun."); return ps, ts, pm; end
    files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs; endswith(f, ".ard") && push!(files, joinpath(root, f)); end; end
    println("Found $(length(files)) .ard files")
    pat = r"\\func\s+([A-Za-z0-9_-]+)\s*(.*?)\s*=>"s
    for f in files
        try
            c = read(f, String)
            for m in eachmatch(pat, c)
                n = length(m.captures) >= 1 ? strip(String(m.captures[1])) : ""
                g = length(m.captures) >= 2 ? strip(String(m.captures[2])) : ""
                if !isempty(n)
                    push!(ps, Dict{String,Any}("id"=>id, "prover"=>"arend",
                        "source_file"=>relpath(f, DIR), "theorem"=>n, "goal"=>g, "context"=>Any[]))
                    id += 1
                end
            end
        catch e; println("Warning: $f: $e"); end
    end
    ps, ts, pm
end
function main()
    println("ECHIDNA Arend Extraction"); println("=" ^ 40)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No records extracted.") : save_common(ps, ts, pm, "arend", START_ID, OUT)
end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
