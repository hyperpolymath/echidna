#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract proofs / declarations / ForTheL files from Naproche (ForTheL).
# Vendor location: external_corpora/naproche/
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/naproche"
const OUT = "training_data"
const START_ID = 3_200_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    if !isdir(DIR); println("Naproche (ForTheL) corpus not found: $DIR"); println("Vendor source into $DIR and rerun."); return ps, ts, pm; end
    files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs; endswith(f, ".ftl") && push!(files, joinpath(root, f)); end; end
    println("Found $(length(files)) .ftl files")
    pat = r"theorem\s+([A-Za-z0-9_]+)\s*:\s*([^.]+)\."s
    for f in files
        try
            c = read(f, String)
            for m in eachmatch(pat, c)
                n = length(m.captures) >= 1 ? strip(String(m.captures[1])) : ""
                g = length(m.captures) >= 2 ? strip(String(m.captures[2])) : ""
                if !isempty(n)
                    push!(ps, Dict{String,Any}("id"=>id, "prover"=>"naproche",
                        "source_file"=>relpath(f, DIR), "theorem"=>n, "goal"=>g, "context"=>Any[]))
                    id += 1
                end
            end
        catch e; println("Warning: $f: $e"); end
    end
    ps, ts, pm
end
function main()
    println("ECHIDNA Naproche (ForTheL) Extraction"); println("=" ^ 40)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No records extracted.") : save_common(ps, ts, pm, "naproche", START_ID, OUT)
end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
