#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract PRISM probabilistic model-checker properties.
# Vendor: git clone https://github.com/prismmodelchecker/prism-examples external_corpora/prism
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/prism"; const OUT = "training_data"; const START_ID = 2_800_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    if !isdir(DIR); println("PRISM examples not found: $DIR"); println("Clone: git clone https://github.com/prismmodelchecker/prism-examples $DIR"); return ps, ts, pm; end
    pctl_files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs; (endswith(f, ".pctl") || endswith(f, ".props") || endswith(f, ".csl")) && push!(pctl_files, joinpath(root, f)); end; end
    println("Found $(length(pctl_files)) PRISM property files")
    # PRISM: P=? [ FORMULA ]  or  S=? [ FORMULA ]   or   "name": FORMULA
    pat = r"(P|S|R|Pmax|Pmin)\s*(?:=\?|>=\s*[0-9.]+|<=\s*[0-9.]+)\s*\[\s*(.+?)\s*\]"s
    for f in pctl_files
        try
            c = read(f, String)
            for m in eachmatch(pat, c)
                push!(ps, Dict{String,Any}("id"=>id, "prover"=>"Prism",
                    "source_file"=>relpath(f, DIR),
                    "theorem"=>"prob_$(id)", "goal"=>strip(m.captures[2]),
                    "operator"=>m.captures[1], "context"=>Any[]))
                id += 1
            end
        catch e; println("Warning: $f: $e"); end
    end
    ps, ts, pm
end
function main(); println("ECHIDNA PRISM Extraction"); println("=" ^ 24)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No properties extracted.") : save_common(ps, ts, pm, "prism", START_ID, OUT) end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
