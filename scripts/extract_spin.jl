#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract SPIN model-checker LTL properties from Promela models.
# Vendor: http://spinroot.com/spin/Examples or nimble-code/Spin
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/spin"; const OUT = "training_data"; const START_ID = 2_000_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    if !isdir(DIR); println("SPIN examples not found: $DIR"); println("Clone: git clone https://github.com/nimble-code/Spin $DIR"); return ps, ts, pm; end
    pml_files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs; endswith(f, ".pml") && push!(pml_files, joinpath(root, f)); end; end
    println("Found $(length(pml_files)) .pml files")
    # ltl NAME { FORMULA } or #define P (...)
    ltl_pat = r"ltl\s+([A-Za-z0-9_]+)\s*\{\s*(.*?)\s*\}"s
    for f in pml_files
        try
            c = read(f, String)
            for m in eachmatch(ltl_pat, c)
                push!(ps, Dict{String,Any}("id"=>id, "prover"=>"SPIN",
                    "source_file"=>relpath(f, DIR), "theorem"=>strip(m.captures[1]),
                    "goal"=>strip(m.captures[2]), "context"=>Any[]))
                id += 1
            end
        catch e; println("Warning: $f: $e"); end
    end
    ps, ts, pm
end
function main(); println("ECHIDNA SPIN Extraction"); println("=" ^ 23)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No LTL properties extracted.") : save_common(ps, ts, pm, "spin", START_ID, OUT) end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
