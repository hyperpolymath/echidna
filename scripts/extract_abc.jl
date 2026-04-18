#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract ABC hardware-verification problems (AIGER / BLIF).
# Vendor: git clone https://github.com/berkeley-abc/abc external_corpora/abc
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/abc"; const OUT = "training_data"; const START_ID = 3_100_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    if !isdir(DIR); println("ABC not found: $DIR"); println("Clone: git clone https://github.com/berkeley-abc/abc $DIR"); return ps, ts, pm; end
    hw_files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs; (endswith(f, ".aig") || endswith(f, ".aag") || endswith(f, ".blif")) && push!(hw_files, joinpath(root, f)); end; end
    println("Found $(length(hw_files)) hardware files")
    # For binary .aig we record metadata only; .aag (ASCII) can be summarised.
    for f in hw_files
        try
            size = filesize(f)
            push!(ps, Dict{String,Any}("id"=>id, "prover"=>"ABC",
                "source_file"=>relpath(f, DIR),
                "theorem"=>basename(f),
                "goal"=>"$(splitext(f)[2][2:end])_circuit size=$size",
                "context"=>Any[]))
            id += 1
        catch e; println("Warning: $f: $e"); end
    end
    ps, ts, pm
end
function main(); println("ECHIDNA ABC Extraction"); println("=" ^ 22)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No circuits extracted.") : save_common(ps, ts, pm, "abc", START_ID, OUT) end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
