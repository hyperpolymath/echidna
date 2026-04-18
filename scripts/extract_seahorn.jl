#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract SeaHorn LLVM-based verification problems (CHC-encoded).
# Vendor: git clone https://github.com/seahorn/seahorn external_corpora/seahorn
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/seahorn"; const OUT = "training_data"; const START_ID = 2_200_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    if !isdir(DIR); println("SeaHorn not found: $DIR"); println("Clone: git clone https://github.com/seahorn/seahorn external_corpora/seahorn"); return ps, ts, pm; end
    c_files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs; (endswith(f, ".c") || endswith(f, ".ll")) && push!(c_files, joinpath(root, f)); end; end
    println("Found $(length(c_files)) SeaHorn input files")
    pat = r"(sassert|assume|verifier_error|__VERIFIER_assert)\s*\(\s*(.+?)\s*\)"s
    for f in c_files
        try
            c = read(f, String)
            for m in eachmatch(pat, c)
                push!(ps, Dict{String,Any}("id"=>id, "prover"=>"SeaHorn",
                    "source_file"=>relpath(f, DIR),
                    "theorem"=>"$(m.captures[1])_$(id)", "goal"=>strip(m.captures[2]),
                    "annotation_kind"=>m.captures[1], "context"=>Any[]))
                id += 1
            end
        catch e; println("Warning: $f: $e"); end
    end
    ps, ts, pm
end
function main(); println("ECHIDNA SeaHorn Extraction"); println("=" ^ 26)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No assertions extracted.") : save_common(ps, ts, pm, "seahorn", START_ID, OUT) end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
