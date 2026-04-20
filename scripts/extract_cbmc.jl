#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract CBMC bounded-model-check problems from diffblue/cbmc regression tests.
# Vendor: git clone https://github.com/diffblue/cbmc external_corpora/cbmc
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/cbmc/regression"; const OUT = "training_data"; const START_ID = 2_100_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    if !isdir(DIR); println("CBMC regression not found: $DIR"); println("Clone: git clone https://github.com/diffblue/cbmc external_corpora/cbmc"); return ps, ts, pm; end
    c_files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs; endswith(f, ".c") && push!(c_files, joinpath(root, f)); end; end
    println("Found $(length(c_files)) regression .c files")
    # CBMC assertions: __CPROVER_assert(cond, "msg");
    pat = r"__CPROVER_assert\s*\(\s*(.+?)\s*,\s*\"([^\"]*)\""s
    for f in c_files
        try
            c = read(f, String)
            for m in eachmatch(pat, c)
                push!(ps, Dict{String,Any}("id"=>id, "prover"=>"CBMC",
                    "source_file"=>relpath(f, DIR),
                    "theorem"=>strip(m.captures[2]), "goal"=>strip(m.captures[1]), "context"=>Any[]))
                id += 1
            end
        catch e; println("Warning: $f: $e"); end
    end
    ps, ts, pm
end
function main(); println("ECHIDNA CBMC Extraction"); println("=" ^ 23)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No assertions extracted.") : save_common(ps, ts, pm, "cbmc", START_ID, OUT) end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
