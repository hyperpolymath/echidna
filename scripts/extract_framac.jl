#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract Frama-C / ACSL proof obligations from the Frama-C tests + WP tutorials.
# Vendor: git clone https://git.frama-c.com/pub/frama-c external_corpora/frama-c
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/frama-c"; const OUT = "training_data"; const START_ID = 1_500_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    if !isdir(DIR); println("Frama-C not found: $DIR"); println("Clone: git clone https://git.frama-c.com/pub/frama-c $DIR"); return ps, ts, pm; end
    c_files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs; endswith(f, ".c") && push!(c_files, joinpath(root, f)); end; end
    println("Found $(length(c_files)) .c files")
    # ACSL: /*@ requires/ensures/assigns … */  or  //@ requires …
    acsl_pat = r"(?:/\*@|//@)\s*(requires|ensures|assigns|behavior|assert|loop invariant)\s+([^;*]+?)(?:;|\*/)"s
    for f in c_files
        try
            c = read(f, String)
            for m in eachmatch(acsl_pat, c)
                push!(ps, Dict{String,Any}("id"=>id, "prover"=>"FramaC",
                    "source_file"=>relpath(f, DIR),
                    "theorem"=>"$(m.captures[1])_$(id)", "goal"=>strip(m.captures[2]),
                    "annotation_kind"=>m.captures[1], "context"=>Any[]))
                id += 1
            end
        catch e; println("Warning: $f: $e"); end
    end
    ps, ts, pm
end
function main(); println("ECHIDNA Frama-C Extraction"); println("=" ^ 26)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No annotations extracted.") : save_common(ps, ts, pm, "framac", START_ID, OUT) end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
