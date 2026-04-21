#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract dReal delta-complete SMT-LIB problems (NRA / nonlinear real arithmetic).
# Vendor: git clone https://github.com/dreal/dreal4 external_corpora/dreal4
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/dreal4"; const OUT = "training_data"; const START_ID = 3_000_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    if !isdir(DIR); println("dReal not found: $DIR"); println("Clone: git clone https://github.com/dreal/dreal4 $DIR"); return ps, ts, pm; end
    smt_files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs; (endswith(f, ".smt2") || endswith(f, ".dr")) && push!(smt_files, joinpath(root, f)); end; end
    println("Found $(length(smt_files)) dReal input files")
    # SMT-LIB assertion extraction (reused pattern from extract_smtlib.jl)
    pat = r"\(assert\s+(.+?)\)\s*\n"s
    for f in smt_files
        try
            c = read(f, String)
            for m in eachmatch(pat, c)
                push!(ps, Dict{String,Any}("id"=>id, "prover"=>"DReal",
                    "source_file"=>relpath(f, DIR),
                    "theorem"=>"dreal_$(id)", "goal"=>strip(m.captures[1]),
                    "context"=>Any[]))
                # Emit premises: SMT-LIB identifiers from assertion body
                for hm in eachmatch(r"\b([a-zA-Z_][a-zA-Z0-9_]{1,40})\b", m.captures[1])
                    h = strip(hm.captures[1])
                    !isempty(h) && length(h) < 50 && push!(pm, Dict{String,Any}(
                        "proof_id"=>id, "premise"=>h,
                        "prover"=>"DReal", "theorem"=>"dreal_$(id)", "source"=>"dreal"))
                end
                id += 1
            end
        catch e; println("Warning: $f: $e"); end
    end
    ps, ts, pm
end
function main(); println("ECHIDNA dReal Extraction"); println("=" ^ 24)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No assertions extracted.") : save_common(ps, ts, pm, "dreal", START_ID, OUT) end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
