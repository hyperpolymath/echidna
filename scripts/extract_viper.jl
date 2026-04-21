#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract Viper (Silver) separation-logic verification problems.
# Vendor: git clone https://github.com/viperproject/silver external_corpora/viper
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/viper"; const OUT = "training_data"; const START_ID = 1_600_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    if !isdir(DIR); println("Viper not found: $DIR"); println("Clone: git clone https://github.com/viperproject/silver $DIR"); return ps, ts, pm; end
    vpr_files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs; endswith(f, ".vpr") && push!(vpr_files, joinpath(root, f)); end; end
    println("Found $(length(vpr_files)) .vpr files")
    # Viper: method NAME(args) returns (...) requires/ensures …
    pat = r"method\s+([a-zA-Z0-9_]+)\s*\([^)]*\)(?:\s*returns\s*\([^)]*\))?\s*(requires.*?|ensures.*?)?(?=\{)"s
    for f in vpr_files
        try
            c = read(f, String)
            for m in eachmatch(pat, c)
                n = strip(m.captures[1])
                spec = m.captures[2] === nothing ? "" : strip(m.captures[2])
                push!(ps, Dict{String,Any}("id"=>id, "prover"=>"Viper",
                    "source_file"=>relpath(f, DIR), "theorem"=>n, "goal"=>spec, "context"=>Any[]))
                # Emit premises: identifiers from method spec (requires/ensures)
                for hm in eachmatch(r"\b([a-zA-Z_][a-zA-Z0-9_]{1,40})\b", spec)
                    h = strip(hm.captures[1])
                    !isempty(h) && length(h) < 50 && push!(pm, Dict{String,Any}(
                        "proof_id"=>id, "premise"=>h,
                        "prover"=>"Viper", "theorem"=>n, "source"=>"viper"))
                end
                id += 1
            end
        catch e; println("Warning: $f: $e"); end
    end
    ps, ts, pm
end
function main(); println("ECHIDNA Viper Extraction"); println("=" ^ 24)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No methods extracted.") : save_common(ps, ts, pm, "viper", START_ID, OUT) end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
