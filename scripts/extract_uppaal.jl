#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract UPPAAL timed-automata reachability / TCTL queries.
# Vendor: https://uppaal.org/documentation/ (examples ship with distribution).
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/uppaal"; const OUT = "training_data"; const START_ID = 2_900_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    if !isdir(DIR); println("UPPAAL examples not found: $DIR"); println("Vendor UPPAAL examples into $DIR"); return ps, ts, pm; end
    q_files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs; (endswith(f, ".q") || endswith(f, ".xml") || endswith(f, ".xta")) && push!(q_files, joinpath(root, f)); end; end
    println("Found $(length(q_files)) UPPAAL files")
    # UPPAAL queries: E<> P, A[] P, E[] P, A<> P  (TCTL)
    pat = r"(?:E<>|A\[\]|E\[\]|A<>)\s*([^\n]+)"
    for f in q_files
        try
            c = read(f, String)
            for m in eachmatch(pat, c)
                push!(ps, Dict{String,Any}("id"=>id, "prover"=>"UPPAAL",
                    "source_file"=>relpath(f, DIR),
                    "theorem"=>"tctl_$(id)", "goal"=>strip(m.match),
                    "context"=>Any[]))
                # Emit premises: identifiers from TCTL query
                for hm in eachmatch(r"\b([A-Za-z_][A-Za-z0-9_]{1,40})\b", m.match)
                    h = strip(hm.captures[1])
                    !isempty(h) && length(h) < 50 && push!(pm, Dict{String,Any}(
                        "proof_id"=>id, "premise"=>h,
                        "prover"=>"UPPAAL", "theorem"=>"tctl_$(id)", "source"=>"uppaal"))
                end
                id += 1
            end
        catch e; println("Warning: $f: $e"); end
    end
    ps, ts, pm
end
function main(); println("ECHIDNA UPPAAL Extraction"); println("=" ^ 25)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No queries extracted.") : save_common(ps, ts, pm, "uppaal", START_ID, OUT) end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
