#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract NuSMV / nuXmv model-checker CTL/LTL properties.
# Vendor: https://nusmv.fbk.eu/distrib/ (examples ship with distribution).
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/nusmv"; const OUT = "training_data"; const START_ID = 2_600_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    if !isdir(DIR); println("NuSMV not found: $DIR"); println("Vendor NuSMV examples into $DIR"); return ps, ts, pm; end
    smv_files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs; endswith(f, ".smv") && push!(smv_files, joinpath(root, f)); end; end
    println("Found $(length(smv_files)) .smv files")
    pat = r"(CTLSPEC|LTLSPEC|INVARSPEC|COMPUTE)\s+(.*?)(?=\n\s*(?:CTLSPEC|LTLSPEC|INVARSPEC|COMPUTE|MODULE|VAR|ASSIGN|DEFINE)|\Z)"s
    for f in smv_files
        try
            c = read(f, String)
            for m in eachmatch(pat, c)
                push!(ps, Dict{String,Any}("id"=>id, "prover"=>"NuSMV",
                    "source_file"=>relpath(f, DIR),
                    "theorem"=>"$(m.captures[1])_$(id)", "goal"=>strip(m.captures[2]),
                    "spec_kind"=>m.captures[1], "context"=>Any[]))
                # Emit premises: identifiers from CTL/LTL formula
                for hm in eachmatch(r"\b([A-Za-z_][A-Za-z0-9_]{1,40})\b", m.captures[2])
                    h = strip(hm.captures[1])
                    !isempty(h) && length(h) < 50 && push!(pm, Dict{String,Any}(
                        "proof_id"=>id, "premise"=>h,
                        "prover"=>"NuSMV", "theorem"=>"$(m.captures[1])_$(id)", "source"=>"nusmv"))
                end
                id += 1
            end
        catch e; println("Warning: $f: $e"); end
    end
    ps, ts, pm
end
function main(); println("ECHIDNA NuSMV Extraction"); println("=" ^ 24)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No specs extracted.") : save_common(ps, ts, pm, "nusmv", START_ID, OUT) end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
