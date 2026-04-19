#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract Tamarin security-protocol theories from tamarin-prover examples.
# Vendor: git clone https://github.com/tamarin-prover/tamarin-prover external_corpora/tamarin
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/tamarin/examples"; const OUT = "training_data"; const START_ID = 1_800_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    if !isdir(DIR); println("Tamarin examples not found: $DIR"); println("Clone: git clone https://github.com/tamarin-prover/tamarin-prover external_corpora/tamarin"); return ps, ts, pm; end
    spthy_files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs; endswith(f, ".spthy") && push!(spthy_files, joinpath(root, f)); end; end
    println("Found $(length(spthy_files)) .spthy files")
    # Tamarin: lemma NAME: "FORMULA"
    pat = r"lemma\s+([A-Za-z0-9_]+)\s*(?:\[[^\]]*\])?\s*:\s*\"([^\"]+)\""s
    for f in spthy_files
        try
            c = read(f, String)
            for m in eachmatch(pat, c)
                push!(ps, Dict{String,Any}("id"=>id, "prover"=>"Tamarin",
                    "source_file"=>relpath(f, DIR), "theorem"=>strip(m.captures[1]),
                    "goal"=>strip(m.captures[2]), "context"=>Any[]))
                id += 1
            end
        catch e; println("Warning: $f: $e"); end
    end
    ps, ts, pm
end
function main(); println("ECHIDNA Tamarin Extraction"); println("=" ^ 26)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No lemmas extracted.") : save_common(ps, ts, pm, "tamarin", START_ID, OUT) end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
