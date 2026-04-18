#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract KeY proof problems (Java + JML). Vendor: key-project/key examples.
using JSON3, Dates
const DIR = "external_corpora/key/examples"; const OUT = "training_data"; const START_ID = 1_400_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]
    id = START_ID
    if !isdir(DIR)
        println("KeY examples not found: $DIR"); println("Clone: git clone https://github.com/KeYProject/key external_corpora/key"); return ps, ts, pm
    end
    key_files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs; endswith(f, ".key") && push!(key_files, joinpath(root, f)); end; end
    println("Found $(length(key_files)) .key files")
    pat = r"\\problem\s*\{(.*?)\}"s
    for f in key_files
        try
            c = read(f, String)
            for m in eachmatch(pat, c)
                push!(ps, Dict{String,Any}("id"=>id, "prover"=>"KeY",
                    "source_file"=>relpath(f, DIR),
                    "theorem"=>basename(f), "goal"=>strip(m.captures[1]), "context"=>Any[]))
                id += 1
            end
        catch e; println("Warning: $f: $e"); end
    end
    ps, ts, pm
end
include("extractor_save_common.jl")
function main(); println("ECHIDNA KeY Extraction"); println("=" ^ 22)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No proofs extracted.") : save_common(ps, ts, pm, "key", START_ID, OUT) end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
