#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract ProVerif queries from inria/proverif-examples.
# Vendor: git clone https://gitlab.inria.fr/bblanche/proverif external_corpora/proverif
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/proverif"; const OUT = "training_data"; const START_ID = 1_900_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    if !isdir(DIR); println("ProVerif not found: $DIR"); println("Clone: https://gitlab.inria.fr/bblanche/proverif"); return ps, ts, pm; end
    pv_files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs; (endswith(f, ".pv") || endswith(f, ".pcv")) && push!(pv_files, joinpath(root, f)); end; end
    println("Found $(length(pv_files)) ProVerif files")
    # ProVerif: query attacker(X); noninterf F; weaksecret S; etc.
    pat = r"(query|noninterf|weaksecret|event)\s+([^.]+?)\."s
    for f in pv_files
        try
            c = read(f, String)
            for m in eachmatch(pat, c)
                push!(ps, Dict{String,Any}("id"=>id, "prover"=>"ProVerif",
                    "source_file"=>relpath(f, DIR),
                    "theorem"=>"$(m.captures[1])_$(id)", "goal"=>strip(m.captures[2]),
                    "query_kind"=>m.captures[1], "context"=>Any[]))
                id += 1
            end
        catch e; println("Warning: $f: $e"); end
    end
    ps, ts, pm
end
function main(); println("ECHIDNA ProVerif Extraction"); println("=" ^ 27)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No queries extracted.") : save_common(ps, ts, pm, "proverif", START_ID, OUT) end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
