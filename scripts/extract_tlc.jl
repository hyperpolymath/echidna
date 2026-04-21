#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract TLC model-checker inputs from tlaplus/examples (same repo as TLAPS).
# TLC checks specifications rather than proves theorems; records capture
# spec+invariant pairs as proof-state analogues.
using JSON3, Dates
const DIR = "external_corpora/tlaplus_examples"
const OUT = "training_data"
const START_ID = 1_300_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]
    id = START_ID
    if !isdir(DIR)
        println("TLA+ examples not found: $DIR")
        println("Clone: git clone https://github.com/tlaplus/Examples $DIR")
        return ps, ts, pm
    end
    tla_files = String[]; cfg_files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs
        endswith(f, ".tla") && push!(tla_files, joinpath(root, f))
        endswith(f, ".cfg") && push!(cfg_files, joinpath(root, f))
    end; end
    println("Found $(length(tla_files)) .tla + $(length(cfg_files)) .cfg files")
    inv_pat = r"(INVARIANT|PROPERTY|SPECIFICATION)\s+([A-Za-z0-9_]+)"
    for f in cfg_files
        try
            c = read(f, String)
            for m in eachmatch(inv_pat, c)
                push!(ps, Dict{String,Any}("id"=>id, "prover"=>"TLC",
                    "source_file"=>relpath(f, DIR), "theorem"=>strip(m.captures[2]),
                    "goal"=>"$(m.captures[1]) $(m.captures[2])", "context"=>Any[]))
                # Emit premises: identifiers from invariant/property name
                for hm in eachmatch(r"\b([A-Za-z_][A-Za-z0-9_]{1,40})\b", m.captures[2])
                    h = strip(hm.captures[1])
                    !isempty(h) && length(h) < 50 && push!(pm, Dict{String,Any}(
                        "proof_id"=>id, "premise"=>h,
                        "prover"=>"TLC", "theorem"=>strip(m.captures[2]), "source"=>"tlc"))
                end
                id += 1
            end
        catch e; println("Warning: $f: $e"); end
    end
    ps, ts, pm
end
function save(ps, ts, pm, prover)
    mkpath(OUT)
    for (name, data) in [("proof_states", ps), ("tactics", ts), ("premises", pm)]
        open(joinpath(OUT, "$(name)_$(lowercase(prover)).jsonl"), "w") do f
            for x in data; println(f, JSON3.write(x)); end
        end
    end
    open(joinpath(OUT, "stats_$(lowercase(prover)).json"), "w") do f
        JSON3.pretty(f, Dict{String,Any}("prover"=>prover, "extraction_date"=>string(Dates.today()),
            "proof_states_count"=>length(ps), "start_id"=>START_ID,
            "end_id"=>isempty(ps) ? START_ID : START_ID + length(ps) - 1))
    end
    println("Saved $(length(ps)) proof states")
end
function main()
    println("ECHIDNA TLC Extraction"); println("=" ^ 22)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No specs extracted.") : save(ps, ts, pm, "tlc")
end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
