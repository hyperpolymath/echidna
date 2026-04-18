#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract TLA+ proofs from the TLAPS examples + tlaplus/examples repo.
# Vendor: git clone https://github.com/tlaplus/Examples external_corpora/tlaplus_examples
using JSON3, Dates
const DIR = "external_corpora/tlaplus_examples"
const OUT = "training_data"
const START_ID = 1_200_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]
    id = START_ID
    if !isdir(DIR)
        println("TLA+ examples not found: $DIR")
        println("Clone: git clone https://github.com/tlaplus/Examples $DIR")
        return ps, ts, pm
    end
    files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs; endswith(f, ".tla") && push!(files, joinpath(root, f)); end; end
    println("Found $(length(files)) TLA+ files")
    # THEOREM Name == Statement   or   THEOREM Name : Statement
    pat = r"THEOREM\s+([A-Za-z0-9_]+)\s*(?:==|:)\s*(.*?)(?=\n(?:THEOREM|LEMMA|AXIOM|DEFINE|====)|$)"s
    for f in files
        try
            c = read(f, String)
            for m in eachmatch(pat, c)
                n, s = strip(m.captures[1]), strip(m.captures[2])
                if !isempty(n) && !isempty(s)
                    push!(ps, Dict{String,Any}("id"=>id, "prover"=>"TLAPS", "source_file"=>relpath(f, DIR), "theorem"=>n, "goal"=>s, "context"=>Any[]))
                    id += 1
                end
            end
        catch e; println("Warning: $f: $e"); end
    end
    ps, ts, pm
end
function save(ps, ts, pm, prover)
    mkpath(OUT)
    open(joinpath(OUT, "proof_states_$(lowercase(prover)).jsonl"), "w") do f; for s in ps; println(f, JSON3.write(s)); end; end
    open(joinpath(OUT, "tactics_$(lowercase(prover)).jsonl"), "w") do f; for t in ts; println(f, JSON3.write(t)); end; end
    open(joinpath(OUT, "premises_$(lowercase(prover)).jsonl"), "w") do f; for p in pm; println(f, JSON3.write(p)); end; end
    open(joinpath(OUT, "stats_$(lowercase(prover)).json"), "w") do f
        JSON3.pretty(f, Dict{String,Any}("prover"=>prover, "extraction_date"=>string(Dates.today()),
            "proof_states_count"=>length(ps), "tactics_count"=>length(ts), "premises_count"=>length(pm),
            "start_id"=>START_ID, "end_id"=>isempty(ps) ? START_ID : START_ID + length(ps) - 1))
    end
    println("Saved $(length(ps)) proof states")
end
function main()
    println("ECHIDNA TLAPS Extraction"); println("=" ^ 24)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No proofs extracted.") : save(ps, ts, pm, "tlaps")
end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
