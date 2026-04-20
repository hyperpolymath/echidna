#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
#
# Shared extractor for the SAT-solver fleet (CaDiCaL, Kissat, MiniSat).
# All three consume DIMACS CNF, so one extractor builds the corpus and
# emits one records-set per target prover so the ML layer trains per-prover
# policies (they share input format but differ in heuristics / behaviour).
#
# Vendor:
#   - SAT Competition: https://www.satcompetition.org/ (benchmark tarballs)
#   - Place under external_corpora/sat_benchmarks/
#   - Or clone SATLIB: https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/sat_benchmarks"; const OUT = "training_data"
# Reserve 3×100K slots for the three SAT provers sharing this extractor.
const CADICAL_START = 2_300_000
const KISSAT_START  = 2_400_000
const MINISAT_START = 2_500_000

function count_dimacs(cnf_text::AbstractString)
    # p cnf NVAR NCLAUSE line
    m = match(r"p\s+cnf\s+(\d+)\s+(\d+)", cnf_text)
    m === nothing ? (0, 0) : (parse(Int, m.captures[1]), parse(Int, m.captures[2]))
end

function collect_for(prover::String, start_id::Int)
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = start_id
    if !isdir(DIR); return ps, ts, pm; end
    cnf_files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs; endswith(f, ".cnf") && push!(cnf_files, joinpath(root, f)); end; end
    for f in cnf_files
        try
            c = read(f, String)
            nvar, nclause = count_dimacs(c)
            push!(ps, Dict{String,Any}("id"=>id, "prover"=>prover,
                "source_file"=>relpath(f, DIR),
                "theorem"=>basename(f),
                "goal"=>"cnf vars=$nvar clauses=$nclause",
                "context"=>Any[]))
            id += 1
        catch e; println("Warning: $f: $e"); end
    end
    ps, ts, pm
end

function main()
    println("ECHIDNA SAT Benchmarks Extraction (CaDiCaL + Kissat + MiniSat)")
    println("=" ^ 60)
    if !isdir(DIR)
        println("Benchmarks not found: $DIR")
        println("Vendor SAT Competition tarballs into $DIR (as .cnf files)")
        return
    end
    for (prover, start_id) in [("CaDiCaL", CADICAL_START), ("Kissat", KISSAT_START), ("MiniSat", MINISAT_START)]
        ps, ts, pm = collect_for(prover, start_id)
        save_common(ps, ts, pm, lowercase(prover), start_id, OUT)
    end
end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
