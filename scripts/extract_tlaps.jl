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
    for (root, _, fs) in walkdir(DIR); for f in fs; (endswith(f, ".tla") || endswith(f, ".cfg")) && push!(files, joinpath(root, f)); end; end
    println("Found $(length(files)) TLA+ files")
    # Widening (2026-04-18): TLA+ has more named top-level items than
    # just THEOREM. Capture LEMMA, AXIOM, ASSUME, and top-level
    # `Name == ...` definitions (which are the bulk of any TLA+ spec).
    thm_pat = r"(THEOREM|LEMMA|COROLLARY|PROPOSITION)\s+([A-Za-z0-9_]+)\s*(?:==|:)\s*(.*?)(?=\n(?:THEOREM|LEMMA|COROLLARY|PROPOSITION|AXIOM|ASSUME|DEFINE|VARIABLE|CONSTANT|=====)|\z)"s
    axiom_pat = r"(AXIOM|ASSUME)\s+([A-Za-z0-9_]+)\s*(?:==|:)?\s*(.*?)(?=\n(?:THEOREM|LEMMA|AXIOM|ASSUME|DEFINE|=====)|\z)"s
    def_pat = r"(?:^|\n)([A-Za-z][A-Za-z0-9_]*)\s*(?:\([^)]*\))?\s*==\s*(.*?)(?=\n[A-Za-z][A-Za-z0-9_]*\s*(?:\([^)]*\))?\s*==|\n(?:THEOREM|LEMMA|AXIOM|ASSUME|VARIABLE|CONSTANT|MODULE|=====)|\z)"s

    for f in files
        c = try
            read(f, String)
        catch
            continue
        end
        rel = relpath(f, DIR)
        seen = Set{String}()
        for (pat, expected_captures) in ((thm_pat, 3), (axiom_pat, 3))
            matches = try collect(eachmatch(pat, c)) catch; Any[] end
            for m in matches
                kind = strip(String(m.captures[1]))
                name = strip(String(m.captures[2]))
                body = first(strip(String(m.captures[3])), 1500)
                isempty(name) && continue
                key = "$(kind):$(name)"
                key in seen && continue
                push!(seen, key)
                push!(ps, Dict{String,Any}("id"=>id, "prover"=>"TLAPS",
                    "source_file"=>rel, "theorem"=>name,
                    "goal"=>body, "kind"=>kind, "context"=>Any[]))
                id += 1
            end
        end
        matches = try collect(eachmatch(def_pat, c)) catch; Any[] end
        for m in matches
            name = strip(String(m.captures[1]))
            body = first(strip(String(m.captures[2])), 1500)
            if !isempty(name) && !isempty(body) &&
               !(name in ("MODULE", "EXTENDS", "INSTANCE", "LOCAL",
                          "VARIABLE", "VARIABLES", "CONSTANT",
                          "CONSTANTS", "RECURSIVE", "ASSUME",
                          "THEOREM", "LEMMA", "AXIOM"))
                key = "def:$(name)"
                if key ∉ seen
                    push!(seen, key)
                    push!(ps, Dict{String,Any}("id"=>id, "prover"=>"TLAPS",
                        "source_file"=>rel, "theorem"=>name,
                        "goal"=>body, "kind"=>"definition",
                        "context"=>Any[]))
                    id += 1
                end
            end
        end
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
