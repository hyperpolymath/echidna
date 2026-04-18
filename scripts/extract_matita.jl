#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract proofs / declarations / .ma files from Matita.
# Vendor location: external_corpora/matita/
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/matita"
const OUT = "training_data"
const START_ID = 3_300_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    if !isdir(DIR); println("Matita corpus not found: $DIR"); println("Vendor source into $DIR and rerun."); return ps, ts, pm; end
    files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs; endswith(f, ".ma") && push!(files, joinpath(root, f)); end; end
    println("Found $(length(files)) .ma files")
    # Widening (2026-04-18): prior pattern matched only `theorem X : T := ...`
    # which is the rarer form. Matita's standard library overwhelmingly
    # uses `lemma`, `definition`, `inductive`, `record`, `axiom`, plus
    # the `qed.`-terminated tactical style.
    kw_pattern = r"(theorem|lemma|axiom|definition|inductive|record|coinductive)\s+([A-Za-z0-9_']+)\s*:\s*(.*?)\s*(?::=|\.\s*(?:qed|end)\.?|\.\s*$)"s
    let_pattern = r"let\s+rec\s+([A-Za-z_][A-Za-z0-9_']*)\s*(.*?):\s*(.*?)\s*:="s
    for f in files
        c = try
            read(f, String)
        catch
            continue
        end
        rel = relpath(f, DIR)
        matches = try collect(eachmatch(kw_pattern, c)) catch; Any[] end
        seen = Set{String}()
        for m in matches
            kind = strip(m.captures[1])
            name = strip(String(m.captures[2]))
            goal = first(strip(String(m.captures[3])), 1000)
            (isempty(name) || name in seen) && continue
            push!(seen, name)
            push!(ps, Dict{String,Any}("id"=>id, "prover"=>"matita",
                "source_file"=>rel, "theorem"=>name, "goal"=>goal,
                "kind"=>kind, "context"=>Any[]))
            id += 1
        end
        matches = try collect(eachmatch(let_pattern, c)) catch; Any[] end
        for m in matches
            name = strip(String(m.captures[1]))
            sig = first(strip(String(m.captures[3])), 1000)
            (isempty(name) || name in seen) && continue
            push!(seen, name)
            push!(ps, Dict{String,Any}("id"=>id, "prover"=>"matita",
                "source_file"=>rel, "theorem"=>name, "goal"=>sig,
                "kind"=>"let rec", "context"=>Any[]))
            id += 1
        end
    end
    ps, ts, pm
end
function main()
    println("ECHIDNA Matita Extraction"); println("=" ^ 40)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No records extracted.") : save_common(ps, ts, pm, "matita", START_ID, OUT)
end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
