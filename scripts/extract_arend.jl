#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract proofs / declarations / .ard files from Arend.
# Vendor location: external_corpora/arend/
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/arend"
const OUT = "training_data"
const START_ID = 3_400_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    # Widening (2026-04-18): the canonical Arend proof corpus lives
    # in JetBrains/arend-lib (not the Arend compiler repo, which is
    # mostly Java). Walk both roots when present.
    roots = String[]
    for cand in (DIR, joinpath(dirname(DIR), "arend-lib"))
        isdir(cand) && push!(roots, cand)
    end
    if isempty(roots)
        println("Arend corpora not found: $DIR or sibling arend-lib/")
        println("Clone JetBrains/arend-lib for the proof corpus.")
        return ps, ts, pm
    end

    files = String[]
    for root in roots
        for (rr, _, fs) in walkdir(root)
            for f in fs
                endswith(f, ".ard") && push!(files, joinpath(rr, f))
            end
        end
    end
    println("Found $(length(files)) .ard files across $(length(roots)) root(s)")

    func_pat = r"\\func\s+([A-Za-z0-9_'\-]+)\s*(.*?)\s*(?:=>|\\elim|\\with|\\where|\\cowith)"s
    data_pat = r"\\data\s+([A-Za-z0-9_'\-]+)\s*(.*?)(?:\s*\\where|\s*$)"sm
    class_pat = r"\\(?:record|class)\s+([A-Za-z0-9_'\-]+)\s*(.*?)(?:\s*\{|\s*\\where|\s*$)"sm
    instance_pat = r"\\instance\s+([A-Za-z0-9_'\-]+)\s*(.*?)(?:=>|:)"s
    lemma_pat = r"\\lemma\s+([A-Za-z0-9_'\-]+)\s*(.*?)\s*(?:=>|:)"s

    for f in files
        c = try
            read(f, String)
        catch
            continue
        end
        rel = relpath(f, dirname(DIR))
        seen = Set{String}()
        for (pat, kind) in ((func_pat, "func"),
                            (data_pat, "data"),
                            (class_pat, "class"),
                            (instance_pat, "instance"),
                            (lemma_pat, "lemma"))
            matches = try collect(eachmatch(pat, c)) catch; Any[] end
            for m in matches
                name = strip(String(m.captures[1]))
                body = first(strip(String(m.captures[2])), 1000)
                (isempty(name) || name in seen) && continue
                push!(seen, name)
                push!(ps, Dict{String,Any}("id"=>id, "prover"=>"arend",
                    "source_file"=>rel, "theorem"=>name,
                    "kind"=>kind, "goal"=>body, "context"=>Any[]))
                id += 1
            end
        end
    end
    ps, ts, pm
end
function main()
    println("ECHIDNA Arend Extraction"); println("=" ^ 40)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No records extracted.") : save_common(ps, ts, pm, "arend", START_ID, OUT)
end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
