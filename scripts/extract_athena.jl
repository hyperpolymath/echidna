#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract proofs / declarations / .ath files from Athena.
# Vendor location: external_corpora/athena/
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/athena"
const OUT = "training_data"
const START_ID = 3_500_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    # Widening (2026-04-18): walk the dedicated Athena dir plus any
    # sibling *athena* clones and follow symlinks so symlinked Athena
    # bundles (athena-lib, maude2athena) are picked up.
    roots = String[]
    isdir(DIR) && push!(roots, DIR)
    for sib in readdir(dirname(DIR); join=true)
        (sib == DIR) && continue
        if isdir(sib) && occursin("athena", lowercase(basename(sib))) && sib ∉ roots
            push!(roots, sib)
        end
    end
    if isempty(roots)
        println("Athena corpora not found: $DIR")
        println("Vendor AthenaFoundation/athena (recommended).")
        return ps, ts, pm
    end

    files = String[]
    for root in roots
        for (rr, _, fs) in walkdir(root; follow_symlinks=true)
            for f in fs
                endswith(f, ".ath") && push!(files, joinpath(rr, f))
            end
        end
    end
    println("Found $(length(files)) .ath files across $(length(roots)) root(s)")

    # Widen: Athena has more named forms than `define` alone —
    # declare (function / sort / domain), assert (axioms), datatype,
    # theorem blocks, structure / by-induction.
    define_pat = r"define\s+([A-Za-z0-9_'-]+)\s*:=\s*\((.*?)\)"s
    declare_pat = r"declare\s+([A-Za-z0-9_'-]+)\s*:\s*([^.]+?)\."s
    assert_pat = r"assert\*?\s+([A-Za-z0-9_'-]+)\s*:?\s*(.*?)\s*(?:\n\s*(?:define|declare|assert|theorem|datatype|domain|module|\Z))"s
    theorem_pat = r"theorem\s+([A-Za-z0-9_'-]+)\s*:?\s*(.*?)\s*(?:\n\s*(?:define|declare|assert|theorem|datatype|domain|module|\Z))"s
    datatype_pat = r"datatype\s+([A-Za-z0-9_'-]+)\s*:=\s*(.*?)\s*(?:\n\s*(?:define|declare|assert|theorem|datatype|domain|module|\Z))"s
    struct_pat = r"structure\s+([A-Za-z0-9_'-]+)\s*:=\s*(.*?)(?:\s*\n\s*(?:define|declare|assert|theorem|datatype|domain|module|\Z))"s

    for f in files
        c = try
            read(f, String)
        catch
            continue
        end
        rel = relpath(f, dirname(DIR))
        seen = Set{String}()
        for (pat, kind) in ((define_pat, "define"),
                            (declare_pat, "declare"),
                            (assert_pat, "assert"),
                            (theorem_pat, "theorem"),
                            (datatype_pat, "datatype"),
                            (struct_pat, "structure"))
            matches = try collect(eachmatch(pat, c)) catch; Any[] end
            for m in matches
                name = strip(String(m.captures[1]))
                body = first(strip(String(m.captures[2])), 800)
                (isempty(name) || "$(kind):$(name)" in seen) && continue
                push!(seen, "$(kind):$(name)")
                push!(ps, Dict{String,Any}("id"=>id, "prover"=>"athena",
                    "source_file"=>rel, "theorem"=>name, "goal"=>body,
                    "kind"=>kind, "context"=>Any[]))
                # Emit premises: Athena define/assert identifiers in body
                for hm in eachmatch(r"\b([A-Za-z][A-Za-z0-9_'-]{1,40})\b", body)
                    h = strip(hm.captures[1])
                    if !isempty(h) && length(h) < 50
                        push!(pm, Dict{String,Any}("proof_id"=>id, "premise"=>h,
                            "prover"=>"athena", "theorem"=>name, "source"=>"athena"))
                    end
                end
                id += 1
            end
        end
    end
    ps, ts, pm
end
function main()
    println("ECHIDNA Athena Extraction"); println("=" ^ 40)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No records extracted.") : save_common(ps, ts, pm, "athena", START_ID, OUT)
end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
