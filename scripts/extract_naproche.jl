#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract proofs / declarations / ForTheL files from Naproche (ForTheL).
# Vendor location: external_corpora/naproche/
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/naproche"
const OUT = "training_data"
const START_ID = 3_200_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    if !isdir(DIR); println("Naproche (ForTheL) corpus not found: $DIR"); println("Vendor source into $DIR and rerun."); return ps, ts, pm; end
    files = String[]
    for (root, _, fs) in walkdir(DIR)
        for f in fs
            # Widening (2026-04-18): Naproche now publishes sources
            # as .ftl.tex (sTeX literate form) rather than bare .ftl.
            if endswith(f, ".ftl") || endswith(f, ".ftl.tex") ||
               endswith(f, ".ftl.en.tex")
                push!(files, joinpath(root, f))
            end
        end
    end
    println("Found $(length(files)) ForTheL files")

    # sTeX/Naproche carries theorems in \begin{theorem}[forthel,
    # title=TITLE, name=NAME] ... \end{theorem} blocks.
    env_pat = r"\\begin\{(theorem|lemma|corollary|proposition|definition|axiom)\}(?:\[([^\]]*)\])?\s*(.*?)\\end\{\1\}"s
    # Older bare-ftl: `Theorem NAME. BODY Proof. ... Qed.`
    plain_pat = r"(Theorem|Lemma|Corollary|Proposition|Definition|Axiom)\s+([A-Za-z][A-Za-z0-9_ \-]*?)\.\s*(.*?)(?=\n\s*(?:Theorem|Lemma|Corollary|Proposition|Definition|Axiom|Proof|Qed)|\z)"s

    for f in files
        c = try
            read(f, String)
        catch
            continue
        end
        rel = relpath(f, DIR)

        matches = try collect(eachmatch(env_pat, c)) catch; Any[] end
        for (i, m) in enumerate(matches)
            kind = strip(m.captures[1])
            opts = m.captures[2] === nothing ? "" : strip(m.captures[2])
            body = first(strip(m.captures[3]), 2000)
            name_match = match(r"name=([A-Za-z0-9_\-]+)", opts)
            title_match = match(r"title=([^,\]]+)", opts)
            name = name_match !== nothing ? strip(name_match.captures[1]) :
                   title_match !== nothing ? replace(strip(title_match.captures[1]), r"\s+" => "_") :
                   "$(kind)_$(i)"
            push!(ps, Dict{String,Any}("id"=>id, "prover"=>"naproche",
                "source_file"=>rel, "theorem"=>name,
                "kind"=>kind, "goal"=>body, "context"=>Any[]))
            # Emit premises: ForTheL identifiers referenced in body
            for hm in eachmatch(r"\b([A-Za-z][A-Za-z0-9_]{1,40})\b", body)
                h = strip(hm.captures[1])
                !isempty(h) && length(h) < 50 && push!(pm, Dict{String,Any}(
                    "proof_id"=>id, "premise"=>h,
                    "prover"=>"naproche", "theorem"=>name, "source"=>"naproche"))
            end
            id += 1
        end

        matches = try collect(eachmatch(plain_pat, c)) catch; Any[] end
        for m in matches
            kind = strip(String(m.captures[1]))
            name = replace(strip(String(m.captures[2])), r"\s+" => "_")
            body = first(strip(String(m.captures[3])), 2000)
            isempty(name) && continue
            push!(ps, Dict{String,Any}("id"=>id, "prover"=>"naproche",
                "source_file"=>rel, "theorem"=>name,
                "kind"=>kind, "goal"=>body, "context"=>Any[]))
            id += 1
        end
    end
    ps, ts, pm
end
function main()
    println("ECHIDNA Naproche (ForTheL) Extraction"); println("=" ^ 40)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No records extracted.") : save_common(ps, ts, pm, "naproche", START_ID, OUT)
end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
