#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract proofs / declarations / λProlog .mod files from λProlog.
# Vendor location: external_corpora/lambda_prolog/
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/lambda_prolog"
# 2026-04-18 (echidna#12 100K push): also walk sibling ELPI clone
# (LPCIC/elpi — the dominant λProlog implementation in active use;
# ships ~467 .elpi / .mod / .sig files of stdlib + regressions +
# examples).
const EXTRA_DIRS = [
    "external_corpora/elpi-lang",
]
const OUT = "training_data"
const START_ID = 3_600_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    roots = String[]
    isdir(DIR) && push!(roots, DIR)
    for d in EXTRA_DIRS
        isdir(d) && push!(roots, d)
    end
    if isempty(roots); println("λProlog corpus not found: $DIR"); println("Vendor source into $DIR and rerun."); return ps, ts, pm; end
    files = String[]
    for root_dir in roots
        for (root, _, fs) in walkdir(root_dir)
            for f in fs
                # Widening (2026-04-18): also accept .elpi (ELPI
                # implementation of λProlog) and .sig (Teyjus signatures).
                if endswith(f, ".mod") || endswith(f, ".elpi") ||
                   endswith(f, ".sig")
                    push!(files, joinpath(root, f))
                end
            end
        end
    end
    println("Found $(length(files)) λProlog source files")

    # Hornish clause head: `name args :- body` — original pattern.
    head_pat = r"([a-zA-Z_][a-zA-Z0-9_]*)\s+([^.:]*?)\s*:-"s
    # Declarations in Teyjus signatures: `kind N type.`, `type NAME T.`,
    # `pred NAME ...`, plus ELPI's `kind`, `type`, `pred`, `macro`,
    # `mode`, `accumulate` forms.
    decl_pat = r"(kind|type|pred|macro|mode|accumulate|namespace|module|sig)\s+([a-zA-Z_][a-zA-Z0-9_']*)\s+(.*?)\.\s*$"sm

    for f in files
        c = try
            read(f, String)
        catch
            continue
        end
        rel = relpath(f, DIR)
        matches = try collect(eachmatch(head_pat, c)) catch; Any[] end
        for m in matches
            n = strip(String(m.captures[1]))
            g = first(strip(String(m.captures[2])), 600)
            isempty(n) && continue
            push!(ps, Dict{String,Any}("id"=>id, "prover"=>"lambda_prolog",
                "source_file"=>rel, "theorem"=>n, "goal"=>g,
                "kind"=>"clause", "context"=>Any[]))
            # Emit premises: predicate names in clause args
            for hm in eachmatch(r"\b([a-zA-Z_][a-zA-Z0-9_']{1,40})\b", g)
                h = strip(hm.captures[1])
                !isempty(h) && length(h) < 50 && push!(pm, Dict{String,Any}(
                    "proof_id"=>id, "premise"=>h,
                    "prover"=>"lambda_prolog", "theorem"=>n, "source"=>"lambda_prolog"))
            end
            id += 1
        end
        matches = try collect(eachmatch(decl_pat, c)) catch; Any[] end
        for m in matches
            kind = strip(String(m.captures[1]))
            name = strip(String(m.captures[2]))
            body = first(strip(String(m.captures[3])), 600)
            isempty(name) && continue
            push!(ps, Dict{String,Any}("id"=>id, "prover"=>"lambda_prolog",
                "source_file"=>rel, "theorem"=>name, "goal"=>body,
                "kind"=>kind, "context"=>Any[]))
            id += 1
        end
    end
    ps, ts, pm
end
function main()
    println("ECHIDNA λProlog Extraction"); println("=" ^ 40)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No records extracted.") : save_common(ps, ts, pm, "lambda_prolog", START_ID, OUT)
end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
