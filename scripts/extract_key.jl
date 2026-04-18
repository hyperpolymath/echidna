#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract KeY proof problems (Java + JML). Vendor: key-project/key examples.
using JSON3, Dates
const DIR = "external_corpora/key/examples"; const OUT = "training_data"; const START_ID = 1_400_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]
    id = START_ID
    if !isdir(DIR)
        println("KeY examples not found: $DIR"); println("Clone: git clone https://github.com/KeYProject/key external_corpora/key"); return ps, ts, pm
    end
    # Widening (2026-04-18): also accept .proof files (saved KeY proof
    # scripts), .java files with JML annotations, and extract nameable
    # items beyond `\problem`: `\functions`, `\predicates`,
    # `\include`, JML `@requires`/`@ensures`/`@invariant`.
    key_files = String[]
    for (root, _, fs) in walkdir(DIR)
        for f in fs
            if endswith(f, ".key") || endswith(f, ".proof") ||
               endswith(f, ".java")
                push!(key_files, joinpath(root, f))
            end
        end
    end
    println("Found $(length(key_files)) KeY + Java source files")

    problem_pat = r"\\problem\s*\{(.*?)\}"s
    functions_pat = r"\\functions\s*\{(.*?)\}"s
    predicates_pat = r"\\predicates\s*\{(.*?)\}"s
    programvars_pat = r"\\programVariables\s*\{(.*?)\}"s
    jml_pat = r"(?:/\*@|//@)\s*(requires|ensures|signals|invariant|pure|assignable|loop_invariant|decreases|behavior|normal_behavior)\s+([^;*]+?)(?:;|\*/)"s
    proof_step_pat = r"\(rule\s+\"([^\"]+)\""

    for f in key_files
        c = try
            read(f, String)
        catch
            continue
        end
        rel = relpath(f, DIR)
        for (pat, kind) in ((problem_pat, "problem"),
                            (functions_pat, "functions"),
                            (predicates_pat, "predicates"),
                            (programvars_pat, "programVariables"))
            matches = try collect(eachmatch(pat, c)) catch; Any[] end
            for (i, m) in enumerate(matches)
                body = first(strip(String(m.captures[1])), 1500)
                isempty(body) && continue
                name = kind == "problem" ? basename(f) : "$(basename(f))_$(kind)_$(i)"
                push!(ps, Dict{String,Any}("id"=>id, "prover"=>"KeY",
                    "source_file"=>rel,
                    "theorem"=>name, "goal"=>body, "kind"=>kind,
                    "context"=>Any[]))
                id += 1
            end
        end
        matches = try collect(eachmatch(jml_pat, c)) catch; Any[] end
        for m in matches
            kind = strip(String(m.captures[1]))
            body = first(strip(String(m.captures[2])), 500)
            isempty(body) && continue
            push!(ps, Dict{String,Any}("id"=>id, "prover"=>"KeY",
                "source_file"=>rel,
                "theorem"=>"jml_$(kind)_$(id)", "goal"=>body,
                "kind"=>"jml_$(kind)", "context"=>Any[]))
            id += 1
        end
        matches = try collect(eachmatch(proof_step_pat, c)) catch; Any[] end
        for (i, m) in enumerate(matches)
            rule = strip(String(m.captures[1]))
            isempty(rule) && continue
            push!(ps, Dict{String,Any}("id"=>id, "prover"=>"KeY",
                "source_file"=>rel,
                "theorem"=>"$(basename(f))_step_$(i)",
                "goal"=>"rule $(rule)", "kind"=>"proof_step",
                "context"=>Any[]))
            id += 1
        end
    end
    ps, ts, pm
end
include("extractor_save_common.jl")
function main(); println("ECHIDNA KeY Extraction"); println("=" ^ 22)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No proofs extracted.") : save_common(ps, ts, pm, "key", START_ID, OUT) end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
