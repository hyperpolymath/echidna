#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
#
# Mathematical Components (mathcomp) extractor for ECHIDNA training data.
# Reads .v Coq/ssreflect source files and extracts Lemma/Theorem statements
# together with their proofs (ssreflect tactics).
#
# Input:  external_corpora/mathcomp/ (git clone of math-comp/math-comp)
# Output: training_data/proof_states_mathcomp.a2ml
#         training_data/tactics_mathcomp.a2ml
#         training_data/stats_mathcomp.a2ml

using Dates, JSON3
include("a2ml_emit.jl")
using .A2MLEmit

const ID_BASE = 200000
const PROVER = "Coq"   # mathcomp targets Rocq/Coq

# Match Lemma/Theorem/Corollary/Fact/Proposition/Remark <name> <binders>? : <stmt>.
# We keep statement capture short-circuited at the first top-level period followed
# by whitespace or newline — imperfect but fast.
const STMT_PAT = r"(Lemma|Theorem|Corollary|Fact|Proposition|Remark)\s+([A-Za-z_][A-Za-z0-9_']*)\s*([^:.]*?):\s*(.*?)\.\s*\n"s

const PROOF_PAT = r"Proof\.(.*?)(Qed|Defined|Admitted)\s*\."s

"""
    split_tactics(proof_body::AbstractString) -> Vector{String}

Split ssreflect proof body into tactic steps at top-level periods.
Balanced brackets are respected so `case: (foo x).` stays together.
"""
function split_tactics(proof_body::AbstractString)::Vector{String}
    tactics = String[]
    buf = IOBuffer()
    depth = 0
    for c in proof_body
        if c == '(' || c == '[' || c == '{'
            depth += 1; print(buf, c)
        elseif c == ')' || c == ']' || c == '}'
            depth = max(0, depth - 1); print(buf, c)
        elseif c == '.' && depth == 0
            s = strip(String(take!(buf)))
            isempty(s) || push!(tactics, s)
        else
            print(buf, c)
        end
    end
    s = strip(String(take!(buf)))
    isempty(s) || push!(tactics, s)
    return tactics
end

function find_v_files(base_dir::String)::Vector{String}
    files = String[]
    for (root, _dirs, fs) in walkdir(base_dir)
        for f in fs
            endswith(f, ".v") && push!(files, joinpath(root, f))
        end
    end
    sort!(files)
    return files
end

function extract_all(base_dir::String)
    files = find_v_files(base_dir)
    println("Found $(length(files)) .v files in $base_dir")

    proof_states = Dict{String,Any}[]
    tactics = Dict{String,Any}[]
    premises = Dict{String,Any}[]
    skipped_noproof = 0
    errors = 0

    # Coq/ssreflect premise patterns: intro/apply/have/pose/specialize
    coq_hyp_patterns = [
        r"\bintro\s+([a-zA-Z0-9_']+)",
        r"\bintros\s+([a-zA-Z0-9_'\s]+)",
        r"\bhave\s+([a-zA-Z0-9_']+)\s*:",
        r"\bpose\s+([a-zA-Z0-9_']+)\s*:=",
        r"\bspecialize\s+\(?([a-zA-Z0-9_']+)\b",
    ]

    for (idx, fpath) in enumerate(files)
        content = try
            read(fpath, String)
        catch
            errors += 1
            continue
        end

        theorem_matches = try
            collect(eachmatch(STMT_PAT, content))
        catch
            errors += 1
            continue
        end

        for tm in theorem_matches
            kind, name, binders, stmt = tm.captures
            record_id = ID_BASE + length(proof_states)

            # Look for Proof block immediately after the theorem statement.
            # Use thisind/nextind to keep the slice on a valid UTF-8
            # character boundary — raw byte indices crash on multi-
            # byte glyphs (° µ ε Σ etc. appear in mathcomp-analysis).
            proof_start = tm.offset + length(tm.match)
            rest = if proof_start > lastindex(content)
                ""
            else
                idx = thisind(content, min(proof_start, lastindex(content)))
                content[idx:end]
            end
            pm = try
                match(PROOF_PAT, rest)
            catch
                nothing
            end

            if pm === nothing
                skipped_noproof += 1
                continue
            end

            proof_body = pm.captures[1]
            terminator = pm.captures[2]
            steps = split_tactics(proof_body)
            isempty(steps) && continue

            theorem = String(strip(name))
            goal = String(strip(stmt))
            # Join binders into goal if present
            bstr = String(strip(binders))
            isempty(bstr) || (goal = bstr * " : " * goal)

            rel = relpath(fpath, base_dir)
            push!(proof_states, Dict{String,Any}(
                "id" => record_id,
                "prover" => PROVER,
                "theorem" => theorem,
                "goal" => goal,
                "context" => String[],
                "source" => "mathcomp",
                "kind" => String(kind),
                "terminator" => String(terminator),
                "file" => rel,
                "proof_steps" => length(steps),
            ))

            # Emit premise records from proof body
            proof_body_text = String(proof_body)
            for hyp_pattern in coq_hyp_patterns
                for hyp_match in eachmatch(hyp_pattern, proof_body_text)
                    hyps = [strip(h) for h in split(hyp_match.captures[1], ' ')]
                    for hyp in hyps
                        if !isempty(hyp) && length(hyp) < 50
                            push!(premises, Dict{String,Any}(
                                "proof_id" => record_id,
                                "premise" => String(hyp),
                                "prover" => PROVER,
                                "theorem" => theorem,
                                "source" => "mathcomp",
                            ))
                        end
                    end
                end
            end

            for (step_idx, tac) in enumerate(steps)
                push!(tactics, Dict{String,Any}(
                    "proof_id" => record_id,
                    "step" => step_idx,
                    "tactic" => tac,
                    "prover" => PROVER,
                ))
            end
        end

        idx % 200 == 0 && println("  processed $idx/$(length(files)) files ...")
    end

    id_range = isempty(proof_states) ? "none" : "$(ID_BASE)-$(ID_BASE + length(proof_states) - 1)"
    stats = Dict{String,Any}(
        "version" => "v2.0-mathcomp",
        "extraction_date" => Dates.format(now(), dateformat"yyyy-mm-ddTHH:MM:SS"),
        "total_files_scanned" => length(files),
        "total_proofs" => length(proof_states),
        "total_tactics" => length(tactics),
        "total_premises" => length(premises),
        "skipped_no_proof" => skipped_noproof,
        "read_errors" => errors,
        "source" => "Mathematical Components (math-comp/math-comp)",
        "id_range" => id_range,
    )
    return proof_states, tactics, premises, stats
end

function save_results(proof_states, tactics, premises, stats; output_dir="training_data")
    mkpath(output_dir)
    write_records_file(
        joinpath(output_dir, "proof_states_mathcomp.a2ml"),
        stats, proof_states, "proof-state";
        header="mathcomp proof-state records (Coq/ssreflect training data)")
    write_records_file(
        joinpath(output_dir, "tactics_mathcomp.a2ml"),
        stats, tactics, "tactic";
        header="mathcomp tactic records (ssreflect tactics per step)")
    open(joinpath(output_dir, "premises_mathcomp.jsonl"), "w") do fh
        for p in premises
            JSON3.write(fh, p); println(fh)
        end
    end
    open(joinpath(output_dir, "stats_mathcomp.a2ml"), "w") do fh
        println(fh, "# SPDX-License-Identifier: PMPL-1.0-or-later")
        println(fh, "# mathcomp extraction statistics"); println(fh)
        A2MLEmit.write_metadata_table(fh, stats)
    end
    println("\nSaved $(length(proof_states)) proof states, $(length(tactics)) tactics, $(length(premises)) premises -> $output_dir/*_mathcomp.*")
end

function main()::Int
    println("=" ^ 60)
    println("ECHIDNA Mathcomp Extractor")
    println("=" ^ 60)
    # Widening (2026-04-18): walk the main math-comp repo plus
    # additional mathcomp-family libraries to push past 20K.
    candidates = [
        "external_corpora/mathcomp",
        "external_corpora/mathcomp-analysis",
        "external_corpora/mathcomp-finmap",
        "external_corpora/mathcomp-algebra-tactics",
        "external_corpora/mathcomp-mczify",
    ]
    roots = filter(isdir, candidates)
    if isempty(roots)
        println("ERROR: No mathcomp corpus directories found")
        return 1
    end
    println("Walking $(length(roots)) mathcomp roots: $(join(basename.(roots), ", "))")
    base_dir = roots[1]
    # Override extract_all to scan every root.
    proof_states = Dict{String,Any}[]
    tactics = Dict{String,Any}[]
    premises = Dict{String,Any}[]
    stats = Dict{String,Any}()
    for root in roots
        ps, ts, pm, st = extract_all(root)
        append!(proof_states, ps)
        append!(tactics, ts)
        append!(premises, pm)
        stats = st  # keep last
    end
    stats["total_proofs"] = length(proof_states)
    stats["total_tactics"] = length(tactics)
    stats["total_premises"] = length(premises)
    stats["id_range"] = isempty(proof_states) ? "none" :
        "$(ID_BASE)-$(ID_BASE + length(proof_states) - 1)"
    if isempty(proof_states)
        println("\nWARNING: No proof states extracted.")
        return 1
    end
    save_results(proof_states, tactics, premises, stats)
    println("\nTotal: $(stats["total_proofs"]) proofs / $(stats["total_tactics"]) tactics (IDs $(stats["id_range"]))")
    return 0
end

if abspath(PROGRAM_FILE) == @__FILE__
    exit(main())
end
