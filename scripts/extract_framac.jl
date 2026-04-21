#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract Frama-C / ACSL proof obligations from the Frama-C tests + WP tutorials.
# Vendor: git clone https://git.frama-c.com/pub/frama-c external_corpora/frama-c
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/frama-c"; const OUT = "training_data"; const START_ID = 1_500_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    if !isdir(DIR); println("Frama-C not found: $DIR"); println("Clone: git clone https://git.frama-c.com/pub/frama-c $DIR"); return ps, ts, pm; end
    c_files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs; (endswith(f, ".c") || endswith(f, ".h") || endswith(f, ".i")) && push!(c_files, joinpath(root, f)); end; end
    println("Found $(length(c_files)) .c/.h/.i files")
    # ACSL annotations in /*@ ... */ or //@ blocks. Widened
    # (2026-04-18) to cover the full ACSL vocabulary, not just the
    # original six clause keywords.
    acsl_clause_pat = r"(?:/\*@|//@)\s*(requires|ensures|assigns|allocates|frees|reads|writes|modifies|behavior|complete\s+behaviors|disjoint\s+behaviors|assumes|assert|check|admit|loop\s+invariant|loop\s+variant|loop\s+assigns|loop\s+allocates|decreases|terminates|exits|returns|breaks|continues)\s+([^;*]+?)(?:;|\*/)"s
    # Top-level ACSL declarations: lemmas, axioms, axiomatic blocks,
    # predicates, logic functions, ghost vars.
    acsl_decl_pat = r"(?:/\*@|//@)\s*(lemma|axiom|predicate|logic|inductive|type\s+invariant|ghost)\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*(?:\([^)]*\))?\s*(?::\s*([^;{*]+?))?(?:;|\{|\*/)"s
    # Named global ACSL assertion / check with label.
    acsl_named_pat = r"(?:/\*@|//@)\s*(?:assert|check)\s+([A-Za-z_][A-Za-z0-9_]*)\s*:\s*([^;*]+?);"s

    for f in c_files
        c = try
            read(f, String)
        catch
            continue
        end
        rel = relpath(f, DIR)
        matches = try
            collect(eachmatch(acsl_clause_pat, c))
        catch; Any[] end
        for m in matches
            body = first(strip(m.captures[2]), 800)
            isempty(body) && continue
            thm_name = "$(m.captures[1])_$(id)"
            push!(ps, Dict{String,Any}("id"=>id, "prover"=>"FramaC",
                "source_file"=>rel,
                "theorem"=>thm_name, "goal"=>body,
                "annotation_kind"=>strip(replace(m.captures[1], r"\s+"=>"_")),
                "context"=>Any[]))
            # Emit premises: C identifiers in ACSL clause body
            for hm in eachmatch(r"\b([a-zA-Z_][a-zA-Z0-9_]{1,40})\b", body)
                h = strip(hm.captures[1])
                !isempty(h) && length(h) < 50 && push!(pm, Dict{String,Any}(
                    "proof_id"=>id, "premise"=>h,
                    "prover"=>"FramaC", "theorem"=>thm_name, "source"=>"framac"))
            end
            id += 1
        end
        matches = try
            collect(eachmatch(acsl_decl_pat, c))
        catch; Any[] end
        for m in matches
            name = strip(m.captures[2])
            body = m.captures[3] === nothing ? "" : first(strip(m.captures[3]), 800)
            isempty(name) && continue
            push!(ps, Dict{String,Any}("id"=>id, "prover"=>"FramaC",
                "source_file"=>rel,
                "theorem"=>name, "goal"=>body,
                "annotation_kind"=>strip(replace(m.captures[1], r"\s+"=>"_")),
                "context"=>Any[]))
            id += 1
        end
        matches = try
            collect(eachmatch(acsl_named_pat, c))
        catch; Any[] end
        for m in matches
            name = strip(m.captures[1])
            body = first(strip(m.captures[2]), 800)
            (isempty(name) || isempty(body)) && continue
            push!(ps, Dict{String,Any}("id"=>id, "prover"=>"FramaC",
                "source_file"=>rel,
                "theorem"=>name, "goal"=>body,
                "annotation_kind"=>"named_assert",
                "context"=>Any[]))
            id += 1
        end
    end
    ps, ts, pm
end
function main(); println("ECHIDNA Frama-C Extraction"); println("=" ^ 26)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No annotations extracted.") : save_common(ps, ts, pm, "framac", START_ID, OUT) end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
