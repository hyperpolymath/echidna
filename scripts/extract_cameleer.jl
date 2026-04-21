#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# Extract proofs from Cameleer examples (OCaml with GOSPEL contracts).
# Vendor: https://github.com/ocaml-gospel/cameleer — examples/ directory.

using JSON3, Dates

const CAMELEER_DIR = "external_corpora/cameleer"
const OUTPUT_DIR = "training_data"
const PROOF_STATES_FILE = joinpath(OUTPUT_DIR, "proof_states_cameleer.jsonl")
const TACTICS_FILE = joinpath(OUTPUT_DIR, "tactics_cameleer.jsonl")
const PREMISES_FILE = joinpath(OUTPUT_DIR, "premises_cameleer.jsonl")
const STATS_FILE = joinpath(OUTPUT_DIR, "stats_cameleer.json")
const START_ID = 800_000

function extract_cameleer_proofs()
    proof_states = Dict{String,Any}[]
    tactics = Dict{String,Any}[]
    premises = Dict{String,Any}[]
    current_id = START_ID

    # Widening (2026-04-18): previous extractor walked only
    # cameleer/examples/ and matched only the `let NAME ... (*@ SPEC *)`
    # pattern. We now walk the whole clone and additionally capture
    # GOSPEL annotations attached to val / type / ghost declarations,
    # and any standalone GOSPEL comment block (which carries real
    # specification content even outside OCaml definitions).
    if !isdir(CAMELEER_DIR)
        println("Cameleer clone not found: $CAMELEER_DIR")
        println("Clone: git clone https://github.com/ocaml-gospel/cameleer $CAMELEER_DIR")
        return proof_states, tactics, premises
    end

    src_files = String[]
    for (root, _, files) in walkdir(CAMELEER_DIR)
        for f in files
            if endswith(f, ".ml") || endswith(f, ".mli") ||
               endswith(f, ".gospel")
                push!(src_files, joinpath(root, f))
            end
        end
    end
    println("Found $(length(src_files)) Cameleer / GOSPEL source files")

    fn_pat = r"let\s+(?:rec\s+)?([a-zA-Z0-9_']+)\s+([^=]*?)=\s*(.*?)\s*\(\*@\s*(.*?)\s*\*\)"s
    val_pat = r"val\s+([a-zA-Z0-9_']+)\s*:\s*([^(]+?)\s*(?:\(\*@\s*(.*?)\s*\*\))?"s
    type_pat = r"type\s+([a-zA-Z0-9_']+)\s+(?:[^=]*?=\s*([^(]+?))?\s*(?:\(\*@\s*(.*?)\s*\*\))"s
    standalone_pat = r"\(\*@\s*(requires|ensures|modifies|consumes|invariant|variant|raises|diverges|equivalent)\s+(.+?)\s*\*\)"s

    # Cameleer/GOSPEL premise patterns: requires/ensures identifiers
    cameleer_hyp_pat = r"\b(requires|ensures|modifies|invariant|variant)\s+([a-zA-Z][a-zA-Z0-9_']*)\b"

    for f in src_files
        content = try
            read(f, String)
        catch
            continue
        end
        rel = relpath(f, CAMELEER_DIR)
        matches = try collect(eachmatch(fn_pat, content)) catch; Any[] end
        for m in matches
            name = strip(String(m.captures[1]))
            spec = first(strip(String(m.captures[4])), 600)
            (isempty(name) || isempty(spec)) && continue
            push!(proof_states, Dict{String,Any}(
                "id" => current_id, "prover" => "Cameleer",
                "source_file" => rel,
                "theorem" => name, "goal" => spec,
                "kind" => "let_spec", "context" => Any[]))
            for hm in eachmatch(cameleer_hyp_pat, spec)
                h = strip(hm.captures[2])
                !isempty(h) && length(h) < 50 && push!(premises, Dict{String,Any}(
                    "proof_id"=>current_id, "premise"=>h,
                    "prover"=>"Cameleer", "theorem"=>name, "source"=>"cameleer"))
            end
            current_id += 1
        end
        for (pat, kind) in ((val_pat, "val"), (type_pat, "type"))
            matches = try collect(eachmatch(pat, content)) catch; Any[] end
            for m in matches
                name = strip(String(m.captures[1]))
                sig = m.captures[2] === nothing ? "" : first(strip(String(m.captures[2])), 300)
                spec_idx = kind == "val" ? 3 : 3
                spec = length(m.captures) >= spec_idx && m.captures[spec_idx] !== nothing ?
                       first(strip(String(m.captures[spec_idx])), 600) : ""
                isempty(name) && continue
                # Skip if neither signature nor spec.
                (isempty(sig) && isempty(spec)) && continue
                push!(proof_states, Dict{String,Any}(
                    "id" => current_id, "prover" => "Cameleer",
                    "source_file" => rel,
                    "theorem" => name,
                    "goal" => isempty(spec) ? sig : spec,
                    "signature" => sig,
                    "kind" => kind, "context" => Any[]))
                current_id += 1
            end
        end
        matches = try collect(eachmatch(standalone_pat, content)) catch; Any[] end
        for (i, m) in enumerate(matches)
            kind = strip(String(m.captures[1]))
            body = first(strip(String(m.captures[2])), 400)
            isempty(body) && continue
            push!(proof_states, Dict{String,Any}(
                "id" => current_id, "prover" => "Cameleer",
                "source_file" => rel,
                "theorem" => "$(kind)_$(i)", "goal" => body,
                "kind" => kind, "context" => Any[]))
            current_id += 1
        end
    end
    return proof_states, tactics, premises
end

function save_extracted_data(ps, ts, pm)
    mkpath(OUTPUT_DIR)
    open(PROOF_STATES_FILE, "w") do f; for s in ps; println(f, JSON3.write(s)); end; end
    open(TACTICS_FILE, "w") do f; for t in ts; println(f, JSON3.write(t)); end; end
    open(PREMISES_FILE, "w") do f; for p in pm; println(f, JSON3.write(p)); end; end
    stats = Dict{String,Any}(
        "source" => "ocaml-gospel/cameleer examples",
        "prover" => "Cameleer", "extraction_date" => string(Dates.today()),
        "proof_states_count" => length(ps), "tactics_count" => length(ts),
        "premises_count" => length(pm), "start_id" => START_ID,
        "end_id" => isempty(ps) ? START_ID : START_ID + length(ps) - 1)
    open(STATS_FILE, "w") do f; JSON3.pretty(f, stats); end
    println("Saved $(length(ps)) proof states")
end

function main()
    println("ECHIDNA Cameleer (OCaml/GOSPEL) Extraction"); println("=" ^ 44)
    ps, ts, pm = extract_cameleer_proofs()
    isempty(ps) ? println("No proofs extracted.") : save_extracted_data(ps, ts, pm)
end

if abspath(PROGRAM_FILE) == @__FILE__; main(); end
