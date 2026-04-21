#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract proofs / declarations / .nun files from Nunchaku (refutation finder).
# Vendor location: external_corpora/nunchaku/
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/nunchaku"
const OUT = "training_data"
const START_ID = 3_900_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    # Widening (2026-04-18): Nunchaku is another Isabelle-embedded
    # refutation finder. Its natural corpus is Isabelle .thy files
    # that invoke `nunchaku`. Walk AFP in addition to any dedicated
    # nunchaku corpus.
    roots = String[]
    isdir(DIR) && push!(roots, DIR)
    afp_root = joinpath(dirname(DIR), "afp")
    isdir(afp_root) && push!(roots, afp_root)
    if isempty(roots)
        println("No Nunchaku-bearing corpus found.")
        println("Vendor external_corpora/afp (recommended) or external_corpora/nunchaku.")
        return ps, ts, pm
    end

    files = String[]
    for root in roots
        for (rr, _, fs) in walkdir(root)
            for f in fs
                (endswith(f, ".thy") || endswith(f, ".nun")) &&
                    push!(files, joinpath(rr, f))
            end
        end
    end
    println("Found $(length(files)) Nunchaku-bearing files across $(length(roots)) root(s)")

    # Native .nun goal syntax.
    nun_pat = r"goal\s+([A-Za-z0-9_]+)\s*:\s*(.*?)\s*\."s
    # Isabelle invocation of Nunchaku.
    call_pat = r"(nunchaku|nunchaku_params)(?:\s*\[([^\]]*)\])?"s
    lemma_before_pat = r"(?:lemma|theorem|corollary)\s+([A-Za-z0-9_']+)\s*(?:\[[^\]]*\])?\s*:\s*(?:\"([^\"]*)\"|\`([^\`]*)\`)"s

    for f in files
        c = try
            read(f, String)
        catch
            continue
        end
        rel = relpath(f, dirname(DIR))
        if endswith(f, ".nun")
            matches = try collect(eachmatch(nun_pat, c)) catch; Any[] end
            for m in matches
                n = m.captures[1] === nothing ? "" : strip(String(m.captures[1]))
                g = m.captures[2] === nothing ? "" : first(strip(String(m.captures[2])), 800)
                isempty(n) && continue
                push!(ps, Dict{String,Any}("id"=>id, "prover"=>"nunchaku",
                    "source_file"=>rel, "theorem"=>n, "goal"=>g,
                    "kind"=>"goal", "context"=>Any[]))
                # Emit premises: identifiers from goal body
                for hm in eachmatch(r"\b([A-Za-z][A-Za-z0-9_']{1,40})\b", g)
                    h = strip(hm.captures[1])
                    !isempty(h) && length(h) < 50 && push!(pm, Dict{String,Any}(
                        "proof_id"=>id, "premise"=>h,
                        "prover"=>"nunchaku", "theorem"=>n, "source"=>"nunchaku"))
                end
                id += 1
            end
        else
            # .thy — scan for nunchaku invocations with preceding lemma.
            lemma_locs = Tuple{Int,String,String}[]
            lemma_matches = try collect(eachmatch(lemma_before_pat, c)) catch; Any[] end
            for lm in lemma_matches
                name = strip(String(lm.captures[1]))
                body_raw = lm.captures[2] !== nothing ? String(lm.captures[2]) :
                           lm.captures[3] !== nothing ? String(lm.captures[3]) : ""
                push!(lemma_locs, (lm.offset, name, body_raw))
            end
            sort!(lemma_locs, by = x -> x[1])
            call_matches = try collect(eachmatch(call_pat, c)) catch; Any[] end
            for (i, m) in enumerate(call_matches)
                kind = strip(String(m.captures[1]))
                opts = m.captures[2] === nothing ? "" : strip(String(m.captures[2]))
                lemma_name = ""; lemma_body = ""
                for (off, name, body) in lemma_locs
                    off < m.offset || break
                    lemma_name = name; lemma_body = body
                end
                theorem = isempty(lemma_name) ? "$(kind)_$(i)" : "$(lemma_name)_$(kind)"
                push!(ps, Dict{String,Any}("id"=>id, "prover"=>"nunchaku",
                    "source_file"=>rel, "theorem"=>theorem,
                    "goal"=>first(lemma_body, 600),
                    "opts"=>opts, "kind"=>kind, "context"=>Any[]))
                # Emit premises: Isabelle identifiers from lemma body
                for hm in eachmatch(r"\b([A-Za-z][A-Za-z0-9_']{1,40})\b", lemma_body)
                    h = strip(hm.captures[1])
                    !isempty(h) && length(h) < 50 && push!(pm, Dict{String,Any}(
                        "proof_id"=>id, "premise"=>h,
                        "prover"=>"nunchaku", "theorem"=>theorem, "source"=>"nunchaku"))
                end
                id += 1
            end
        end
    end
    ps, ts, pm
end
function main()
    println("ECHIDNA Nunchaku (refutation finder) Extraction"); println("=" ^ 40)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No records extracted.") : save_common(ps, ts, pm, "nunchaku", START_ID, OUT)
end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
