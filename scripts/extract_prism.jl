#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract PRISM probabilistic model-checker properties.
# Vendor: git clone https://github.com/prismmodelchecker/prism-examples external_corpora/prism
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/prism"; const OUT = "training_data"; const START_ID = 2_800_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    if !isdir(DIR); println("PRISM examples not found: $DIR"); println("Clone: git clone https://github.com/prismmodelchecker/prism-examples $DIR"); return ps, ts, pm; end
    # Widening (2026-04-18): also walk model files (.prism, .sm, .nm,
    # .pm) — PRISM models define the actual state machines that
    # properties quantify over. Each has named modules, formulas,
    # constants, rewards worth indexing.
    all_files = String[]
    for (root, _, fs) in walkdir(DIR)
        for f in fs
            if endswith(f, ".pctl") || endswith(f, ".props") ||
               endswith(f, ".csl") || endswith(f, ".prism") ||
               endswith(f, ".sm") || endswith(f, ".nm") ||
               endswith(f, ".pm") || endswith(f, ".smg")
                push!(all_files, joinpath(root, f))
            end
        end
    end
    println("Found $(length(all_files)) PRISM property/model files")

    prop_pat = r"(P|S|R|Pmax|Pmin|Rmax|Rmin)\s*(?:=\?|>=\s*[0-9.]+|<=\s*[0-9.]+|<\s*[0-9.]+|>\s*[0-9.]+)\s*\[\s*(.+?)\s*\]"s
    named_prop_pat = r"\"([A-Za-z_][A-Za-z0-9_]*)\"\s*:\s*(.+?)(?:;|$)"m
    module_pat = r"module\s+([A-Za-z_][A-Za-z0-9_]*)\s*(.*?)\s*endmodule"s
    formula_pat = r"formula\s+([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.+?)\s*;"s
    const_pat = r"const\s+(?:int|double|bool)?\s*([A-Za-z_][A-Za-z0-9_]*)\s*(?:=\s*(.+?))?\s*;"s
    reward_pat = r"rewards\s+(?:\"([A-Za-z_][A-Za-z0-9_]*)\")?\s*(.*?)\s*endrewards"s

    for f in all_files
        c = try
            read(f, String)
        catch
            continue
        end
        rel = relpath(f, DIR)
        matches = try collect(eachmatch(prop_pat, c)) catch; Any[] end
        for m in matches
            goal = first(strip(String(m.captures[2])), 600)
            isempty(goal) && continue
            push!(ps, Dict{String,Any}("id"=>id, "prover"=>"Prism",
                "source_file"=>rel,
                "theorem"=>"prob_$(id)", "goal"=>goal,
                "kind"=>"property", "operator"=>String(m.captures[1]),
                "context"=>Any[]))
            # Emit premises: identifiers from property formula
            for hm in eachmatch(r"\b([A-Za-z_][A-Za-z0-9_]{1,40})\b", goal)
                h = strip(hm.captures[1])
                !isempty(h) && length(h) < 50 && push!(pm, Dict{String,Any}(
                    "proof_id"=>id, "premise"=>h,
                    "prover"=>"Prism", "theorem"=>"prob_$(id)", "source"=>"prism"))
            end
            id += 1
        end
        for (pat, kind) in ((named_prop_pat, "named_property"),
                            (formula_pat, "formula"),
                            (const_pat, "const"),
                            (module_pat, "module"),
                            (reward_pat, "reward"))
            matches = try collect(eachmatch(pat, c)) catch; Any[] end
            for m in matches
                name_raw = m.captures[1] === nothing ? "" : strip(String(m.captures[1]))
                name = isempty(name_raw) ? "$(kind)_$(id)" : name_raw
                goal = length(m.captures) >= 2 && m.captures[2] !== nothing ?
                       first(strip(String(m.captures[2])), 600) : ""
                push!(ps, Dict{String,Any}("id"=>id, "prover"=>"Prism",
                    "source_file"=>rel,
                    "theorem"=>name, "goal"=>goal, "kind"=>kind,
                    "context"=>Any[]))
                # Emit premises: identifiers from module/formula body
                for hm in eachmatch(r"\b([A-Za-z_][A-Za-z0-9_]{1,40})\b", goal)
                    h = strip(hm.captures[1])
                    !isempty(h) && length(h) < 50 && push!(pm, Dict{String,Any}(
                        "proof_id"=>id, "premise"=>h,
                        "prover"=>"Prism", "theorem"=>name, "source"=>"prism"))
                end
                id += 1
            end
        end
    end
    ps, ts, pm
end
function main(); println("ECHIDNA PRISM Extraction"); println("=" ^ 24)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No properties extracted.") : save_common(ps, ts, pm, "prism", START_ID, OUT) end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
