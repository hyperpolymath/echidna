#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract Alloy relational-model-finder constraints from alloytools examples.
# Vendor: git clone https://github.com/AlloyTools/models external_corpora/alloy
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/alloy"; const OUT = "training_data"; const START_ID = 2_700_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    if !isdir(DIR); println("Alloy not found: $DIR"); println("Clone: git clone https://github.com/AlloyTools/models external_corpora/alloy"); return ps, ts, pm; end
    als_files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs; endswith(f, ".als") && push!(als_files, joinpath(root, f)); end; end
    println("Found $(length(als_files)) .als files")
    # Widening (2026-04-18): was matching only `assert`. Alloy
    # vocabulary is much richer — fact, pred, fun, sig, check, run,
    # module / open are all named items worth indexing.
    assert_pat = r"assert\s+([A-Za-z0-9_]+)\s*\{([^}]+)\}"s
    fact_pat = r"fact\s+(?:([A-Za-z0-9_]+)\s*)?\{([^}]+)\}"s
    pred_pat = r"pred\s+([A-Za-z0-9_]+)\s*(?:\[[^\]]*\])?\s*\{([^}]+)\}"s
    fun_pat = r"fun\s+([A-Za-z0-9_]+)\s*(?:\[[^\]]*\])?\s*:\s*([^{]+?)\{"s
    sig_pat = r"(?:abstract\s+|one\s+|lone\s+|some\s+)*sig\s+([A-Za-z0-9_]+)\s*(?:extends\s+\w+|in\s+\w+)?\s*\{([^}]*)\}"s
    check_pat = r"check\s+([A-Za-z0-9_]+)\s*(?:for\s+[^\n]+)?"
    run_pat = r"run\s+([A-Za-z0-9_]+)\s*(?:for\s+[^\n]+)?"

    for f in als_files
        c = try
            read(f, String)
        catch
            continue
        end
        rel = relpath(f, DIR)
        seen = Set{String}()
        for (pat, kind) in ((assert_pat, "assert"),
                            (fact_pat, "fact"),
                            (pred_pat, "pred"),
                            (fun_pat, "fun"),
                            (sig_pat, "sig"),
                            (check_pat, "check"),
                            (run_pat, "run"))
            matches = try collect(eachmatch(pat, c)) catch; Any[] end
            for (i, m) in enumerate(matches)
                name_raw = m.captures[1] === nothing ? "" : strip(m.captures[1])
                name = isempty(name_raw) ? "$(kind)_$(i)" : name_raw
                goal = length(m.captures) >= 2 && m.captures[2] !== nothing ?
                       first(strip(m.captures[2]), 1000) : ""
                name_key = "$(kind):$(name)"
                name_key in seen && continue
                push!(seen, name_key)
                push!(ps, Dict{String,Any}("id"=>id, "prover"=>"Alloy",
                    "source_file"=>rel,
                    "theorem"=>name, "goal"=>goal,
                    "kind"=>kind, "context"=>Any[]))
                id += 1
            end
        end
    end
    ps, ts, pm
end
function main(); println("ECHIDNA Alloy Extraction"); println("=" ^ 24)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No assertions extracted.") : save_common(ps, ts, pm, "alloy", START_ID, OUT) end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
