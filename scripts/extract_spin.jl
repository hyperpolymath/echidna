#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract SPIN model-checker LTL properties from Promela models.
# Vendor: https://spinroot.com/spin/Examples or nimble-code/Spin
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/spin"; const OUT = "training_data"; const START_ID = 2_000_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    if !isdir(DIR); println("SPIN examples not found: $DIR"); println("Clone: git clone https://github.com/nimble-code/Spin $DIR"); return ps, ts, pm; end
    pml_files = String[]
    for (root, _, fs) in walkdir(DIR); for f in fs; (endswith(f, ".pml") || endswith(f, ".prom") || endswith(f, ".promela")) && push!(pml_files, joinpath(root, f)); end; end
    println("Found $(length(pml_files)) Promela files")
    # Widening (2026-04-18): Promela has more nameable items than ltl.
    ltl_pat = r"ltl\s+([A-Za-z0-9_]+)\s*\{\s*(.*?)\s*\}"s
    proc_pat = r"(?:active\s+(?:\[[^\]]*\]\s+)?)?proctype\s+([A-Za-z_][A-Za-z0-9_]*)\s*\([^)]*\)\s*\{"
    init_pat = r"init\s*(?:\{|\()"
    inline_pat = r"inline\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(([^)]*)\)"
    mtype_pat = r"mtype\s*(?::\s*(\w+))?\s*=\s*\{([^}]+)\}"
    define_pat = r"#define\s+([A-Z_][A-Z_0-9]*)\s+(.+?)$"m
    assert_pat = r"assert\s*\(([^;]+?)\)\s*;"

    for f in pml_files
        c = try
            read(f, String)
        catch
            continue
        end
        rel = relpath(f, DIR)
        for (pat, kind) in ((ltl_pat, "ltl"),
                            (inline_pat, "inline"),
                            (mtype_pat, "mtype"),
                            (define_pat, "define"))
            matches = try collect(eachmatch(pat, c)) catch; Any[] end
            for (i, m) in enumerate(matches)
                name_raw = m.captures[1] === nothing ? "" : String(m.captures[1])
                name = strip(name_raw)
                isempty(name) && (name = "$(kind)_$(i)")
                goal = length(m.captures) >= 2 && m.captures[2] !== nothing ?
                       first(strip(String(m.captures[2])), 800) : ""
                push!(ps, Dict{String,Any}("id"=>id, "prover"=>"SPIN",
                    "source_file"=>rel, "theorem"=>name,
                    "goal"=>goal, "kind"=>kind, "context"=>Any[]))
                # Emit premises: identifiers from LTL/inline/mtype/define body
                for hm in eachmatch(r"\b([A-Za-z_][A-Za-z0-9_]{1,40})\b", goal)
                    h = strip(hm.captures[1])
                    !isempty(h) && length(h) < 50 && push!(pm, Dict{String,Any}(
                        "proof_id"=>id, "premise"=>h,
                        "prover"=>"SPIN", "theorem"=>name, "source"=>"spin"))
                end
                id += 1
            end
        end
        # proctype and init need custom handling since the regex
        # captures the name only.
        matches = try collect(eachmatch(proc_pat, c)) catch; Any[] end
        for m in matches
            name = strip(String(m.captures[1]))
            isempty(name) && continue
            push!(ps, Dict{String,Any}("id"=>id, "prover"=>"SPIN",
                "source_file"=>rel, "theorem"=>name,
                "goal"=>"proctype $(name)", "kind"=>"proctype",
                "context"=>Any[]))
            id += 1
        end
        if match(init_pat, c) !== nothing
            push!(ps, Dict{String,Any}("id"=>id, "prover"=>"SPIN",
                "source_file"=>rel, "theorem"=>"init",
                "goal"=>"init block", "kind"=>"init",
                "context"=>Any[]))
            id += 1
        end
        matches = try collect(eachmatch(assert_pat, c)) catch; Any[] end
        for (i, m) in enumerate(matches)
            body = first(strip(String(m.captures[1])), 400)
            isempty(body) && continue
            push!(ps, Dict{String,Any}("id"=>id, "prover"=>"SPIN",
                "source_file"=>rel, "theorem"=>"assert_$(i)",
                "goal"=>body, "kind"=>"assert",
                "context"=>Any[]))
            id += 1
        end
    end
    ps, ts, pm
end
function main(); println("ECHIDNA SPIN Extraction"); println("=" ^ 23)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No LTL properties extracted.") : save_common(ps, ts, pm, "spin", START_ID, OUT) end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
