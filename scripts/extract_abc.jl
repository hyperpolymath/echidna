#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract ABC hardware-verification problems (AIGER / BLIF).
# Vendor: git clone https://github.com/berkeley-abc/abc external_corpora/abc
using JSON3, Dates
include("extractor_save_common.jl")
const DIR = "external_corpora/abc"; const OUT = "training_data"; const START_ID = 3_100_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    # Widening (2026-04-18): walk both the ABC source repo and any
    # sibling hardware-benchmark corpora (hwmcc20, hwmcc24).
    roots = String[]
    isdir(DIR) && push!(roots, DIR)
    for sibling in ("hwmcc20", "hwmcc24")
        p = joinpath(dirname(DIR), sibling)
        isdir(p) && push!(roots, p)
    end
    if isempty(roots)
        println("ABC / HWMCC corpora not found.")
        println("Clone: git clone https://github.com/berkeley-abc/abc $DIR")
        return ps, ts, pm
    end
    hw_files = String[]
    for root in roots
        for (rr, _, fs) in walkdir(root)
            for f in fs
                # AIG variants (binary + ASCII), BLIF, Bench, Btor2.
                if endswith(f, ".aig") || endswith(f, ".aag") ||
                   endswith(f, ".blif") || endswith(f, ".bench") ||
                   endswith(f, ".btor") || endswith(f, ".btor2")
                    push!(hw_files, joinpath(rr, f))
                end
            end
        end
    end
    println("Found $(length(hw_files)) hardware files across $(length(roots)) root(s)")
    for f in hw_files
        try
            sz = filesize(f)
            push!(ps, Dict{String,Any}("id"=>id, "prover"=>"ABC",
                "source_file"=>relpath(f, dirname(DIR)),
                "theorem"=>basename(f),
                "goal"=>"$(splitext(f)[2][2:end])_circuit size=$(sz)",
                "kind"=>splitext(f)[2][2:end],
                "context"=>Any[]))
            id += 1
        catch e; println("Warning: $f: $e"); end
    end
    ps, ts, pm
end
function main(); println("ECHIDNA ABC Extraction"); println("=" ^ 22)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No circuits extracted.") : save_common(ps, ts, pm, "abc", START_ID, OUT) end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
