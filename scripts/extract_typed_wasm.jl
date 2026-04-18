#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Extract TypedWasm proof problems from echidna's own test fixtures
# (internal oracle — source lives here, not external). Runs against
# `tests/typed_wasm_properties.rs` and any `.twasm` fixtures.
using JSON3, Dates
include("extractor_save_common.jl")
const FIXTURES_DIR = "tests"; const OUT = "training_data"; const START_ID = 1_700_000
function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]; id = START_ID
    twasm_files = String[]
    for (root, _, fs) in walkdir(".")
        for f in fs
            endswith(f, ".twasm") && push!(twasm_files, joinpath(root, f))
        end
    end
    println("Found $(length(twasm_files)) .twasm fixtures")
    if isempty(twasm_files)
        println("No TypedWasm fixtures found; see tests/ for property-test inputs.")
    end
    for f in twasm_files
        try
            c = read(f, String)
            push!(ps, Dict{String,Any}("id"=>id, "prover"=>"TypedWasm",
                "source_file"=>f, "theorem"=>basename(f),
                "goal"=>first(c, 512), "context"=>Any[]))
            id += 1
        catch e; println("Warning: $f: $e"); end
    end
    ps, ts, pm
end
function main(); println("ECHIDNA TypedWasm Extraction"); println("=" ^ 28)
    ps, ts, pm = run_extract()
    isempty(ps) ? println("No fixtures extracted.") : save_common(ps, ts, pm, "typed_wasm", START_ID, OUT) end
if abspath(PROGRAM_FILE) == @__FILE__; main(); end
