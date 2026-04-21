#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
#
# Extract TypedWasm proof problems from ECHIDNA's own test fixtures and
# synthetic-fixture generation. TypedWasm is the in-process oracle for
# the 10-level type-safety system; its natural corpus is
# `tests/typed_wasm*.rs` (property-test definitions) and any `.twasm`
# fixtures we choose to snapshot.
#
# Per the-prover-story.txt: ML guidance needs ≥ 2K records. We combine:
#   1. 23 real proptest property declarations from tests/typed_wasm_properties.rs
#   2. A further N synthetic .twasm programs generated via the same
#      schema (region / field / type grammar) the proptests sample from.
#
# Output:
#   training_data/proof_states_typed_wasm.jsonl
#   training_data/stats_typed_wasm.json
#
# ID range: 1_700_000+

using JSON3
using Dates
include("extractor_save_common.jl")

const REPO_ROOT = dirname(dirname(abspath(@__FILE__)))
const TESTS_DIR = joinpath(REPO_ROOT, "tests")
const OUT = joinpath(REPO_ROOT, "training_data")
const START_ID = 1_700_000
const SYNTHETIC_TARGET = 2400  # Enough to push past the 2K ML threshold

# ---------------------------------------------------------------------------
# Extract proptest property declarations from typed_wasm*.rs
# ---------------------------------------------------------------------------

"""
    extract_proptest_properties(path) -> Vector{Dict{String,Any}}

Parse a Rust proptest file and return one record per `#[test] fn NAME`
declaration inside a `proptest! { ... }` block.
"""
function extract_proptest_properties(path::AbstractString)::Vector{Dict{String,Any}}
    out = Dict{String,Any}[]
    content = try
        read(path, String)
    catch
        return out
    end

    # Match `#[test] fn NAME( ARGS ) { BODY }` blocks. Body may span
    # multiple lines and contain nested braces; rely on `prop_assert!`
    # / `assert!` / `return` as sentinel-enders for sanity.
    pat = r"#\[test\]\s*fn\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(([^)]*)\)\s*\{([^{}]*(?:\{[^{}]*\}[^{}]*)*)\}"s
    matches = try collect(eachmatch(pat, content)) catch; Any[] end
    for m in matches
        name = strip(String(m.captures[1]))
        args = strip(String(m.captures[2]))
        body = first(strip(String(m.captures[3])), 1500)
        isempty(name) && continue
        push!(out, Dict{String,Any}(
            "theorem" => name,
            "goal" => isempty(args) ? body : "fn $(name)($(args)) — $(body)",
            "kind" => "proptest_property",
            "args" => args,
            "source_file" => relpath(path, REPO_ROOT),
        ))
    end
    return out
end

# ---------------------------------------------------------------------------
# Synthesise .twasm fixtures via the proptest schema
# ---------------------------------------------------------------------------

const WASM_TYPES = ["i32", "i64", "f32", "f64", "v128"]

"""
    synth_field_name(rng_seed) -> String

Generate a lowercase alphanumeric identifier matching `[a-z][a-z0-9]{2,7}`.
"""
function synth_field_name(rng)::String
    len = rand(rng, 3:8)
    first_ch = rand(rng, 'a':'z')
    rest = String(rand(rng, ['a':'z'; '0':'9'], len - 1))
    return string(first_ch) * rest
end

"""
    synth_field(rng) -> String

One field declaration: `name: type`.
"""
synth_field(rng)::String = "$(synth_field_name(rng)): $(rand(rng, WASM_TYPES))"

"""
    synth_schema_body(rng) -> String

Between 1 and 5 field declarations separated by `; `.
"""
function synth_schema_body(rng)::String
    nfields = rand(rng, 1:5)
    return join([synth_field(rng) for _ in 1:nfields], "; ")
end

"""
    synth_twasm_program(rng) -> String

Full single-region .twasm program: `region NAME { body } [COUNT]`.
"""
function synth_twasm_program(rng)::String
    name = synth_field_name(rng)  # region name is lowercase too
    body = synth_schema_body(rng)
    count = rand(rng, 1:99)
    return "region $(name) { $(body) } [$(count)]"
end

"""
    synth_twasm_invalid(rng) -> String

A program that *should* fail the type-soundness check — used as the
negative-class for training (deliberately wrong field-type pair).
"""
function synth_twasm_invalid(rng)::String
    name = synth_field_name(rng)
    body = synth_schema_body(rng)
    # Inject an undeclared-field reference, which breaks soundness.
    undeclared = synth_field_name(rng)
    return "region $(name) { $(body) } [1]; region.get $(name)[0] .$(undeclared)"
end

# ---------------------------------------------------------------------------
# Pipeline
# ---------------------------------------------------------------------------

function run_extract()
    ps, ts, pm = Dict{String,Any}[], Dict{String,Any}[], Dict{String,Any}[]
    id = START_ID

    # 1. Pull real proptest property declarations.
    rs_files = String[]
    if isdir(TESTS_DIR)
        for (root, _, files) in walkdir(TESTS_DIR)
            for f in files
                (startswith(f, "typed_wasm") && endswith(f, ".rs")) &&
                    push!(rs_files, joinpath(root, f))
            end
        end
    end
    println("Found $(length(rs_files)) typed_wasm*.rs test files")
    real_count = 0
    for f in rs_files
        for rec in extract_proptest_properties(f)
            rec["id"] = id
            rec["prover"] = "TypedWasm"
            push!(ps, rec)
            # Emit premises: Rust identifiers from proptest goal/args
            goal_text = get(rec, "goal", "")
            for hm in eachmatch(r"\b([a-zA-Z_][a-zA-Z0-9_]{1,40})\b", goal_text)
                h = strip(hm.captures[1])
                !isempty(h) && length(h) < 50 && push!(pm, Dict{String,Any}(
                    "proof_id"=>id, "premise"=>h,
                    "prover"=>"TypedWasm", "theorem"=>rec["theorem"], "source"=>"typed_wasm"))
            end
            id += 1
            real_count += 1
        end
    end
    println("  extracted $(real_count) proptest properties")

    # 2. Snapshot any `.twasm` fixtures we already have on disk.
    fixture_count = 0
    for (root, _, files) in walkdir(REPO_ROOT)
        for f in files
            endswith(f, ".twasm") || continue
            fp = joinpath(root, f)
            c = try
                read(fp, String)
            catch
                continue
            end
            push!(ps, Dict{String,Any}(
                "id" => id, "prover" => "TypedWasm",
                "source_file" => relpath(fp, REPO_ROOT),
                "theorem" => basename(fp),
                "goal" => first(c, 800),
                "kind" => "fixture",
                "context" => Any[],
            ))
            id += 1
            fixture_count += 1
        end
    end
    println("  extracted $(fixture_count) .twasm fixtures")

    # 3. Synthesise enough programs to clear the 2K ML threshold.
    # Seed determinism: the stats file captures the seed so reruns
    # produce the same corpus.
    needed = max(0, SYNTHETIC_TARGET - real_count - fixture_count)
    if needed > 0
        rng = MersenneTwister(20260418)
        # Split: 85% valid programs, 15% invalid (negative class).
        for i in 1:needed
            is_invalid = rand(rng) < 0.15
            program = is_invalid ? synth_twasm_invalid(rng) : synth_twasm_program(rng)
            push!(ps, Dict{String,Any}(
                "id" => id, "prover" => "TypedWasm",
                "source_file" => "synthetic/typed_wasm_$(i).twasm",
                "theorem" => "synth_$(lpad(i, 5, '0'))",
                "goal" => program,
                "kind" => is_invalid ? "synthetic_invalid" : "synthetic_valid",
                "expected" => is_invalid ? "reject" : "accept",
                "context" => Any[],
            ))
            id += 1
        end
        println("  synthesised $(needed) programs (seed 20260418)")
    end

    return ps, ts, pm
end

using Random

function main()
    println("ECHIDNA TypedWasm Extraction (real + synthetic)")
    println("=" ^ 48)
    ps, ts, pm = run_extract()
    if isempty(ps)
        println("No records produced.")
        return
    end
    save_common(ps, ts, pm, "typed_wasm", START_ID, OUT)
end

if abspath(PROGRAM_FILE) == abspath(@__FILE__)
    main()
end
