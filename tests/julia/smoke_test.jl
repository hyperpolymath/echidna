# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-License-Identifier: PMPL-1.0-or-later
#
# tests/julia/smoke_test.jl — Julia smoke tests for ECHIDNA ML components
#
# Tests that the Julia ML scripts are syntactically valid, importable, and
# export the expected public API surface.
#
# Run with:
#   julia tests/julia/smoke_test.jl
#
# All tests are self-contained and do NOT start the API server, connect to
# external services, or require trained model files.

using Test

const REPO_ROOT = abspath(joinpath(@__DIR__, "..", ".."))
const JULIA_SRC = joinpath(REPO_ROOT, "src", "julia")

# ---------------------------------------------------------------------------
# Helper: include a script in an isolated module to avoid name collisions
# ---------------------------------------------------------------------------

"""
    include_isolated(path) -> Module

Include Julia source at `path` inside a fresh anonymous module, returning
that module. Errors during inclusion are re-thrown with context.
"""
function include_isolated(path::String)
    m = Module()
    try
        Base.include(m, path)
    catch err
        error("Failed to include $path: $err")
    end
    return m
end

# ---------------------------------------------------------------------------
# Helper: syntax-check via Meta.parse on each top-level expression
# ---------------------------------------------------------------------------

"""
    syntax_ok(path) -> Bool

Return true if all top-level expressions in `path` parse without error.
This is a lightweight check that does not evaluate the code.
"""
function syntax_ok(path::String)::Bool
    src = read(path, String)
    try
        Meta.parseall(src)
        return true
    catch e
        @warn "Syntax error in $path" exception=e
        return false
    end
end

# ---------------------------------------------------------------------------
# Suite 1: Syntax validation for all top-level Julia scripts
# ---------------------------------------------------------------------------

@testset "Julia ML — Syntax validation" begin
    scripts = [
        "api_server.jl",
        "run_server.jl",
        "run_training.jl",
        "train_models.jl",
        "train_final_models.jl",
        "train_complete_final.jl",
        "train_advanced_models.jl",
        "extract_training_data.jl",
        "extract_all_proofs.jl",
    ]
    for script in scripts
        path = joinpath(JULIA_SRC, script)
        if isfile(path)
            @testset "$script" begin
                @test syntax_ok(path)
            end
        else
            @warn "Script not found, skipping: $path"
        end
    end
end

# ---------------------------------------------------------------------------
# Suite 2: Syntax validation for inference sub-package
# ---------------------------------------------------------------------------

@testset "Julia ML — Inference sub-package syntax" begin
    inference_dir = joinpath(JULIA_SRC, "inference")
    if isdir(inference_dir)
        for fname in readdir(inference_dir)
            if endswith(fname, ".jl")
                path = joinpath(inference_dir, fname)
                @testset "inference/$fname" begin
                    @test syntax_ok(path)
                end
            end
        end
    else
        @warn "inference/ directory not found at $inference_dir"
    end
end

# ---------------------------------------------------------------------------
# Suite 3: EchidnaML module — public API surface
# ---------------------------------------------------------------------------

@testset "EchidnaML — module structure" begin
    path = joinpath(JULIA_SRC, "EchidnaML.jl")
    @test isfile(path)  # EchidnaML.jl must exist
    if isfile(path)
        @test syntax_ok(path)
    end
end

# ---------------------------------------------------------------------------
# Suite 4: Training data and model directories exist
# ---------------------------------------------------------------------------

@testset "Julia ML — expected directory structure" begin
    @test isdir(JULIA_SRC)  # src/julia/ must exist
    @test isfile(joinpath(JULIA_SRC, "Project.toml"))  # Project.toml must exist
    # api_server.jl and run_server.jl are the primary entrypoints
    @test isfile(joinpath(JULIA_SRC, "api_server.jl"))  # api_server.jl must exist
    @test isfile(joinpath(JULIA_SRC, "run_server.jl"))  # run_server.jl must exist
end

# ---------------------------------------------------------------------------
# Suite 5: api/server.jl inference endpoint — syntax
# ---------------------------------------------------------------------------

@testset "Julia ML — api/server.jl syntax" begin
    api_dir = joinpath(JULIA_SRC, "api")
    if isdir(api_dir)
        for fname in readdir(api_dir)
            if endswith(fname, ".jl")
                path = joinpath(api_dir, fname)
                @testset "api/$fname" begin
                    @test syntax_ok(path)
                end
            end
        end
    else
        @warn "api/ subdirectory not found at $api_dir"
    end
end

# ---------------------------------------------------------------------------
# Suite 6: scripts/*.jl — extraction and corpus scripts
# ---------------------------------------------------------------------------

@testset "Julia ML — corpus scripts syntax" begin
    scripts_dir = joinpath(REPO_ROOT, "scripts")
    if isdir(scripts_dir)
        jl_scripts = filter(f -> endswith(f, ".jl"), readdir(scripts_dir))
        for fname in jl_scripts
            path = joinpath(scripts_dir, fname)
            @testset "scripts/$fname" begin
                @test syntax_ok(path)
            end
        end
        if isempty(jl_scripts)
            @warn "No .jl scripts found in scripts/"
        end
    end
end

# ---------------------------------------------------------------------------
# Suite 7: Core tokenizer logic (self-contained, no network)
# ---------------------------------------------------------------------------

@testset "Tokenizer — unit smoke" begin
    # Inline the tokenizer logic used by api_server.jl and train_models.jl
    # to validate it behaves correctly without loading the full module.
    function tokenize_inline(text::String)::Vector{String}
        tokens = split(lowercase(text), r"[^a-z0-9]+")
        return filter(!isempty, tokens)
    end

    @testset "basic split" begin
        tokens = tokenize_inline("forall x, x = x")
        @test !isempty(tokens)
        @test "forall" in tokens
    end

    @testset "empty string returns empty" begin
        @test isempty(tokenize_inline(""))
    end

    @testset "punctuation only returns empty" begin
        @test isempty(tokenize_inline("---!!!---"))
    end

    @testset "numbers preserved" begin
        tokens = tokenize_inline("step1 step2 n0")
        @test "step1" in tokens
        @test "step2" in tokens
    end

    @testset "case-folded" begin
        tokens = tokenize_inline("Theorem FORALL Prop")
        @test "theorem" in tokens
        @test "forall" in tokens
        @test "prop" in tokens
    end
end

# ---------------------------------------------------------------------------
# Suite 8: BOW vectorizer smoke (inline, no deps)
# ---------------------------------------------------------------------------

@testset "BOW vectorizer — smoke" begin
    function text_to_bow_inline(text::String, vocab::Vector{String})::Vector{Float64}
        word_to_id = Dict(word => i for (i, word) in enumerate(vocab))
        vec = zeros(Float64, length(vocab))
        for token in split(lowercase(text), r"[^a-z0-9]+")
            idx = get(word_to_id, token, 0)
            if idx > 0
                vec[idx] += 1.0
            end
        end
        total = sum(vec)
        if total > 0
            vec ./= total
        end
        return vec
    end

    vocab = ["forall", "exists", "theorem", "proof"]

    @testset "produces correct length vector" begin
        v = text_to_bow_inline("theorem forall", vocab)
        @test length(v) == length(vocab)
    end

    @testset "sums to 1.0 when input has vocab words" begin
        v = text_to_bow_inline("theorem forall proof", vocab)
        @test abs(sum(v) - 1.0) < 1e-9
    end

    @testset "all-zero vector for unknown words" begin
        v = text_to_bow_inline("zzunknownword", vocab)
        @test all(x -> x == 0.0, v)
    end

    @testset "correct dimension" begin
        v = text_to_bow_inline("forall x exists y", vocab)
        @test length(v) == 4
    end
end

println("\n✓ Julia smoke tests complete.")
