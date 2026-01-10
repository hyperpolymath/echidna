# SPDX-FileCopyrightText: 2025 ECHIDNA Project Team
# SPDX-License-Identifier: MIT AND Palimpsest-0.6

"""
    test_server.jl

Minimal test server for Rust↔Julia integration testing.
Provides mock endpoints that don't require trained models.
"""

using Oxygen
using HTTP
using JSON3
using Logging
using Dates

# ============================================================================
# Mock Server State
# ============================================================================

mutable struct MockServerState
    request_count::Int
    start_time::DateTime
end

const MOCK_STATE = Ref{MockServerState}()

function init_mock_state()
    MOCK_STATE[] = MockServerState(0, now())
end

# ============================================================================
# Mock Endpoints
# ============================================================================

@get "/health" function(req::HTTP.Request)
    state = MOCK_STATE[]
    uptime = (now() - state.start_time).value / 1000

    return JSON3.write(Dict(
        "status" => "healthy",
        "model_loaded" => true,
        "uptime_seconds" => uptime,
        "request_count" => state.request_count
    ))
end

@get "/provers" function(req::HTTP.Request)
    return JSON3.write(Dict(
        "tier1" => ["agda", "coq", "rocq", "lean", "isabelle", "z3", "cvc5"],
        "tier2" => ["metamath", "hol_light", "mizar"],
        "tier3" => ["pvs", "acl2"],
        "tier4" => ["hol4"],
        "total" => 13
    ))
end

@post "/predict" function(req::HTTP.Request)
    state = MOCK_STATE[]
    state.request_count += 1

    try
        body = JSON3.read(String(req.body))

        # Mock response with synthetic premises
        mock_premises = [
            Dict("name" => "lemma_1", "statement" => "∀x. P(x) → Q(x)", "score" => 0.95),
            Dict("name" => "lemma_2", "statement" => "∀x. Q(x) → R(x)", "score" => 0.87),
            Dict("name" => "axiom_1", "statement" => "∀x. x = x", "score" => 0.72),
        ]

        response = Dict(
            "success" => true,
            "premises" => mock_premises,
            "scores" => [0.95, 0.87, 0.72],
            "confidence" => 0.85,
            "prover" => get(body, "prover", "unknown"),
            "cached" => false,
            "inference_time_ms" => 12.5
        )

        return JSON3.write(response)
    catch e
        return HTTP.Response(500, JSON3.write(Dict(
            "success" => false,
            "error" => string(e),
            "error_type" => string(typeof(e))
        )))
    end
end

@post "/suggest" function(req::HTTP.Request)
    state = MOCK_STATE[]
    state.request_count += 1

    try
        body = JSON3.read(String(req.body))

        # Mock suggestion response
        mock_premises = [
            Dict("name" => "apply_lemma", "statement" => "apply P_implies_Q", "score" => 0.92),
            Dict("name" => "intro_x", "statement" => "intro x", "score" => 0.85),
            Dict("name" => "rewrite_def", "statement" => "rewrite definition", "score" => 0.78),
        ]

        response = Dict(
            "success" => true,
            "premises" => mock_premises,
            "scores" => [0.92, 0.85, 0.78],
            "confidence" => 0.88,
            "prover" => get(body, "prover", "unknown"),
            "inference_time_ms" => 8.3,
            "diversity_applied" => get(body, "use_diversity", false),
            "uncertainty_estimated" => get(body, "estimate_uncertainty", false)
        )

        return JSON3.write(response)
    catch e
        return HTTP.Response(500, JSON3.write(Dict(
            "success" => false,
            "error" => string(e),
            "error_type" => string(typeof(e))
        )))
    end
end

# ============================================================================
# Server Management
# ============================================================================

"""
    start_test_server(; port::Int=8081, host::String="127.0.0.1")

Start the mock test server for integration testing.
"""
function start_test_server(; port::Int=8081, host::String="127.0.0.1")
    @info "Starting ECHIDNA Test Server"
    @info "Host: $host:$port"

    init_mock_state()

    @info "Test server ready - listening on http://$host:$port"
    @info "Endpoints:"
    @info "  GET  /health   - Health check"
    @info "  GET  /provers  - List supported provers"
    @info "  POST /predict  - Mock premise prediction"
    @info "  POST /suggest  - Mock suggestion"

    serve(host=host, port=port, async=false)
end

# Run if executed directly
if abspath(PROGRAM_FILE) == @__FILE__
    port = length(ARGS) > 0 ? parse(Int, ARGS[1]) : 8081
    start_test_server(port=port)
end
