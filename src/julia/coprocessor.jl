# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# src/julia/coprocessor.jl
#
# Julia-side coprocessor router for ECHIDNA.
#
# Receives `CoprocessorOp` requests over HTTP from the Rust
# `JuliaCoprocessorBridge` (src/rust/coprocessor/julia_bridge.rs) and
# routes to one of:
#   - LowLevel.jl              — CPU/GPU/NPU/TPU/QPU/PPU/DSP/FPGA/IOPU
#   - ProvenCrypto.jl          — formally verified crypto
#   - KnotTheory.jl / Skein.jl — topology
#   - native Julia fallback    — for ops the in-process Rust Math backend
#                                 already covers but a Julia call is preferred
#                                 (e.g. for batch dispatch using BLAS or CUDA).
#
# Endpoint: POST /coprocessor/dispatch
# Probe:    GET  /coprocessor/health
#
# Wire format mirrors `CoprocessorOp` / `CoprocessorOutcome` Serde external
# tagging:
#   request:  {"kind": "Math",
#              "op":   {"BigIntGcd": {"a": "12", "b": "18"}}}
#   response: {"outcome": {"BigInt": "6"}}
#
# Errors come back as {"error": "..."} (transport / Julia runtime failure)
# or as {"outcome": {"Failure": "..."}} (well-formed input, op declined).
#
# Phase 0 ships the router scaffold + a native-Julia Math fallback that
# parallels the Rust Math backend.  Phase 6 wires LowLevel.jl /
# ProvenCrypto.jl / topology backends behind specific kinds.

module EchidnaCoprocessor

using HTTP
using JSON3
using Logging

export start_coprocessor_server, dispatch_op

# ── Health ────────────────────────────────────────────────────────────────────

"Liveness response for `GET /coprocessor/health`."
function health_response()
    JSON3.write(Dict(
        "success"  => true,
        "kinds"    => ["Math"],   # Phase 6 will extend this list
        "version"  => "0.1.0",
    ))
end

# ── Dispatch ──────────────────────────────────────────────────────────────────

"""
    dispatch_op(kind::String, op::Dict)::Dict

Dispatch a single coprocessor op.  Returns a Dict matching the wire
`DispatchResponse` shape.
"""
function dispatch_op(kind::AbstractString, op::Dict)::Dict
    if kind == "Math"
        return dispatch_math(op)
    end
    return Dict("error" => "unsupported kind: $kind")
end

# ── Math fallback (parallels src/rust/coprocessor/math.rs) ───────────────────

function dispatch_math(op::Dict)::Dict
    # Op is a single-key Dict whose key is the variant name.
    if length(op) != 1
        return Dict("error" => "op must have exactly one variant key")
    end
    (variant, payload) = first(op)
    try
        return Dict("outcome" => _exec_math(string(variant), payload))
    catch e
        # Distinguish input-shape errors (return as Failure outcome — caller
        # may retry) from Julia runtime errors (return as transport error).
        if isa(e, ArgumentError) || isa(e, DomainError)
            return Dict("outcome" => Dict("Failure" => string(e)))
        else
            return Dict("error" => string(e))
        end
    end
end

function _exec_math(variant::String, payload)::Dict
    if variant == "BigIntGcd"
        a = parse(BigInt, payload["a"])
        b = parse(BigInt, payload["b"])
        return Dict("BigInt" => string(gcd(a, b)))
    elseif variant == "BigIntLcm"
        a = parse(BigInt, payload["a"])
        b = parse(BigInt, payload["b"])
        return Dict("BigInt" => string(lcm(a, b)))
    elseif variant == "BigIntModExp"
        b = parse(BigInt, payload["base"])
        e = parse(BigInt, payload["exp"])
        m = parse(BigInt, payload["modulus"])
        e < 0 && return Dict("Failure" => "exponent must be non-negative")
        m < 1 && return Dict("Failure" => "modulus must be positive")
        return Dict("BigInt" => string(powermod(b, e, m)))
    elseif variant == "BigIntIsProbablePrime"
        n = parse(BigInt, payload["n"])
        return Dict("Boolean" => Base.GMP.MPZ.probab_prime_p(n, 40) > 0)
    elseif variant == "Fibonacci"
        n = Int(payload["n"])
        return Dict("BigInt" => string(_fib(n)))
    elseif variant == "Factorial"
        n = Int(payload["n"])
        n < 0 && return Dict("Failure" => "factorial input must be non-negative")
        return Dict("BigInt" => string(factorial(big(n))))
    end
    return Dict("Failure" => "Math op not implemented in Julia layer: $variant")
end

# Fast-doubling Fibonacci — matches the Rust impl exactly so cross-checking
# the Rust ↔ Julia paths produces bitwise-identical answers.
function _fib(n::Int)::BigInt
    function helper(n::Int)::Tuple{BigInt,BigInt}
        n == 0 && return (big(0), big(1))
        a, b = helper(n ÷ 2)
        c = a * (2b - a)
        d = a*a + b*b
        return iseven(n) ? (c, d) : (d, c + d)
    end
    return helper(n)[1]
end

# ── HTTP server ───────────────────────────────────────────────────────────────

"""
    start_coprocessor_server(port::Int = 8090)

Start the HTTP coprocessor router on `127.0.0.1:port`.  Blocks the calling
task; run inside `@async` if you want a non-blocking variant.

Routes:
- `GET  /coprocessor/health`
- `POST /coprocessor/dispatch`  body = {"kind": "...", "op": {...}}
"""
function start_coprocessor_server(port::Int = 8090)
    router = HTTP.Router()

    HTTP.register!(router, "GET", "/coprocessor/health", function (req)
        HTTP.Response(200, ["Content-Type" => "application/json"], body=health_response())
    end)

    HTTP.register!(router, "POST", "/coprocessor/dispatch", function (req)
        body = String(HTTP.payload(req))
        try
            parsed = JSON3.read(body, Dict)
            kind = string(get(parsed, "kind", ""))
            op   = Dict(get(parsed, "op",   Dict()))
            resp = dispatch_op(kind, op)
            HTTP.Response(200, ["Content-Type" => "application/json"], body=JSON3.write(resp))
        catch e
            HTTP.Response(400, ["Content-Type" => "application/json"],
                body=JSON3.write(Dict("error" => "request parse: $(string(e))")))
        end
    end)

    @info "EchidnaCoprocessor router listening on 127.0.0.1:$port"
    HTTP.serve(router, "127.0.0.1", port)
end

end # module EchidnaCoprocessor
