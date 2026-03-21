# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# run_server.jl — Start the ECHIDNA neural premise selection API server.
#
# Usage:
#   julia --project=src/julia src/julia/run_server.jl [model_dir] [port]
#
# Defaults:
#   model_dir = models/neural/final_model
#   port      = 8090
#
# The Rust server (server.rs) connects to this on ECHIDNA_ML_API_URL
# (default http://127.0.0.1:8090).

using Pkg
Pkg.activate(joinpath(@__DIR__))

println("╔═══════════════════════════════════════════════════════════╗")
println("║  ECHIDNA Neural Solver — API Server                      ║")
println("╚═══════════════════════════════════════════════════════════╝")
println()

# Parse arguments
model_dir = length(ARGS) >= 1 ? ARGS[1] : joinpath(@__DIR__, "..", "..", "models", "neural", "final_model")
port = length(ARGS) >= 2 ? parse(Int, ARGS[2]) : 8090

println("Model directory: $model_dir")
println("Port: $port")
println()

# Load module
println("Loading EchidnaML module...")
include(joinpath(@__DIR__, "EchidnaML.jl"))
using .EchidnaML

# Start server (blocking — runs until Ctrl+C)
start_api_server(model_dir; port=port, host="0.0.0.0", cache_size=1000, async=false)
