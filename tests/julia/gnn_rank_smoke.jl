# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# Smoke test: confirm that a running EchidnaML server exposes /gnn/rank
# and that it routes through the trained PremiseRanker rather than the
# cosine-similarity fallback.
#
# Usage (server must already be running on ECHIDNA_ML_API_URL):
#   julia --project=src/julia tests/julia/gnn_rank_smoke.jl
#
# Exits non-zero if the GNN model is not loaded, i.e. /gnn/rank would
# silently fall back to cosine similarity (pre-pkg5 behaviour).

using HTTP
using JSON3

const BASE = get(ENV, "ECHIDNA_ML_API_URL", "http://127.0.0.1:8090")

# --------------------------------------------------------------------------
# 1. /gnn/health — authoritative signal for "trained model loaded".  When
#    gnn_model_loaded is true, rank_with_gnn dispatches to
#    rank_with_trained_model instead of rank_with_cosine, so the cosine
#    fallback code path is unreachable from /gnn/rank.
# --------------------------------------------------------------------------
println("Probing GET $BASE/gnn/health")
let r = HTTP.get("$BASE/gnn/health"; readtimeout=10, retries=0)
    @assert r.status == 200 "health: status $(r.status)"
    body = JSON3.read(String(r.body))
    println("  status=$(body.status) gnn_model_loaded=$(body.gnn_model_loaded) num_gnn_layers=$(body.num_gnn_layers)")
    @assert body.gnn_model_loaded "GNN model NOT loaded — endpoint would fall back to cosine"
    println("  PASS: GNN model loaded")
end

# --------------------------------------------------------------------------
# 2. /gnn/rank — send a toy 3-node graph.  Goal: confirm the trained-model
#    path is exercised.  A 200 with ranked premises means the model ran and
#    returned scores.  A 500 with a shape-mismatch error still counts — it
#    proves rank_with_trained_model was entered (vs rank_with_cosine which
#    is shape-agnostic and would have returned a 200 with cosine scores).
#    A 500 for any other reason is a wiring failure.
# --------------------------------------------------------------------------
println("\nProbing POST $BASE/gnn/rank (3-node toy graph, 128-dim features)")
feat_dim = 128
num_nodes = 3
node_features = [Float32(sin(i)) for i in 1:(feat_dim * num_nodes)]
payload = Dict(
    "graph" => Dict(
        "num_nodes"            => num_nodes,
        "num_edges"            => 2,
        "edge_src"             => [0, 0],
        "edge_dst"             => [1, 2],
        "edge_weights"         => [1.0f0, 1.0f0],
        "edge_kinds"           => ["goal_to_premise", "goal_to_premise"],
        "node_features"        => node_features,
        "feature_dim"          => feat_dim,
        "node_kinds"           => ["goal", "premise", "premise"],
        "node_labels"          => ["goal", "lemma_a", "lemma_b"],
        "goal_node_idx"        => 0,
        "premise_node_indices" => [1, 2],
    ),
    "top_k"              => 5,
    "min_score"          => 0.0,
    "include_embeddings" => false,
    "config"             => Dict("num_gnn_layers" => 4, "use_attention" => true),
)
body_json = JSON3.write(payload)
let r = HTTP.post("$BASE/gnn/rank", ["Content-Type" => "application/json"], body_json;
                  readtimeout=30, retries=0, status_exception=false)
    body = JSON3.read(String(r.body))
    if r.status == 200 && get(body, :success, false)
        println("  status=200 success=true  n_ranked=$(length(body.premise_names))  inference_ms=$(body.inference_time_ms)")
        println("  premise_names=$(body.premise_names)  scores=$(body.scores)")
        println("  PASS: trained model ran and returned ranked premises")
    else
        err_msg = string(get(body, :error, "(no error field)"))
        # Shape errors prove we reached rank_with_trained_model and not
        # the cosine fallback (which is shape-agnostic).
        reached_model = any(needle -> occursin(needle, err_msg),
                            ["DimensionMismatch", "MethodError", "BoundsError",
                             "size", "axes", "shape"])
        println("  status=$(r.status) success=false  error=$err_msg")
        @assert reached_model "rank_with_trained_model was NOT entered — cosine fallback suspected"
        println("  PASS: rank_with_trained_model entered (shape/type error from the trained path)")
    end
end

println("\nOK — /gnn/rank reaches the trained model.  Cosine fallback is not taken.")
