# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# verisim_sink.jl — Post metric rows to VeriSimDB.
#
# POST /api/v1/metrics  { run_id, metric, value, unit, context, ts }
#
# If VeriSimDB is unreachable, rows are still appended to
# training_data/metrics_<run_id>.jsonl so the run is recoverable.

module VeriSimSink

using Dates
using HTTP
using JSON3

export emit_metric, metric_row

const DEFAULT_URL = get(ENV, "VERISIM_URL", "http://localhost:8080")
const TIMEOUT_S   = 5

function metric_row(run_id::AbstractString,
                    metric::AbstractString,
                    value::Real;
                    unit::AbstractString = "",
                    context::AbstractDict = Dict{String,Any}())
    Dict{String, Any}(
        "run_id"  => String(run_id),
        "metric"  => String(metric),
        "value"   => Float64(value),
        "unit"    => String(unit),
        "context" => context,
        "ts"      => string(now()),
    )
end

function emit_metric(row::AbstractDict;
                     verisim_url::AbstractString = DEFAULT_URL,
                     fallback_dir::AbstractString = joinpath(
                         dirname(dirname(abspath(@__FILE__))),
                         "training_data"))
    sent_ok = false
    url = "$(rstrip(verisim_url, '/'))/api/v1/metrics"
    try
        resp = HTTP.post(url,
                         ["Content-Type" => "application/json"],
                         JSON3.write(row);
                         readtimeout = TIMEOUT_S,
                         connect_timeout = TIMEOUT_S)
        sent_ok = 200 <= resp.status < 300
    catch err
        @warn "VeriSim emit failed; falling back to disk" metric = row["metric"] error = err
    end

    run_id = row["run_id"]
    mkpath(fallback_dir)
    path = joinpath(fallback_dir, "metrics_$(run_id).jsonl")
    open(path, "a") do fh
        JSON3.write(fh, row)
        println(fh)
    end

    return (; sent_ok, cached_at = path)
end

end
