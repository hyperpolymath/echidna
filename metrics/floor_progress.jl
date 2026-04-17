# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
#
# floor_progress.jl — Append-only ledger of Phase-1 progress toward the
# 10K-across-every-prover target. Banners every 5-prover milestone so
# the running total is impossible to miss.
#
# Writes to:
#   training_data/floor_progress.md   — append-only markdown log
#   training_data/floor_progress.jsonl — machine-readable ledger

module FloorProgress

using Dates
using JSON3

using ..CorpusLoader: CorpusIndex

export record_progress, FLOOR_TARGET, MILESTONE_STEP

const FLOOR_TARGET   = 10_000
const MILESTONE_STEP = 5
const PROGRESS_MD    = "floor_progress.md"
const PROGRESS_JSONL = "floor_progress.jsonl"

"""
    record_progress(idx; training_dir, run_id) -> NamedTuple

Count how many provers have reached the 10K floor. Append one row to
the ledger files. If the count is a multiple of MILESTONE_STEP and it
is the first time this count is reached, print a banner to stdout.
"""
function record_progress(idx::CorpusIndex;
                         training_dir::AbstractString,
                         run_id::AbstractString)
    counts = Dict(p => length(recs) for (p, recs) in idx)
    at_floor = [p for (p, c) in counts if c >= FLOOR_TARGET]
    total_provers = length(counts)
    total_records = sum(values(counts); init = 0)
    floor_val = isempty(counts) ? 0 : minimum(values(counts))
    count_at = length(at_floor)

    previous = _previous_count(joinpath(training_dir, PROGRESS_JSONL))
    newly_crossed = count_at - previous
    newly_crossed = newly_crossed < 0 ? 0 : newly_crossed

    row = Dict{String, Any}(
        "ts"             => string(now()),
        "run_id"         => run_id,
        "provers_total"  => total_provers,
        "provers_at_10k" => count_at,
        "newly_crossed"  => newly_crossed,
        "floor_value"    => floor_val,
        "total_records"  => total_records,
        "at_floor_list"  => sort(at_floor),
    )

    jpath = joinpath(training_dir, PROGRESS_JSONL)
    open(jpath, "a") do fh
        JSON3.write(fh, row)
        println(fh)
    end

    mpath = joinpath(training_dir, PROGRESS_MD)
    isnew = !isfile(mpath)
    open(mpath, "a") do fh
        if isnew
            write(fh, "# Phase-1 floor progress (target: 10 000 proofs per prover)\n\n")
            write(fh, "| ts | run_id | provers_at_10k / total | floor | total_records | newly_crossed |\n")
            write(fh, "|---|---|---:|---:|---:|---:|\n")
        end
        line = string("| ", row["ts"], " | ", run_id, " | ",
                      count_at, " / ", total_provers, " | ",
                      floor_val, " | ", total_records, " | ",
                      newly_crossed, " |\n")
        write(fh, line)
    end

    crossed_milestone = count_at >= MILESTONE_STEP &&
                        (count_at ÷ MILESTONE_STEP) >
                        (previous ÷ MILESTONE_STEP)
    if crossed_milestone
        banner = "★" ^ 40
        println("\n", banner)
        println("  MILESTONE: $count_at / $total_provers provers at 10K floor")
        println("  Newly crossed this run: $newly_crossed")
        println(banner, "\n")
    end

    return (; at_floor = sort(at_floor),
              count_at,
              total_provers,
              newly_crossed,
              floor_val,
              total_records)
end

function _previous_count(jsonl_path::AbstractString)::Int
    isfile(jsonl_path) || return 0
    last_count = 0
    open(jsonl_path, "r") do fh
        for line in eachline(fh)
            s = strip(line)
            isempty(s) && continue
            try
                r = JSON3.read(s, Dict{String,Any})
                last_count = Int(get(r, "provers_at_10k", last_count))
            catch
            end
        end
    end
    return last_count
end

end
