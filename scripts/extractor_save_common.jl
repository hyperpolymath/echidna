# SPDX-License-Identifier: PMPL-1.0-or-later
# Shared helper used by the backend-only-prover extractors to serialise
# proof-states / tactics / premises to the standard training_data layout.
using JSON3, Dates

"""
    save_common(proof_states, tactics, premises, prover_name, start_id, out_dir)

Write the four canonical output files for a per-prover extractor:
`proof_states_<name>.jsonl`, `tactics_<name>.jsonl`,
`premises_<name>.jsonl`, and `stats_<name>.json`. Keeps the extractor
bodies compact — each new extractor needs only its own regex and
source-walking logic, not another copy of this boilerplate.
"""
function save_common(ps::Vector, ts::Vector, pm::Vector, prover::String, start_id::Int, out_dir::String="training_data")
    mkpath(out_dir)
    lname = lowercase(prover)
    for (name, data) in [("proof_states", ps), ("tactics", ts), ("premises", pm)]
        open(joinpath(out_dir, "$(name)_$(lname).jsonl"), "w") do f
            for x in data
                println(f, JSON3.write(x))
            end
        end
    end
    stats = Dict{String,Any}(
        "prover" => prover,
        "extraction_date" => string(Dates.today()),
        "proof_states_count" => length(ps),
        "tactics_count" => length(ts),
        "premises_count" => length(pm),
        "start_id" => start_id,
        "end_id" => isempty(ps) ? start_id : start_id + length(ps) - 1,
    )
    open(joinpath(out_dir, "stats_$(lname).json"), "w") do f
        JSON3.pretty(f, stats)
    end
    println("Saved $(length(ps)) proof states, $(length(ts)) tactics, $(length(pm)) premises to $out_dir ($(prover))")
end
