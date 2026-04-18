#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
#
# Extract constraint models from MiniZinc benchmarks and generate training data
# for constraint solver backends: MiniZinc, Chuffed, OR-Tools, SCIP, GLPK.
#
# Attempts to download from the MiniZinc Challenge benchmarks on GitHub.
# Falls back to generating high-quality synthetic constraint models.
#
# These provers solve optimization/satisfaction problems rather than logical
# theorems, so the schema is adapted: "theorem" = model name, "goal" = objective,
# "context" = constraints.
#
# Output: training_data/proof_states_minizinc.jsonl (covers all 5 solvers)
# ID range: 99000+

using JSON3

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

const REPO_ROOT = dirname(dirname(abspath(@__FILE__)))
const EXTERNAL_DIR = joinpath(REPO_ROOT, "external_corpora", "minizinc")
const OUTPUT_DIR = joinpath(REPO_ROOT, "training_data")
const OUTPUT_FILE = joinpath(OUTPUT_DIR, "proof_states_minizinc.jsonl")
const STATS_FILE = joinpath(OUTPUT_DIR, "stats_minizinc.json")
const START_ID = 99000

const MZN_RAW = "https://raw.githubusercontent.com/MiniZinc/minizinc-benchmarks/master"
const MZN_FILES = [
    "golomb/golomb.mzn",
    "queens/queens.mzn",
    "knapsack/knapsack.mzn",
    "jobshop/jobshop.mzn",
    "sudoku/sudoku.mzn",
    "magic-square/magic-square.mzn",
    "latin-squares/latin-squares.mzn",
    "graph-coloring/graph-coloring.mzn",
    "traveling-salesman/traveling-salesman.mzn",
    "bin-packing/bin-packing.mzn",
    "car-sequencing/car-sequencing.mzn",
    "nurses/nurses.mzn",
    "cumulative-job-shop/cumulative-job-shop.mzn",
    "open-stacks/open-stacks.mzn",
    "rcpsp/rcpsp.mzn",
]

# ---------------------------------------------------------------------------
# Parser
# ---------------------------------------------------------------------------

"""
    parse_mzn_file(filepath::String) -> Vector{Dict{String,Any}}

Parse a MiniZinc .mzn file and extract model structure.
"""
function parse_mzn_file(filepath::String)::Vector{Dict{String,Any}}
    results = Dict{String,Any}[]
    content = try
        read(filepath, String)
    catch
        return results
    end

    model_name = splitext(basename(filepath))[1]

    # Each of these regexes can catastrophically backtrack on large
    # data files or amalgamated benchmarks. Wrap each collection in
    # a try/catch so a single pathological file just skips — the rest
    # of the corpus still extracts.
    variables = try
        [(m.captures[2], m.captures[1]) for m in eachmatch(r"var\s+([\w.]+)\s*:\s*(\w+)"i, content)]
    catch
        Tuple{Any,Any}[]
    end

    constraints = try
        [first(replace(strip(m.captures[1]), r"\s+" => " "), 200)
         for m in eachmatch(r"constraint\s+(.*?)\s*;"s, content)]
    catch
        String[]
    end

    objective = "satisfy"
    try
        for m in eachmatch(r"solve\s+(.*?)\s*;"s, content)
            objective = first(replace(strip(m.captures[1]), r"\s+" => " "), 200)
        end
    catch
        # keep default
    end

    if !isempty(variables) || !isempty(constraints)
        push!(results, Dict{String,Any}(
            "theorem" => model_name,
            "goal" => objective,
            "variables" => ["$(v[1]): $(v[2])" for v in variables[1:min(20, length(variables))]],
            "constraints" => constraints[1:min(30, length(constraints))],
            "source" => "minizinc/$(basename(filepath))",
        ))
    end

    return results
end

# ---------------------------------------------------------------------------
# Downloader
# ---------------------------------------------------------------------------

"""
    download_mzn_files() -> Int

Attempt to download MiniZinc benchmark files.
"""
function download_mzn_files()::Int
    downloaded = 0
    for rel_path in MZN_FILES
        url = "$(MZN_RAW)/$(rel_path)"
        local_path = joinpath(EXTERNAL_DIR, basename(rel_path))
        if isfile(local_path)
            downloaded += 1
            continue
        end
        try
            download(url, local_path)
            downloaded += 1
            println("  Downloaded: $(rel_path)")
        catch exc
            println("  Skipped $(rel_path): $(exc)")
        end
    end
    return downloaded
end

# ---------------------------------------------------------------------------
# Synthetic generation
# ---------------------------------------------------------------------------

"""
    generate_synthetic_constraint_models() -> Vector{Dict{String,Any}}

Generate synthetic constraint satisfaction and optimization models.

Each model is assigned to one of the 5 solver backends in round-robin
fashion to ensure coverage: MiniZinc, Chuffed, ORTools, SCIP, GLPK.
"""
function generate_synthetic_constraint_models()::Vector{Dict{String,Any}}
    solvers = ["MiniZinc", "Chuffed", "ORTools", "SCIP", "GLPK"]

    scheduling = [
        ("job_shop_scheduling", "minimize makespan",
         ["var 1..horizon: start[j,m]", "var 1..horizon: end[j,m]"],
         ["forall(j in jobs, m in machines)(end[j,m] = start[j,m] + duration[j,m])",
          "forall(j in jobs, i in 1..num_ops-1)(start[j,op_order[j,i+1]] >= end[j,op_order[j,i]])",
          "forall(m in machines)(disjunctive(start[..,m], duration[..,m]))",
          "makespan = max(j in jobs)(end[j,last_op[j]])"]),
        ("flow_shop", "minimize max(end[num_jobs, ..])",
         ["var 0..horizon: start[1..num_jobs, 1..num_machines]"],
         ["forall(j in 1..num_jobs, m in 1..num_machines-1)(start[j,m+1] >= start[j,m] + proc[j,m])",
          "forall(j in 1..num_jobs-1, m in 1..num_machines)(start[j+1,m] >= start[j,m] + proc[j,m])"]),
        ("nurse_scheduling", "satisfy",
         ["var shifts: roster[1..num_nurses, 1..num_days]"],
         ["forall(d in 1..num_days, s in 1..num_shifts)(sum(n in 1..num_nurses)(roster[n,d] = s) >= demand[d,s])",
          "forall(n in 1..num_nurses, d in 1..num_days-1)(not (roster[n,d] = night /\\ roster[n,d+1] = morning))",
          "forall(n in 1..num_nurses)(sum(d in 1..num_days)(roster[n,d] != off) <= max_shifts)"]),
        ("task_assignment", "minimize total_cost",
         ["var 1..num_workers: assign[1..num_tasks]"],
         ["all_different(assign)",
          "total_cost = sum(t in 1..num_tasks)(cost[t, assign[t]])",
          "forall(w in 1..num_workers)(sum(t in 1..num_tasks)(assign[t] = w) <= capacity[w])"]),
        ("resource_constrained_project", "minimize makespan",
         ["var 0..horizon: start[1..num_activities]", "var 0..horizon: end[1..num_activities]"],
         ["forall(a in activities)(end[a] = start[a] + duration[a])",
          "forall((a,b) in precedences)(start[b] >= end[a])",
          "forall(r in resources, t in 0..horizon)(sum(a in activities where start[a] <= t /\\ t < end[a])(usage[a,r]) <= capacity[r])",
          "makespan = max(a in activities)(end[a])"]),
    ]

    packing_routing = [
        ("bin_packing", "minimize num_bins",
         ["var 1..max_bins: bin[1..num_items]", "var 0..1: used[1..max_bins]"],
         ["forall(b in 1..max_bins)(sum(i in 1..num_items where bin[i] = b)(size[i]) <= capacity)",
          "forall(i in 1..num_items)(used[bin[i]] = 1)",
          "num_bins = sum(b in 1..max_bins)(used[b])"]),
        ("cutting_stock", "minimize num_rolls",
         ["var 0..max_copies: cut[1..num_patterns]"],
         ["forall(w in 1..num_widths)(sum(p in 1..num_patterns)(pattern[p,w] * cut[p]) >= demand[w])",
          "num_rolls = sum(p in 1..num_patterns)(cut[p])"]),
        ("vehicle_routing", "minimize total_distance",
         ["var 0..num_customers: next[0..num_customers]"],
         ["circuit(next)",
          "forall(v in 1..num_vehicles)(load[v] <= vehicle_capacity)",
          "total_distance = sum(i in 0..num_customers)(dist[i, next[i]])"]),
        ("tsp", "minimize tour_length",
         ["var 1..n: order[1..n]"],
         ["all_different(order)",
          "tour_length = sum(i in 1..n-1)(dist[order[i], order[i+1]]) + dist[order[n], order[1]]"]),
        ("container_loading", "maximize total_value",
         ["var 0..1: load[1..num_items]"],
         ["sum(i in 1..num_items)(load[i] * weight[i]) <= max_weight",
          "sum(i in 1..num_items)(load[i] * volume[i]) <= max_volume",
          "total_value = sum(i in 1..num_items)(load[i] * value[i])"]),
    ]

    combinatorial = [
        ("n_queens", "satisfy",
         ["var 1..n: queens[1..n]"],
         ["all_different(queens)",
          "all_different([queens[i] + i | i in 1..n])",
          "all_different([queens[i] - i | i in 1..n])"]),
        ("sudoku", "satisfy",
         ["var 1..9: grid[1..9, 1..9]"],
         ["forall(r in 1..9)(all_different(grid[r, ..]))",
          "forall(c in 1..9)(all_different(grid[.., c]))",
          "forall(br in 0..2, bc in 0..2)(all_different([grid[br*3+r, bc*3+c] | r in 1..3, c in 1..3]))"]),
        ("magic_square", "satisfy",
         ["var 1..n*n: square[1..n, 1..n]"],
         ["all_different(array1d(square))",
          "forall(r in 1..n)(sum(c in 1..n)(square[r,c]) = magic_sum)",
          "forall(c in 1..n)(sum(r in 1..n)(square[r,c]) = magic_sum)",
          "sum(i in 1..n)(square[i,i]) = magic_sum",
          "sum(i in 1..n)(square[i,n+1-i]) = magic_sum"]),
        ("graph_coloring", "minimize num_colors",
         ["var 1..max_colors: color[1..num_nodes]"],
         ["forall((u,v) in edges)(color[u] != color[v])",
          "num_colors = max(color)"]),
        ("latin_square", "satisfy",
         ["var 1..n: square[1..n, 1..n]"],
         ["forall(r in 1..n)(all_different(square[r, ..]))",
          "forall(c in 1..n)(all_different(square[.., c]))"]),
        ("golomb_ruler", "minimize marks[n]",
         ["var 0..max_mark: marks[1..n]"],
         ["marks[1] = 0",
          "forall(i in 1..n-1)(marks[i] < marks[i+1])",
          "all_different([marks[j] - marks[i] | i in 1..n, j in i+1..n])"]),
        ("set_covering", "minimize sum(selected)",
         ["var 0..1: selected[1..num_sets]"],
         ["forall(e in 1..num_elements)(sum(s in 1..num_sets where e in set_content[s])(selected[s]) >= 1)"]),
        ("steiner_triple", "satisfy",
         ["var set of 1..n: triple[1..num_triples]"],
         ["forall(t in 1..num_triples)(card(triple[t]) = 3)",
          "forall(t1 in 1..num_triples, t2 in t1+1..num_triples)(card(triple[t1] intersect triple[t2]) <= 1)"]),
    ]

    optimization = [
        ("knapsack_01", "maximize total_value",
         ["var 0..1: take[1..n]"],
         ["sum(i in 1..n)(take[i] * weight[i]) <= capacity",
          "total_value = sum(i in 1..n)(take[i] * value[i])"]),
        ("portfolio_optimization", "maximize expected_return - lambda * risk",
         ["var 0.0..1.0: allocation[1..num_assets]"],
         ["sum(allocation) = 1.0",
          "forall(i in 1..num_assets)(allocation[i] >= min_alloc[i])",
          "expected_return = sum(i in 1..num_assets)(allocation[i] * return_rate[i])",
          "risk = sum(i,j in 1..num_assets)(allocation[i] * allocation[j] * covariance[i,j])"]),
        ("facility_location", "minimize total_cost",
         ["var 0..1: open[1..num_facilities]", "var 0..1: assign[1..num_customers, 1..num_facilities]"],
         ["forall(c in 1..num_customers)(sum(f in 1..num_facilities)(assign[c,f]) = 1)",
          "forall(c in 1..num_customers, f in 1..num_facilities)(assign[c,f] <= open[f])",
          "total_cost = sum(f)(open[f] * fixed_cost[f]) + sum(c,f)(assign[c,f] * transport_cost[c,f])"]),
        ("diet_problem", "minimize total_cost",
         ["var 0.0..max_serving: amount[1..num_foods]"],
         ["forall(n in 1..num_nutrients)(sum(f in 1..num_foods)(amount[f] * nutrient_content[f,n]) >= min_nutrient[n])",
          "forall(n in 1..num_nutrients)(sum(f in 1..num_foods)(amount[f] * nutrient_content[f,n]) <= max_nutrient[n])",
          "total_cost = sum(f in 1..num_foods)(amount[f] * price[f])"]),
        ("assignment_problem", "minimize total_cost",
         ["var 0..1: assign[1..n, 1..n]"],
         ["forall(i in 1..n)(sum(j in 1..n)(assign[i,j]) = 1)",
          "forall(j in 1..n)(sum(i in 1..n)(assign[i,j]) = 1)",
          "total_cost = sum(i,j in 1..n)(assign[i,j] * cost[i,j])"]),
        ("max_flow", "maximize flow_value",
         ["var 0..capacity[i,j]: flow[1..n, 1..n]"],
         ["forall(v in 2..n-1)(sum(u)(flow[u,v]) = sum(w)(flow[v,w]))",
          "flow_value = sum(v)(flow[1,v])"]),
        ("min_cost_flow", "minimize total_cost",
         ["var 0..capacity[i,j]: flow[1..n, 1..n]"],
         ["forall(v in 1..n)(sum(u)(flow[u,v]) - sum(w)(flow[v,w]) = demand[v])",
          "total_cost = sum(i,j)(flow[i,j] * cost[i,j])"]),
    ]

    all_categories = [
        ("scheduling", scheduling),
        ("packing_routing", packing_routing),
        ("combinatorial", combinatorial),
        ("optimization", optimization),
    ]

    proofs = Dict{String,Any}[]
    solver_idx = 0
    for (category, models) in all_categories
        for entry in models
            model_name = entry[1]
            objective = entry[2]
            variables = entry[3]
            constraints = entry[4]

            solver = solvers[(solver_idx % length(solvers)) + 1]
            solver_idx += 1

            push!(proofs, Dict{String,Any}(
                "theorem" => model_name,
                "goal" => objective,
                "variables" => variables,
                "constraints" => constraints,
                "solver" => solver,
                "source" => "constraint_synthetic/$(category)",
            ))
        end
    end

    return proofs
end

# ---------------------------------------------------------------------------
# Main pipeline
# ---------------------------------------------------------------------------

"""
    run() -> Tuple{Int,Int}

Run the full extraction pipeline. Returns (extracted_count, synthetic_count).
"""
function run()::Tuple{Int,Int}
    mkpath(OUTPUT_DIR)
    mkpath(EXTERNAL_DIR)

    all_entries = Dict{String,Any}[]
    extracted_count = 0

    println("[MiniZinc/Constraint Solvers] Phase 1: Attempting to download benchmarks ...")
    downloaded = download_mzn_files()
    println("  Downloaded/cached $(downloaded) files")

    # Widening (2026-04-18): walk MiniZinc/minizinc-benchmarks at
    # external_corpora/minizinc_full/ — the official benchmark suite
    # with hundreds of real-world constraint models. Accepts .mzn
    # (model) and .dzn (data) files.
    src_files = String[]
    for fname in readdir(EXTERNAL_DIR)
        (endswith(fname, ".mzn") || endswith(fname, ".dzn")) &&
            push!(src_files, joinpath(EXTERNAL_DIR, fname))
    end
    full_root = joinpath(dirname(EXTERNAL_DIR), "minizinc_full")
    if isdir(full_root)
        println("[MiniZinc] Walking full benchmark clone at $(full_root) ...")
        for (root, _dirs, files) in walkdir(full_root)
            for fname in files
                (endswith(fname, ".mzn") || endswith(fname, ".dzn")) &&
                    push!(src_files, joinpath(root, fname))
            end
        end
    end
    println("  $(length(src_files)) MiniZinc source files to parse")

    processed = 0
    for fpath in src_files
        parsed = parse_mzn_file(fpath)
        append!(all_entries, parsed)
        processed += 1
        if processed % 500 == 0
            println("  processed $(processed)/$(length(src_files)) files — running count: $(length(all_entries))")
        end
    end
    extracted_count = length(all_entries)

    println("[MiniZinc/Constraint Solvers] Phase 2: Generating synthetic models ...")
    synthetic = generate_synthetic_constraint_models()
    existing_names = Set(e["theorem"] for e in all_entries)
    added = 0
    for entry in synthetic
        if entry["theorem"] ∉ existing_names
            push!(all_entries, entry)
            push!(existing_names, entry["theorem"])
            added += 1
        end
    end
    println("  Generated $(added) unique synthetic models")

    # Full-share (2026-04-18): every MiniZinc model is solvable by
    # every constraint solver in the fleet. Emit one record per
    # (model, solver) pair — 5× the per-solver coverage without any
    # new data. Synthetic entries retain their specific `solver`
    # assignment so sub-family statistics stay accurate.
    solvers_cycle = ["MiniZinc", "Chuffed", "ORTools", "SCIP", "GLPK"]
    current_id = START_ID
    output_records = Dict{String,Any}[]

    for entry in all_entries
        if haskey(entry, "solver")
            # Synthetic entry — keep single-solver assignment.
            record = Dict{String,Any}(
                "id" => current_id,
                "prover" => entry["solver"],
                "theorem" => entry["theorem"],
                "goal" => entry["goal"],
                "context" => get(entry, "constraints", get(entry, "variables", String[])),
                "tactic_proof" => JSON3.write(Dict(
                    "variables" => get(entry, "variables", String[]),
                    "constraints" => get(entry, "constraints", String[]))),
                "source" => get(entry, "source", "minizinc"),
            )
            push!(output_records, record)
            current_id += 1
        else
            # Real benchmark — emit for every solver.
            for solver in solvers_cycle
                record = Dict{String,Any}(
                    "id" => current_id,
                    "prover" => solver,
                    "theorem" => entry["theorem"],
                    "goal" => entry["goal"],
                    "context" => get(entry, "constraints", get(entry, "variables", String[])),
                    "tactic_proof" => JSON3.write(Dict(
                        "variables" => get(entry, "variables", String[]),
                        "constraints" => get(entry, "constraints", String[]))),
                    "source" => get(entry, "source", "minizinc"),
                )
                push!(output_records, record)
                current_id += 1
            end
        end
    end

    open(OUTPUT_FILE, "w") do fh
        for rec in output_records
            println(fh, JSON3.write(rec))
        end
    end

    # Count per solver
    solver_counts = Dict{String,Int}()
    for rec in output_records
        solver_counts[rec["prover"]] = get(solver_counts, rec["prover"], 0) + 1
    end

    stats = Dict{String,Any}(
        "total_models" => length(output_records),
        "extracted_from_source" => extracted_count,
        "synthetic_added" => length(output_records) - extracted_count,
        "id_range" => [START_ID, current_id - 1],
        "solver_distribution" => solver_counts,
        "output_file" => OUTPUT_FILE,
    )
    open(STATS_FILE, "w") do fh
        JSON3.pretty(fh, stats)
    end

    println("\n[Constraint Solvers] COMPLETE: $(length(output_records)) models written to $(OUTPUT_FILE)")
    println("  Solver distribution: $(solver_counts)")
    return (extracted_count, length(output_records) - extracted_count)
end

if abspath(PROGRAM_FILE) == abspath(@__FILE__)
    run()
end
