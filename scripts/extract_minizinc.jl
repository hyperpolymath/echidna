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

    # Extract variables
    variables = [(m.captures[2], m.captures[1]) for m in eachmatch(r"var\s+([\w.]+)\s*:\s*(\w+)"i, content)]

    # Extract constraints
    constraints = [first(replace(strip(m.captures[1]), r"\s+" => " "), 200)
                   for m in eachmatch(r"constraint\s+(.*?)\s*;"s, content)]

    # Extract objective
    objective = "satisfy"
    for m in eachmatch(r"solve\s+(.*?)\s*;"s, content)
        objective = first(replace(strip(m.captures[1]), r"\s+" => " "), 200)
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

    timetabling = [
        ("university_timetable", "satisfy",
         ["var 1..num_slots: schedule[1..num_courses]"],
         ["forall(c in courses)(schedule[c] in available[c])",
          "forall(c1 in courses, c2 in courses where c1 < c2 /\\ shared_students[c1,c2] > 0)(schedule[c1] != schedule[c2])",
          "forall(r in rooms, s in slots)(sum(c in courses where schedule[c] = s /\\ room[c] = r)(1) <= 1)",
          "forall(t in teachers)(alldifferent([schedule[c] | c in courses where teacher[c] = t]))"]),
        ("exam_scheduling", "minimize num_slots_used",
         ["var 1..max_slots: exam_slot[1..num_exams]", "var 0..1: slot_used[1..max_slots]"],
         ["forall(e1,e2 in exams where conflict[e1,e2])(exam_slot[e1] != exam_slot[e2])",
          "forall(s in 1..max_slots)(slot_used[s] = (exists(e in exams)(exam_slot[e] = s)))",
          "num_slots_used = sum(s in 1..max_slots)(slot_used[s])"]),
        ("sports_league", "satisfy",
         ["var 1..num_rounds: round[1..num_matches]", "var teams: home[1..num_matches]", "var teams: away[1..num_matches]"],
         ["forall(m in matches)(home[m] != away[m])",
          "forall(t in teams)(sum(m in matches)(home[m] = t \\/ away[m] = t) = num_rounds)",
          "forall(r in rounds)(alldifferent([home[m] | m in matches where round[m] = r] ++ [away[m] | m in matches where round[m] = r]))"]),
        ("crew_scheduling", "minimize total_crew_cost",
         ["var 0..1: assign[1..num_crew, 1..num_flights]"],
         ["forall(f in flights)(sum(c in crew)(assign[c,f]) >= min_crew[f])",
          "forall(c in crew)(sum(f in flights)(assign[c,f] * duration[f]) <= max_hours)",
          "total_crew_cost = sum(c in crew, f in flights)(assign[c,f] * cost[c,f])"]),
        ("room_assignment", "minimize max_distance",
         ["var 1..num_rooms: assign[1..num_people]"],
         ["alldifferent(assign)",
          "forall(p in people)(capacity[assign[p]] >= needs[p])",
          "max_distance = max(p1,p2 in people where collaborate[p1,p2])(distance[assign[p1], assign[p2]])"]),
        ("conference_schedule", "satisfy",
         ["var 1..num_sessions: talk_session[1..num_talks]", "var 1..num_tracks: talk_track[1..num_talks]"],
         ["forall(s in sessions, t in tracks)(sum(k in talks where talk_session[k] = s /\\ talk_track[k] = t)(1) <= 1)",
          "forall(k1,k2 in talks where same_speaker[k1,k2])(talk_session[k1] != talk_session[k2])",
          "forall(k in talks)(talk_track[k] in preferred_tracks[k])"]),
    ]

    network = [
        ("shortest_path", "minimize path_cost",
         ["var 0..1: use_edge[1..num_edges]"],
         ["forall(v in 2..n-1)(sum(e in in_edges[v])(use_edge[e]) = sum(e in out_edges[v])(use_edge[e]))",
          "sum(e in out_edges[source])(use_edge[e]) - sum(e in in_edges[source])(use_edge[e]) = 1",
          "path_cost = sum(e in edges)(use_edge[e] * weight[e])"]),
        ("load_balancing", "minimize max_load",
         ["var 1..num_servers: assign[1..num_tasks]"],
         ["forall(s in servers)(sum(t in tasks where assign[t] = s)(demand[t]) <= server_capacity[s])",
          "max_load = max(s in servers)(sum(t in tasks where assign[t] = s)(demand[t]))"]),
        ("wavelength_assignment", "minimize num_wavelengths",
         ["var 1..max_wl: wavelength[1..num_paths]"],
         ["forall(e in edges, p1,p2 in paths where p1 < p2 /\\ uses_edge[p1,e] /\\ uses_edge[p2,e])(wavelength[p1] != wavelength[p2])",
          "num_wavelengths = max(wavelength)"]),
        ("bandwidth_alloc", "maximize total_throughput",
         ["var 0.0..max_rate: rate[1..num_flows]"],
         ["forall(e in edges)(sum(f in flows where uses_edge[f,e])(rate[f]) <= capacity[e])",
          "total_throughput = sum(f in flows)(rate[f])"]),
        ("vlan_assignment", "minimize num_vlans",
         ["var 1..max_vlan: vlan[1..num_hosts]"],
         ["forall(h1,h2 in hosts where must_separate[h1,h2])(vlan[h1] != vlan[h2])",
          "forall(h1,h2 in hosts where must_communicate[h1,h2])(vlan[h1] = vlan[h2])",
          "num_vlans = max(vlan)"]),
    ]

    logistics = [
        ("warehouse_location", "minimize total_cost",
         ["var 0..1: open_wh[1..num_warehouses]", "var 0..1: serve[1..num_warehouses, 1..num_customers]"],
         ["forall(c in customers)(sum(w in warehouses)(serve[w,c]) = 1)",
          "forall(w in warehouses, c in customers)(serve[w,c] <= open_wh[w])",
          "total_cost = sum(w)(open_wh[w]*fixed_cost[w]) + sum(w,c)(serve[w,c]*transport[w,c])"]),
        ("fleet_routing", "minimize total_distance",
         ["var 0..num_customers: next[0..num_customers]"],
         ["subcircuit(next)",
          "forall(v in vehicles)(cumulative_load[v] <= vehicle_cap)",
          "total_distance = sum(i in 0..num_customers)(dist[i, next[i]])"]),
        ("inventory_optimization", "minimize total_holding + total_ordering",
         ["var 0..max_order: order[1..num_periods]", "var 0..max_inv: inventory[1..num_periods]"],
         ["forall(t in periods)(inventory[t] = inventory[t-1] + order[t] - demand[t])",
          "forall(t in periods)(inventory[t] >= safety_stock)",
          "total_holding = sum(t)(inventory[t]*hold_cost)",
          "total_ordering = sum(t)(if order[t] > 0 then setup_cost + order[t]*unit_cost else 0 endif)"]),
        ("supply_chain", "minimize total_supply_cost",
         ["var 0..max_ship: ship[1..num_plants, 1..num_warehouses]", "var 0..max_ship: deliver[1..num_warehouses, 1..num_retailers]"],
         ["forall(r in retailers)(sum(w in warehouses)(deliver[w,r]) >= demand[r])",
          "forall(w in warehouses)(sum(p in plants)(ship[p,w]) >= sum(r in retailers)(deliver[w,r]))",
          "forall(p in plants)(sum(w in warehouses)(ship[p,w]) <= capacity[p])",
          "total_supply_cost = sum(p,w)(ship[p,w]*cost_pw[p,w]) + sum(w,r)(deliver[w,r]*cost_wr[w,r])"]),
        ("cold_chain", "satisfy",
         ["var 0..max_time: depart[1..num_stops]", "var vehicles: truck[1..num_stops]"],
         ["forall(s in stops)(depart[s] + service[s] + travel[s, next[s]] <= depart[next[s]])",
          "forall(s in stops)(depart[s] + max_cold_time >= depart[next[s]])",
          "forall(v in vehicles)(sum(s in stops where truck[s] = v)(demand[s]) <= truck_cap)"]),
    ]

    puzzle = [
        ("cryptarithmetic", "satisfy",
         ["var 0..9: letter[1..num_letters]"],
         ["alldifferent(letter)",
          "letter[leading1] > 0 /\\ letter[leading2] > 0",
          "sum(i in 1..len1)(letter[word1[i]] * pow10[len1-i]) + sum(i in 1..len2)(letter[word2[i]] * pow10[len2-i]) = sum(i in 1..len3)(letter[word3[i]] * pow10[len3-i])"]),
        ("kakuro", "satisfy",
         ["var 1..9: cell[1..num_cells]"],
         ["forall(g in groups)(alldifferent([cell[c] | c in group_cells[g]]))",
          "forall(g in groups)(sum(c in group_cells[g])(cell[c]) = clue[g])"]),
        ("nonogram", "satisfy",
         ["var 0..1: grid[1..rows, 1..cols]"],
         ["forall(r in 1..rows)(check_runs(grid[r,..], row_clues[r]))",
          "forall(c in 1..cols)(check_runs(grid[..,c], col_clues[c]))"]),
        ("kenken", "satisfy",
         ["var 1..n: grid[1..n, 1..n]"],
         ["forall(r in 1..n)(alldifferent(grid[r, ..]))",
          "forall(c in 1..n)(alldifferent(grid[.., c]))",
          "forall(g in groups)(cage_constraint(grid, g, op[g], target[g]))"]),
        ("futoshiki", "satisfy",
         ["var 1..n: grid[1..n, 1..n]"],
         ["forall(r in 1..n)(alldifferent(grid[r, ..]))",
          "forall(c in 1..n)(alldifferent(grid[.., c]))",
          "forall((r1,c1,r2,c2) in inequalities)(grid[r1,c1] < grid[r2,c2])"]),
        ("hidato", "satisfy",
         ["var 1..n*m: cell[1..n, 1..m]"],
         ["alldifferent(array1d(cell))",
          "forall(v in 1..n*m-1)(exists(r1,c1,r2,c2 in positions where adjacent(r1,c1,r2,c2))(cell[r1,c1] = v /\\ cell[r2,c2] = v+1))"]),
    ]

    production = [
        ("lot_sizing", "minimize total_production_cost",
         ["var 0..max_prod: produce[1..num_periods]", "var 0..1: setup[1..num_periods]"],
         ["forall(t in periods)(produce[t] <= big_M * setup[t])",
          "forall(t in periods)(inventory[t] = inventory[t-1] + produce[t] - demand[t])",
          "forall(t in periods)(inventory[t] >= 0)",
          "total_production_cost = sum(t)(setup[t]*setup_cost + produce[t]*prod_cost + inventory[t]*hold_cost)"]),
        ("assembly_line", "minimize cycle_time",
         ["var 1..num_stations: station[1..num_tasks]"],
         ["forall((i,j) in precedences)(station[i] <= station[j])",
          "forall(s in stations)(sum(t in tasks where station[t] = s)(proc_time[t]) <= cycle_time)",
          "cycle_time >= max(s in stations)(sum(t in tasks where station[t] = s)(proc_time[t]))"]),
        ("workforce_planning", "minimize total_labor_cost",
         ["var 0..max_workers: hire[1..num_periods]", "var 0..max_workers: fire[1..num_periods]", "var 0..max_workers: workforce[1..num_periods]"],
         ["forall(t in periods)(workforce[t] = workforce[t-1] + hire[t] - fire[t])",
          "forall(t in periods)(workforce[t] >= min_demand[t])",
          "total_labor_cost = sum(t)(hire[t]*hire_cost + fire[t]*fire_cost + workforce[t]*wage)"]),
        ("preventive_maintenance", "minimize total_downtime",
         ["var 0..1: maintain[1..num_machines, 1..num_periods]"],
         ["forall(m in machines)(sum(t in periods)(maintain[m,t]) >= min_maintenance[m])",
          "forall(t in periods)(sum(m in machines)(maintain[m,t]) <= max_simultaneous)",
          "total_downtime = sum(m,t)(maintain[m,t] * downtime[m])"]),
        ("yield_optimization", "maximize total_yield",
         ["var 0.0..1.0: mix[1..num_ingredients]"],
         ["sum(mix) = 1.0",
          "forall(p in properties)(sum(i in ingredients)(mix[i] * prop_value[i,p]) >= min_prop[p])",
          "forall(p in properties)(sum(i in ingredients)(mix[i] * prop_value[i,p]) <= max_prop[p])",
          "total_yield = sum(i in ingredients)(mix[i] * yield_rate[i])"]),
    ]

    all_categories = [
        ("scheduling", scheduling),
        ("packing_routing", packing_routing),
        ("combinatorial", combinatorial),
        ("optimization", optimization),
        ("timetabling", timetabling),
        ("network", network),
        ("logistics", logistics),
        ("puzzle", puzzle),
        ("production", production),
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

    for fname in readdir(EXTERNAL_DIR)
        if endswith(fname, ".mzn")
            fpath = joinpath(EXTERNAL_DIR, fname)
            parsed = parse_mzn_file(fpath)
            append!(all_entries, parsed)
            if !isempty(parsed)
                println("  Parsed $(length(parsed)) models from $(fname)")
            end
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

    # Assign IDs and normalize schema
    # Distribute across solvers for downloaded models
    solvers_cycle = ["MiniZinc", "Chuffed", "ORTools", "SCIP", "GLPK"]
    current_id = START_ID
    output_records = Dict{String,Any}[]

    for (i, entry) in enumerate(all_entries)
        solver = get(entry, "solver", solvers_cycle[((i - 1) % length(solvers_cycle)) + 1])
        record = Dict{String,Any}(
            "id" => current_id,
            "prover" => solver,
            "theorem" => entry["theorem"],
            "goal" => entry["goal"],
            "context" => get(entry, "constraints", get(entry, "variables", String[])),
            "tactic_proof" => JSON3.write(Dict("variables" => get(entry, "variables", String[]), "constraints" => get(entry, "constraints", String[]))),
            "source" => get(entry, "source", "minizinc"),
        )
        push!(output_records, record)
        current_id += 1
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
