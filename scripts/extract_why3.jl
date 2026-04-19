#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
#
# Extract proofs from Why3 examples and convert to ECHIDNA training format.
#
# Attempts to download from the Why3 GitLab repository (examples/ dir).
# Falls back to generating high-quality synthetic Why3 proofs.
#
# Why3 is a platform for deductive program verification, featuring a rich
# specification language (WhyML) and integration with many automated and
# interactive provers.
#
# Output: training_data/proof_states_why3.jsonl
# ID range: 95000+

using JSON3

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

const REPO_ROOT = dirname(dirname(abspath(@__FILE__)))
const EXTERNAL_DIR = joinpath(REPO_ROOT, "external_corpora", "why3")
const OUTPUT_DIR = joinpath(REPO_ROOT, "training_data")
const OUTPUT_FILE = joinpath(OUTPUT_DIR, "proof_states_why3.jsonl")
const STATS_FILE = joinpath(OUTPUT_DIR, "stats_why3.json")
const START_ID = 95000

const WHY3_RAW = "https://gitlab.inria.fr/why3/why3/-/raw/master"
const WHY3_FILES = [
    "examples/euler001.mlw",
    "examples/fibonacci.mlw",
    "examples/insertion_sort.mlw",
    "examples/selection_sort.mlw",
    "examples/mergesort_list.mlw",
    "examples/binary_search.mlw",
    "examples/queens.mlw",
    "examples/power.mlw",
    "examples/factorial.mlw",
    "examples/gcd.mlw",
    "examples/maximum_subarray.mlw",
    "examples/knuth_prime_numbers.mlw",
    "examples/dutch_flag.mlw",
    "examples/ring_buffer.mlw",
    "examples/tortoise_and_hare.mlw",
    "examples/same_fringe.mlw",
]

# ---------------------------------------------------------------------------
# Parser
# ---------------------------------------------------------------------------

"""
    parse_why3_file(filepath::String) -> Vector{Dict{String,Any}}

Parse a Why3 .mlw file and extract lemma/goal/predicate patterns.

Why3 files contain modules with:
    lemma name: formula
    goal name: formula
    let rec function ... = ... ensures { ... }
"""
function parse_why3_file(filepath::String)::Vector{Dict{String,Any}}
    results = Dict{String,Any}[]
    content = try
        read(filepath, String)
    catch
        return results
    end

    # Widening (2026-04-18): Why3 has more named constructs than
    # lemma/goal/axiom alone. Capture also predicate / function /
    # constant / type / inductive / meta declarations.
    pattern = r"(lemma|goal|axiom|theorem|corollary|conjecture)\s+(\w+)\s*:\s*(.*?)(?=\n\s*(?:lemma|goal|axiom|theorem|corollary|conjecture|let|val|predicate|function|constant|type|inductive|meta|end|use|module|scope)|\z)"si
    for m in eachmatch(pattern, content)
        kind = strip(m.captures[1])
        name = strip(m.captures[2])
        body = first(replace(strip(m.captures[3]), r"\s+" => " "), 300)
        keywords = [lowercase(k.match) for k in eachmatch(r"\b(forall|exists|ensures|requires|invariant|variant|raises|reads|writes|diverges)\b"i, body)]
        seen = Set{String}()
        unique_kw = String[]
        for kw in keywords
            if kw ∉ seen
                push!(seen, kw)
                push!(unique_kw, kw)
            end
        end
        push!(results, Dict{String,Any}(
            "theorem" => name,
            "goal" => body,
            "kind" => kind,
            "tactics" => unique_kw,
            "source" => "why3/$(basename(filepath))",
        ))
    end

    # Additional declaration forms common in Why3 stdlib + examples.
    extra_pat = r"(predicate|function|constant|inductive|type)\s+(\w+)\s+(.*?)(?=\n\s*(?:lemma|goal|axiom|theorem|corollary|conjecture|let|val|predicate|function|constant|type|inductive|meta|end|use|module|scope)|\z)"si
    ex_matches = try collect(eachmatch(extra_pat, content)) catch; Any[] end
    for m in ex_matches
        kind = strip(String(m.captures[1]))
        name = strip(String(m.captures[2]))
        body = first(replace(strip(String(m.captures[3])), r"\s+" => " "), 300)
        isempty(name) && continue
        push!(results, Dict{String,Any}(
            "theorem" => name,
            "goal" => body,
            "kind" => kind,
            "tactics" => String[kind],
            "source" => "why3/$(basename(filepath))",
        ))
    end

    # Extract function specs (ensures/requires). Wrap in try/catch:
    # the `.*?` chains in func_pattern can catastrophically backtrack
    # on large amalgamated library files — skipping the whole file on
    # PCRE match-limit error is strictly better than aborting the run.
    func_pattern = r"let\s+(?:rec\s+)?(\w+).*?(?:requires\s*\{(.*?)\})?.*?(?:ensures\s*\{(.*?)\})"s
    func_matches = try
        collect(eachmatch(func_pattern, content))
    catch e
        Any[]
    end
    for m in func_matches
        name = m.captures[1]
        requires = m.captures[2]
        ensures = m.captures[3]
        if ensures !== nothing
            ensures_clean = first(replace(strip(ensures), r"\s+" => " "), 200)
            tactics = requires !== nothing ? ["ensures", "requires"] : ["ensures"]
            push!(results, Dict{String,Any}(
                "theorem" => "$(name)_spec",
                "goal" => "ensures { $(ensures_clean) }",
                "kind" => "function_spec",
                "tactics" => tactics,
                "source" => "why3/$(basename(filepath))",
            ))
        end
    end

    return results
end

# ---------------------------------------------------------------------------
# Downloader
# ---------------------------------------------------------------------------

"""
    download_why3_files() -> Int

Attempt to download Why3 example files. Returns count of downloaded/cached files.
"""
function download_why3_files()::Int
    downloaded = 0
    for rel_path in WHY3_FILES
        url = "$(WHY3_RAW)/$(rel_path)"
        local_path = joinpath(EXTERNAL_DIR, basename(rel_path))
        if isfile(local_path)
            downloaded += 1
            continue
        end
        try
            data = download(url, local_path)
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
    generate_synthetic_why3() -> Vector{Dict{String,Any}}

Generate high-quality synthetic Why3 proofs using WhyML syntax.
"""
function generate_synthetic_why3()::Vector{Dict{String,Any}}
    arithmetic = [
        ("add_comm", "forall x y: int. x + y = y + x", ""),
        ("add_assoc", "forall x y z: int. (x + y) + z = x + (y + z)", ""),
        ("mul_comm", "forall x y: int. x * y = y * x", ""),
        ("mul_assoc", "forall x y z: int. (x * y) * z = x * (y * z)", ""),
        ("distrib_left", "forall x y z: int. x * (y + z) = x * y + x * z", ""),
        ("add_zero", "forall x: int. x + 0 = x", ""),
        ("mul_one", "forall x: int. x * 1 = x", ""),
        ("mul_zero", "forall x: int. x * 0 = 0", ""),
        ("sub_self", "forall x: int. x - x = 0", ""),
        ("neg_neg", "forall x: int. -(-x) = x", ""),
        ("abs_nonneg", "forall x: int. abs x >= 0", ""),
        ("abs_pos", "forall x: int. x > 0 -> abs x = x", ""),
        ("abs_neg", "forall x: int. x < 0 -> abs x = -x", ""),
        ("div_mod", "forall a b: int. b <> 0 -> a = b * div a b + mod a b", ""),
        ("mod_bounds", "forall a: int, b: int. b > 0 -> 0 <= mod a b < b", ""),
    ]

    sorting = [
        ("insertion_sort_sorted", "forall a: array int. let b = insertion_sort a in sorted b", "ensures { sorted result } ensures { permut_all (old a) result }"),
        ("insertion_sort_permut", "forall a: array int. let b = insertion_sort a in permut_all a b", "ensures { permut_all (old a) result }"),
        ("selection_sort_sorted", "forall a: array int. let b = selection_sort a in sorted b", "ensures { sorted result }"),
        ("merge_sorted", "forall l1 l2: list int. sorted_list l1 -> sorted_list l2 -> sorted_list (merge l1 l2)", ""),
        ("merge_permut", "forall l1 l2: list int. permut (merge l1 l2) (l1 ++ l2)", ""),
        ("mergesort_sorted", "forall l: list int. sorted_list (mergesort l)", "ensures { sorted_list result }"),
        ("mergesort_permut", "forall l: list int. permut (mergesort l) l", "ensures { permut result l }"),
        ("binary_search_found", "forall a: array int, v: int. sorted a -> (exists i. 0 <= i < length a /\\ a[i] = v) -> let r = binary_search a v in 0 <= r < length a /\\ a[r] = v", "ensures { 0 <= result < length a } ensures { a[result] = v }"),
        ("binary_search_not_found", "forall a: array int, v: int. sorted a -> (forall i. 0 <= i < length a -> a[i] <> v) -> binary_search a v = -1", "ensures { result = -1 }"),
        ("partition_spec", "forall a: array int, lo hi: int. lo <= hi -> let (a', p) = partition a lo hi in lo <= p <= hi /\\ (forall i. lo <= i < p -> a'[i] <= a'[p]) /\\ (forall i. p < i <= hi -> a'[i] >= a'[p])", ""),
    ]

    data_structures = [
        ("list_append_nil", "forall l: list 'a. l ++ Nil = l", ""),
        ("list_append_assoc", "forall l1 l2 l3: list 'a. (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)", ""),
        ("list_length_append", "forall l1 l2: list 'a. length (l1 ++ l2) = length l1 + length l2", ""),
        ("list_reverse_reverse", "forall l: list 'a. reverse (reverse l) = l", ""),
        ("list_length_reverse", "forall l: list 'a. length (reverse l) = length l", ""),
        ("list_mem_append", "forall x: 'a, l1 l2: list 'a. mem x (l1 ++ l2) <-> mem x l1 \\/ mem x l2", ""),
        ("list_map_length", "forall f: 'a -> 'b, l: list 'a. length (map f l) = length l", ""),
        ("list_map_compose", "forall f: 'b -> 'c, g: 'a -> 'b, l: list 'a. map f (map g l) = map (fun x -> f (g x)) l", ""),
        ("queue_fifo", "forall q: queue 'a, x: 'a. let q' = push q x in peek (q') = if is_empty q then x else peek q", ""),
        ("stack_lifo", "forall s: stack 'a, x: 'a. peek (push s x) = x", ""),
    ]

    program_verification = [
        ("loop_invariant_sum", "let sum (a: array int) (n: int) : int requires { n = length a } ensures { result = sum_func a 0 n } = let ref s = 0 in for i = 0 to n - 1 do invariant { s = sum_func a 0 i } s <- s + a[i] done; s",
         "requires { n = length a } ensures { result = sum_func a 0 n } invariant { s = sum_func a 0 i }"),
        ("factorial_correct", "let rec factorial (n: int) : int requires { n >= 0 } ensures { result = fact n } variant { n } = if n = 0 then 1 else n * factorial (n - 1)",
         "requires { n >= 0 } ensures { result = fact n } variant { n }"),
        ("fibonacci_correct", "let rec fib (n: int) : int requires { n >= 0 } ensures { result = fibonacci n } variant { n } = if n <= 1 then n else fib (n - 1) + fib (n - 2)",
         "requires { n >= 0 } ensures { result = fibonacci n } variant { n }"),
        ("gcd_correct", "let rec gcd (a b: int) : int requires { a >= 0 /\\ b >= 0 } ensures { result = Gcd.gcd a b } variant { b } = if b = 0 then a else gcd b (mod a b)",
         "requires { a >= 0 /\\ b >= 0 } ensures { result = Gcd.gcd a b } variant { b }"),
        ("power_correct", "let rec power (x n: int) : int requires { n >= 0 } ensures { result = pow x n } variant { n } = if n = 0 then 1 else if mod n 2 = 0 then let p = power x (div n 2) in p * p else x * power x (n - 1)",
         "requires { n >= 0 } ensures { result = pow x n } variant { n }"),
        ("max_correct", "let max (a b: int) : int ensures { result >= a /\\ result >= b } ensures { result = a \\/ result = b } = if a >= b then a else b",
         "ensures { result >= a /\\ result >= b } ensures { result = a \\/ result = b }"),
        ("swap_correct", "let swap (a: array 'a) (i j: int) : unit requires { 0 <= i < length a /\\ 0 <= j < length a } ensures { a[i] = old a[j] /\\ a[j] = old a[i] } ensures { forall k. k <> i -> k <> j -> a[k] = old a[k] }",
         "requires { 0 <= i < length a /\\ 0 <= j < length a } ensures { a[i] = old a[j] /\\ a[j] = old a[i] }"),
        ("dutch_flag", "let dutch_flag (a: array color) : unit ensures { sorted_colors a } ensures { permut_all (old a) a } = let ref r = 0 in let ref w = 0 in let ref b = length a - 1 in while w <= b do invariant { ... } variant { b - w + 1 } ... done",
         "ensures { sorted_colors result } ensures { permut_all (old a) a } invariant { ... } variant { b - w + 1 }"),
        ("ring_buffer_push", "let push (rb: ring_buffer 'a) (x: 'a) : unit requires { not is_full rb } ensures { length rb = old (length rb) + 1 }",
         "requires { not is_full rb } ensures { length rb = old (length rb) + 1 }"),
        ("ring_buffer_pop", "let pop (rb: ring_buffer 'a) : 'a requires { not is_empty rb } ensures { length rb = old (length rb) - 1 }",
         "requires { not is_empty rb } ensures { length rb = old (length rb) - 1 }"),
    ]

    graph_algorithms = [
        ("dfs_visited", "forall g: graph, s: vertex. let v = dfs g s in forall u: vertex. mem u v <-> reachable g s u", "ensures { forall u. mem u result <-> reachable g s u }"),
        ("bfs_shortest", "forall g: graph, s: vertex. let d = bfs g s in forall u: vertex. d[u] = shortest_path g s u", "ensures { forall u. result[u] = shortest_path g s u }"),
        ("dijkstra_correct", "forall g: weighted_graph, s: vertex. let d = dijkstra g s in forall u: vertex. d[u] = shortest_weighted_path g s u", "ensures { forall u. result[u] = shortest_weighted_path g s u }"),
        ("topological_sort_valid", "forall g: dag. let l = topological_sort g in forall (u v: vertex). edge g u v -> index l u < index l v", "ensures { forall u v. edge g u v -> index result u < index result v }"),
        ("mst_correct", "forall g: connected_weighted_graph. let t = kruskal g in is_spanning_tree t g /\\ weight t = min_spanning_weight g", "ensures { is_spanning_tree result g } ensures { weight result = min_spanning_weight g }"),
    ]

    all_categories = [
        ("arithmetic", arithmetic),
        ("sorting", sorting),
        ("data_structures", data_structures),
        ("program_verification", program_verification),
        ("graph_algorithms", graph_algorithms),
    ]

    proofs = Dict{String,Any}[]
    for (category, theorems) in all_categories
        for entry in theorems
            name, goal = entry[1], entry[2]
            spec = length(entry) > 2 ? entry[3] : ""
            keywords = [lowercase(k.match) for k in eachmatch(r"\b(forall|exists|ensures|requires|invariant|variant|raises|sorted|permut|mem|length)\b"i, goal * " " * spec)]
            # Deduplicate preserving order, limit to 20
            seen = Set{String}()
            unique_kw = String[]
            for kw in keywords
                if kw ∉ seen
                    push!(seen, kw)
                    push!(unique_kw, kw)
                end
                length(unique_kw) >= 20 && break
            end
            push!(proofs, Dict{String,Any}(
                "theorem" => name,
                "goal" => goal,
                "tactic_proof" => spec,
                "tactics" => unique_kw,
                "source" => "why3_synthetic/$(category)",
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

    println("[Why3] Phase 1: Attempting to download from GitLab ...")
    downloaded = download_why3_files()
    println("  Downloaded/cached $(downloaded) files")

    # Widening (2026-04-18): additionally walk a full clone of the
    # Why3 project at external_corpora/why3_full/ (canonical source
    # is gitlab.inria.fr/why3/why3.git). Accepts .mlw (source) and
    # .why (library) files.
    src_files = String[]
    for fname in readdir(EXTERNAL_DIR)
        (endswith(fname, ".mlw") || endswith(fname, ".why")) &&
            push!(src_files, joinpath(EXTERNAL_DIR, fname))
    end
    full_root = joinpath(dirname(EXTERNAL_DIR), "why3_full")
    if isdir(full_root)
        println("[Why3] Walking full clone at $(full_root) ...")
        for (root, _dirs, files) in walkdir(full_root)
            for fname in files
                (endswith(fname, ".mlw") || endswith(fname, ".why")) &&
                    push!(src_files, joinpath(root, fname))
            end
        end
    end
    # 2026-04-18 (echidna#12 100K push): also walk the sibling
    # gitlab.inria.fr/why3/why3 clone (why3-examples) — adds ~1 552
    # further .mlw/.why files from the main upstream project (beyond
    # the curated why3_full/ clone).
    examples_root = joinpath(dirname(EXTERNAL_DIR), "why3-examples")
    if isdir(examples_root)
        println("[Why3] Walking why3-examples clone at $(examples_root) ...")
        for (root, _dirs, files) in walkdir(examples_root)
            for fname in files
                (endswith(fname, ".mlw") || endswith(fname, ".why")) &&
                    push!(src_files, joinpath(root, fname))
            end
        end
    end
    println("  $(length(src_files)) Why3 source files to parse")

    processed = 0
    for fpath in src_files
        parsed = parse_why3_file(fpath)
        append!(all_entries, parsed)
        processed += 1
        if processed % 200 == 0
            println("  processed $(processed)/$(length(src_files)) files — running count: $(length(all_entries))")
        end
    end
    extracted_count = length(all_entries)

    println("[Why3] Phase 2: Generating synthetic proofs ...")
    synthetic = generate_synthetic_why3()
    existing_names = Set(e["theorem"] for e in all_entries)
    added = 0
    for entry in synthetic
        if entry["theorem"] ∉ existing_names
            push!(all_entries, entry)
            push!(existing_names, entry["theorem"])
            added += 1
        end
    end
    println("  Generated $(added) unique synthetic proofs")

    current_id = START_ID
    output_records = Dict{String,Any}[]
    for entry in all_entries
        record = Dict{String,Any}(
            "id" => current_id,
            "prover" => "Why3",
            "theorem" => entry["theorem"],
            "goal" => entry["goal"],
            "context" => get(entry, "tactics", String[]),
            "tactic_proof" => get(entry, "tactic_proof", ""),
            "source" => get(entry, "source", "why3"),
        )
        push!(output_records, record)
        current_id += 1
    end

    open(OUTPUT_FILE, "w") do fh
        for rec in output_records
            println(fh, JSON3.write(rec))
        end
    end

    stats = Dict{String,Any}(
        "prover" => "Why3",
        "total_proofs" => length(output_records),
        "extracted_from_source" => extracted_count,
        "synthetic_added" => length(output_records) - extracted_count,
        "id_range" => [START_ID, current_id - 1],
        "output_file" => OUTPUT_FILE,
    )
    open(STATS_FILE, "w") do fh
        JSON3.pretty(fh, stats)
    end

    println("\n[Why3] COMPLETE: $(length(output_records)) proofs written to $(OUTPUT_FILE)")
    println("  Extracted from source: $(extracted_count)")
    println("  Synthetic: $(length(output_records) - extracted_count)")
    return (extracted_count, length(output_records) - extracted_count)
end

if abspath(PROGRAM_FILE) == abspath(@__FILE__)
    run()
end
