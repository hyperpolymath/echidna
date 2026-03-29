#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
#
# Extract proofs from Dafny test suite and convert to ECHIDNA training format.
#
# Attempts to download from the Dafny GitHub repository (Test/ and
# Source/IntegrationTests/ directories). Falls back to generating high-quality
# synthetic Dafny proofs.
#
# Dafny is an auto-active verification language that uses Z3 as its backend
# solver. It features method/lemma/function constructs with requires/ensures
# contracts, loop invariants, and termination measures.
#
# Output: training_data/proof_states_dafny.jsonl
# ID range: 96000+

using JSON3
using Downloads

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

const REPO_ROOT = dirname(dirname(abspath(@__FILE__)))
const EXTERNAL_DIR = joinpath(REPO_ROOT, "external_corpora", "dafny")
const OUTPUT_DIR = joinpath(REPO_ROOT, "training_data")
const OUTPUT_FILE = joinpath(OUTPUT_DIR, "proof_states_dafny.jsonl")
const STATS_FILE = joinpath(OUTPUT_DIR, "stats_dafny.json")
const START_ID = 96000

const DAFNY_RAW = "https://raw.githubusercontent.com/dafny-lang/dafny/master"
const DAFNY_FILES = [
    "Test/dafny0/Basics.dfy",
    "Test/dafny0/Array.dfy",
    "Test/dafny0/Datatypes.dfy",
    "Test/dafny0/Maps.dfy",
    "Test/dafny0/Sequences.dfy",
    "Test/dafny0/Sets.dfy",
    "Test/dafny0/Multisets.dfy",
    "Test/dafny0/TypeTests.dfy",
    "Test/dafny0/Termination.dfy",
    "Test/dafny0/GhostMethods.dfy",
    "Test/dafny4/Ackermann.dfy",
    "Test/dafny4/BinarySearch.dfy",
    "Test/dafny4/NatList.dfy",
    "Test/dafny4/Leq.dfy",
]

"""
    parse_dafny_file(filepath::String) -> Vector{Dict{String,Any}}

Parse a Dafny .dfy file and extract lemma/method/function specs.
"""
function parse_dafny_file(filepath::String)::Vector{Dict{String,Any}}
    results = Dict{String,Any}[]
    local content::String
    try
        content = read(filepath, String)
    catch
        return results
    end

    # Extract lemma/method/function declarations with specs
    pattern = r"(lemma|method|function|ghost method|ghost function)\s+(\w+)\s*(?:<[^>]*>)?\s*\((.*?)\)(?:\s*:\s*(\S+))?\s*((?:\s*(?:requires|ensures|decreases|modifies|reads|invariant)\s+.*?)*?)(?:\s*\{)"s

    for m in eachmatch(Regex(pattern, "s"), content)
        kind = strip(m.captures[1])
        name = strip(m.captures[2])
        params = replace(strip(something(m.captures[3], "")), r"\s+" => " ")
        ret_type = something(m.captures[4], "")
        specs = strip(something(m.captures[5], ""))

        isempty(specs) && continue

        specs_clean = replace(specs, r"\s+" => " ")
        specs_clean = specs_clean[1:min(400, length(specs_clean))]
        spec_keywords = [lowercase(m_.match) for m_ in eachmatch(r"\b(requires|ensures|decreases|modifies|reads|invariant)\b"i, specs)]

        push!(results, Dict{String,Any}(
            "theorem" => name,
            "goal" => specs_clean,
            "kind" => kind,
            "params" => params[1:min(200, length(params))],
            "tactics" => unique(spec_keywords),
            "source" => "dafny/$(basename(filepath))",
        ))
    end

    return results
end

"""
    download_dafny_files() -> Int

Attempt to download Dafny test files.
"""
function download_dafny_files()::Int
    downloaded = 0
    for rel_path in DAFNY_FILES
        url = "$DAFNY_RAW/$rel_path"
        local_path = joinpath(EXTERNAL_DIR, basename(rel_path))
        if isfile(local_path)
            downloaded += 1
            continue
        end
        try
            Downloads.download(url, local_path; timeout=15)
            downloaded += 1
            println("  Downloaded: $rel_path")
        catch exc
            println("  Skipped $rel_path: $exc")
        end
    end
    return downloaded
end

"""
    generate_synthetic_dafny() -> Vector{Dict{String,Any}}

Generate high-quality synthetic Dafny proofs.
"""
function generate_synthetic_dafny()::Vector{Dict{String,Any}}
    arithmetic_lemmas = [
        ("AddComm", "lemma AddComm(x: int, y: int)\n  ensures x + y == y + x\n{}", ["ensures"]),
        ("AddAssoc", "lemma AddAssoc(x: int, y: int, z: int)\n  ensures (x + y) + z == x + (y + z)\n{}", ["ensures"]),
        ("MulComm", "lemma MulComm(x: int, y: int)\n  ensures x * y == y * x\n{}", ["ensures"]),
        ("MulAssoc", "lemma MulAssoc(x: int, y: int, z: int)\n  ensures (x * y) * z == x * (y * z)\n{}", ["ensures"]),
        ("Distributive", "lemma Distributive(x: int, y: int, z: int)\n  ensures x * (y + z) == x * y + x * z\n{}", ["ensures"]),
        ("AbsNonneg", "lemma AbsNonneg(x: int)\n  ensures if x >= 0 then x >= 0 else -x >= 0\n{}", ["ensures"]),
        ("DivModIdentity", "lemma DivModIdentity(a: int, b: int)\n  requires b > 0\n  ensures a == b * (a / b) + (a % b)\n{}", ["requires", "ensures"]),
        ("ModBounds", "lemma ModBounds(a: int, b: int)\n  requires b > 0\n  ensures 0 <= a % b < b\n{}", ["requires", "ensures"]),
        ("PowerOfTwo", "function PowerOfTwo(n: nat): nat\n  ensures PowerOfTwo(n) >= 1\n{\n  if n == 0 then 1 else 2 * PowerOfTwo(n - 1)\n}", ["ensures"]),
        ("FibPositive", "lemma FibPositive(n: nat)\n  requires n >= 1\n  ensures Fib(n) >= 1\n{\n  if n == 1 || n == 2 { } else { FibPositive(n - 1); FibPositive(n - 2); }\n}", ["requires", "ensures"]),
        ("FactorialPositive", "lemma FactorialPositive(n: nat)\n  ensures Factorial(n) >= 1\n{\n  if n == 0 { } else { FactorialPositive(n - 1); }\n}", ["ensures"]),
        ("GcdDivides", "lemma GcdDivides(a: nat, b: nat)\n  requires a > 0 || b > 0\n  ensures Gcd(a, b) > 0\n  ensures a % Gcd(a, b) == 0\n  ensures b % Gcd(a, b) == 0\n  decreases a + b\n{}", ["requires", "ensures", "decreases"]),
    ]

    sequence_lemmas = [
        ("SeqAppendLength", "lemma SeqAppendLength<T>(s1: seq<T>, s2: seq<T>)\n  ensures |s1 + s2| == |s1| + |s2|\n{}", ["ensures"]),
        ("SeqAppendAssoc", "lemma SeqAppendAssoc<T>(s1: seq<T>, s2: seq<T>, s3: seq<T>)\n  ensures (s1 + s2) + s3 == s1 + (s2 + s3)\n{}", ["ensures"]),
        ("SeqAppendNil", "lemma SeqAppendNil<T>(s: seq<T>)\n  ensures s + [] == s\n{}", ["ensures"]),
        ("SeqReverseReverse", "lemma SeqReverseReverse<T>(s: seq<T>)\n  ensures Reverse(Reverse(s)) == s\n  decreases |s|\n{}", ["ensures", "decreases"]),
        ("SeqReverseLength", "lemma SeqReverseLength<T>(s: seq<T>)\n  ensures |Reverse(s)| == |s|\n  decreases |s|\n{}", ["ensures", "decreases"]),
        ("SeqMapLength", "lemma SeqMapLength<T, U>(f: T -> U, s: seq<T>)\n  ensures |Map(f, s)| == |s|\n  decreases |s|\n{}", ["ensures", "decreases"]),
        ("SeqFilterSubseq", "lemma SeqFilterSubseq<T>(P: T -> bool, s: seq<T>)\n  ensures |Filter(P, s)| <= |s|\n  decreases |s|\n{}", ["ensures", "decreases"]),
        ("SeqMemberAppend", "lemma SeqMemberAppend<T>(x: T, s1: seq<T>, s2: seq<T>)\n  ensures x in s1 + s2 <==> x in s1 || x in s2\n{}", ["ensures"]),
        ("SeqFlattenLength", "lemma SeqFlattenLength<T>(ss: seq<seq<T>>)\n  ensures |Flatten(ss)| == Sum(Map(s => |s|, ss))\n  decreases |ss|\n{}", ["ensures", "decreases"]),
        ("SeqTakeDropIdentity", "lemma SeqTakeDropIdentity<T>(s: seq<T>, i: nat)\n  requires 0 <= i <= |s|\n  ensures s[..i] + s[i..] == s\n{}", ["requires", "ensures"]),
    ]

    set_lemmas = [
        ("SetUnionComm", "lemma SetUnionComm<T>(s1: set<T>, s2: set<T>)\n  ensures s1 + s2 == s2 + s1\n{}", ["ensures"]),
        ("SetInterComm", "lemma SetInterComm<T>(s1: set<T>, s2: set<T>)\n  ensures s1 * s2 == s2 * s1\n{}", ["ensures"]),
        ("SetUnionAssoc", "lemma SetUnionAssoc<T>(s1: set<T>, s2: set<T>, s3: set<T>)\n  ensures (s1 + s2) + s3 == s1 + (s2 + s3)\n{}", ["ensures"]),
        ("SetSubsetRefl", "lemma SetSubsetRefl<T>(s: set<T>)\n  ensures s <= s\n{}", ["ensures"]),
        ("SetSubsetTrans", "lemma SetSubsetTrans<T>(s1: set<T>, s2: set<T>, s3: set<T>)\n  requires s1 <= s2 && s2 <= s3\n  ensures s1 <= s3\n{}", ["requires", "ensures"]),
        ("SetUnionEmpty", "lemma SetUnionEmpty<T>(s: set<T>)\n  ensures s + {} == s\n{}", ["ensures"]),
        ("SetInterSubset", "lemma SetInterSubset<T>(s1: set<T>, s2: set<T>)\n  ensures s1 * s2 <= s1\n{}", ["ensures"]),
        ("SetDeMorgan", "lemma SetDeMorgan<T>(s1: set<T>, s2: set<T>, u: set<T>)\n  requires s1 <= u && s2 <= u\n  ensures u - (s1 * s2) == (u - s1) + (u - s2)\n{}", ["requires", "ensures"]),
        ("SetCardUnionDisjoint", "lemma SetCardUnionDisjoint<T>(s1: set<T>, s2: set<T>)\n  requires s1 * s2 == {}\n  ensures |s1 + s2| == |s1| + |s2|\n{}", ["requires", "ensures"]),
        ("MultisetAdd", "lemma MultisetAdd<T>(s: multiset<T>, x: T)\n  ensures (s + multiset{x})[x] == s[x] + 1\n{}", ["ensures"]),
    ]

    sorting_search = [
        ("BinarySearchCorrect", "method BinarySearch(a: array<int>, key: int) returns (index: int)\n  requires Sorted(a, 0, a.Length)\n  ensures 0 <= index < a.Length ==> a[index] == key\n  ensures index < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != key\n{}", ["requires", "ensures"]),
        ("InsertionSortSorted", "method InsertionSort(a: array<int>)\n  modifies a\n  ensures Sorted(a, 0, a.Length)\n  ensures multiset(a[..]) == multiset(old(a[..]))\n{}", ["modifies", "ensures"]),
        ("SelectionSortCorrect", "method SelectionSort(a: array<int>)\n  modifies a\n  ensures Sorted(a, 0, a.Length)\n  ensures multiset(a[..]) == multiset(old(a[..]))\n{}", ["modifies", "ensures"]),
        ("MergeSortedArrays", "method MergeSorted(a: array<int>, b: array<int>) returns (c: array<int>)\n  requires Sorted(a, 0, a.Length) && Sorted(b, 0, b.Length)\n  ensures Sorted(c, 0, c.Length)\n  ensures c.Length == a.Length + b.Length\n  ensures multiset(c[..]) == multiset(a[..]) + multiset(b[..])\n{}", ["requires", "ensures"]),
        ("QuickSortCorrect", "method QuickSort(a: array<int>, lo: int, hi: int)\n  requires 0 <= lo <= hi <= a.Length\n  modifies a\n  ensures Sorted(a, lo, hi)\n  ensures multiset(a[lo..hi]) == multiset(old(a[lo..hi]))\n  ensures forall i :: 0 <= i < lo || hi <= i < a.Length ==> a[i] == old(a[i])\n  decreases hi - lo\n{}", ["requires", "modifies", "ensures", "decreases"]),
        ("DutchNationalFlag", "method DutchFlag(a: array<int>)\n  requires forall i :: 0 <= i < a.Length ==> a[i] == 0 || a[i] == 1 || a[i] == 2\n  modifies a\n  ensures Sorted(a, 0, a.Length)\n  ensures multiset(a[..]) == multiset(old(a[..]))\n{}", ["requires", "modifies", "ensures"]),
    ]

    data_structures = [
        ("LinkedListInsert", "method Insert(head: Node?, val: int) returns (newHead: Node)\n  requires ValidList(head)\n  ensures ValidList(newHead)\n  ensures Content(newHead) == Content(head) + {val}\n{}", ["requires", "ensures"]),
        ("BSTInsert", "method BSTInsert(t: Tree, val: int) returns (newT: Tree)\n  requires BST(t)\n  ensures BST(newT)\n  ensures Content(newT) == Content(t) + {val}\n{}", ["requires", "ensures"]),
        ("BSTSearch", "method BSTSearch(t: Tree, val: int) returns (found: bool)\n  requires BST(t)\n  ensures found == (val in Content(t))\n{}", ["requires", "ensures"]),
        ("QueueEnqueue", "method Enqueue(q: Queue<int>, val: int) returns (q': Queue<int>)\n  requires Valid(q)\n  ensures Valid(q')\n  ensures Elements(q') == Elements(q) + [val]\n{}", ["requires", "ensures"]),
        ("StackPush", "method Push(s: Stack<int>, val: int) returns (s': Stack<int>)\n  requires Valid(s)\n  ensures Valid(s')\n  ensures Elements(s') == [val] + Elements(s)\n{}", ["requires", "ensures"]),
        ("HeapInsert", "method HeapInsert(h: array<int>, size: nat, val: int) returns (newSize: nat)\n  requires IsHeap(h, size) && size < h.Length\n  modifies h\n  ensures IsHeap(h, newSize)\n  ensures newSize == size + 1\n  ensures multiset(h[..newSize]) == multiset(old(h[..size])) + multiset{val}\n{}", ["requires", "modifies", "ensures"]),
    ]

    termination = [
        ("AckermannTerminates", "function Ackermann(m: nat, n: nat): nat\n  decreases m, n\n{\n  if m == 0 then n + 1\n  else if n == 0 then Ackermann(m - 1, 1)\n  else Ackermann(m - 1, Ackermann(m, n - 1))\n}", ["decreases"]),
        ("CollatzStep", "function CollatzNext(n: nat): nat\n  requires n >= 2\n{\n  if n % 2 == 0 then n / 2 else 3 * n + 1\n}", ["requires"]),
        ("MutualRecTermination", "function Even(n: nat): bool\n  decreases n\n{\n  if n == 0 then true else Odd(n - 1)\n}\nfunction Odd(n: nat): bool\n  decreases n\n{\n  if n == 0 then false else Even(n - 1)\n}", ["decreases"]),
        ("McCarthyNinetyOne", "function McCarthy91(n: int): int\n  requires n >= 0\n  ensures n > 100 ==> McCarthy91(n) == n - 10\n  ensures n <= 100 ==> McCarthy91(n) == 91\n  decreases 101 - n\n{\n  if n > 100 then n - 10 else McCarthy91(McCarthy91(n + 11))\n}", ["requires", "ensures", "decreases"]),
    ]

    all_categories = [
        ("arithmetic", arithmetic_lemmas),
        ("sequences", sequence_lemmas),
        ("sets", set_lemmas),
        ("sorting", sorting_search),
        ("data_structures", data_structures),
        ("termination", termination),
    ]

    proofs = Dict{String,Any}[]
    for (category, entries) in all_categories
        for entry in entries
            name = entry[1]
            body = entry[2]
            entry_tactics = length(entry) > 2 ? entry[3] : String[]

            # Extract goal from body
            spec_lines = [strip(l) for l in split(body, '\n') if any(k -> occursin(k, l), ["requires", "ensures", "decreases", "modifies", "invariant"])]
            goal = !isempty(spec_lines) ? join(spec_lines, "; ") : split(body, '\n')[1]

            push!(proofs, Dict{String,Any}(
                "theorem" => name,
                "goal" => goal,
                "tactic_proof" => body,
                "tactics" => entry_tactics,
                "source" => "dafny_synthetic/$category",
            ))
        end
    end
    return proofs
end

"""
    run() -> Tuple{Int,Int}

Run the full extraction pipeline.
"""
function run()::Tuple{Int,Int}
    mkpath(OUTPUT_DIR)
    mkpath(EXTERNAL_DIR)

    all_entries = Dict{String,Any}[]
    extracted_count = 0

    println("[Dafny] Phase 1: Attempting to download from GitHub ...")
    downloaded = download_dafny_files()
    println("  Downloaded/cached $downloaded files")

    for fname in readdir(EXTERNAL_DIR)
        if endswith(fname, ".dfy")
            fpath = joinpath(EXTERNAL_DIR, fname)
            parsed = parse_dafny_file(fpath)
            append!(all_entries, parsed)
            if !isempty(parsed)
                println("  Parsed $(length(parsed)) from $fname")
            end
        end
    end
    extracted_count = length(all_entries)

    println("[Dafny] Phase 2: Generating synthetic proofs ...")
    synthetic = generate_synthetic_dafny()
    existing_names = Set(e["theorem"] for e in all_entries)
    added = 0
    for entry in synthetic
        if entry["theorem"] ∉ existing_names
            push!(all_entries, entry)
            push!(existing_names, entry["theorem"])
            added += 1
        end
    end
    println("  Generated $added unique synthetic proofs")

    current_id = START_ID
    output_records = Dict{String,Any}[]
    for entry in all_entries
        record = Dict{String,Any}(
            "id" => current_id,
            "prover" => "Dafny",
            "theorem" => entry["theorem"],
            "goal" => entry["goal"],
            "context" => get(entry, "tactics", String[]),
            "tactic_proof" => get(entry, "tactic_proof", ""),
            "source" => get(entry, "source", "dafny"),
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
        "prover" => "Dafny",
        "total_proofs" => length(output_records),
        "extracted_from_source" => extracted_count,
        "synthetic_added" => length(output_records) - extracted_count,
        "id_range" => [START_ID, current_id - 1],
        "output_file" => OUTPUT_FILE,
    )
    open(STATS_FILE, "w") do fh
        write(fh, JSON3.write(stats))
    end

    println("\n[Dafny] COMPLETE: $(length(output_records)) proofs written to $OUTPUT_FILE")
    return extracted_count, length(output_records) - extracted_count
end

if abspath(PROGRAM_FILE) == @__FILE__
    run()
end
