#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
#
# Extract proofs from ACL2 community books and convert to ECHIDNA training format.
#
# Attempts to download from the ACL2 GitHub repository (books/ directory).
# Falls back to generating high-quality synthetic ACL2 proofs from standard
# patterns (defthm, defun, verify-guards).
#
# ACL2 (A Computational Logic for Applicative Common Lisp) is an industrial-
# strength theorem prover used for hardware and software verification (e.g.
# AMD floating-point division, JVM bytecode verification).
#
# Output: training_data/proof_states_acl2.jsonl
# ID range: 92000+

using JSON3
using Downloads

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

const REPO_ROOT = dirname(dirname(abspath(@__FILE__)))
const EXTERNAL_DIR = joinpath(REPO_ROOT, "external_corpora", "acl2")
const OUTPUT_DIR = joinpath(REPO_ROOT, "training_data")
const OUTPUT_FILE = joinpath(OUTPUT_DIR, "proof_states_acl2.jsonl")
const STATS_FILE = joinpath(OUTPUT_DIR, "stats_acl2.json")
const START_ID = 92000

const ACL2_RAW_BASE = "https://raw.githubusercontent.com/acl2/acl2/master"
const ACL2_FILES = [
    "books/arithmetic/top.lisp",
    "books/arithmetic-5/top.lisp",
    "books/std/lists/top.lisp",
    "books/std/lists/append.lisp",
    "books/std/lists/rev.lisp",
    "books/std/lists/nth.lisp",
    "books/std/lists/len.lisp",
    "books/std/alists/top.lisp",
    "books/ihs/ihs-definitions.lisp",
    "books/ihs/logops-lemmas.lisp",
    "books/data-structures/list-theory.lisp",
    "books/sorting/msort.lisp",
    "books/sorting/isort.lisp",
    "books/arithmetic/natp-posp.lisp",
]

"""
    parse_acl2_file(filepath::String) -> Vector{Dict{String,Any}}

Parse an ACL2 .lisp file and extract defthm forms.

ACL2 proofs look like:
    (defthm theorem-name
      body
      :hints (("Goal" :in-theory (enable ...))))
"""
function parse_acl2_file(filepath::String)::Vector{Dict{String,Any}}
    results = Dict{String,Any}[]
    local content::String
    try
        content = read(filepath, String)
    catch
        return results
    end

    # Extract defthm forms (simplified heuristic for balanced parens)
    pattern_thm = r"\(defthm\s+(\S+)\s+(.*?)(?=\n\s*\(def|\n\s*\(in-theory|\n\s*\(include-book|\z)"s

    for m in eachmatch(pattern_thm, content)
        name = strip(m.captures[1])
        body = strip(m.captures[2])
        # Clean up body
        body_clean = replace(body, r"\s+" => " ")
        body_clean = first(body_clean, 300)

        # Extract hints
        hints_match = match(r":hints\s*\((.*?)\)"s, body)
        hints = String[]
        if hints_match !== nothing
            hint_text = hints_match.captures[1]
            hints = [m_.captures[1] for m_ in eachmatch(r":(\w+)", hint_text)]
        end

        # Extract rule classes
        rules_match = match(r":rule-classes\s+(\S+)", body)
        rule_class = rules_match !== nothing ? rules_match.captures[1] : "rewrite"

        push!(results, Dict{String,Any}(
            "theorem" => name,
            "goal" => body_clean,
            "hints" => hints,
            "rule_class" => rule_class,
            "source" => "acl2/$(basename(filepath))",
        ))
    end

    return results
end

"""
    download_acl2_files() -> Int

Attempt to download ACL2 community book files.
"""
function download_acl2_files()::Int
    downloaded = 0
    for rel_path in ACL2_FILES
        url = "$ACL2_RAW_BASE/$rel_path"
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
    generate_synthetic_acl2() -> Vector{Dict{String,Any}}

Generate high-quality synthetic ACL2 proofs.

ACL2 proofs use a unique waterfall architecture: simplification,
destructor elimination, cross-fertilization, generalization, and
induction. Hints guide the prover.
"""
function generate_synthetic_acl2()::Vector{Dict{String,Any}}
    arithmetic = [
        ("commutativity-of-+", "(equal (+ x y) (+ y x))", ":rule-classes :rewrite"),
        ("associativity-of-+", "(equal (+ (+ x y) z) (+ x (+ y z)))", ":rule-classes :rewrite"),
        ("commutativity-of-*", "(equal (* x y) (* y x))", ":rule-classes :rewrite"),
        ("associativity-of-*", "(equal (* (* x y) z) (* x (* y z)))", ":rule-classes :rewrite"),
        ("distributivity-of-*-over-+", "(equal (* x (+ y z)) (+ (* x y) (* x z)))", ":rule-classes :rewrite"),
        ("right-identity-of-+", "(equal (+ x 0) x)", ":rule-classes :rewrite"),
        ("left-identity-of-*", "(equal (* 1 x) x)", ":rule-classes :rewrite"),
        ("right-cancellation-for-+", "(implies (equal (+ a x) (+ b x)) (equal a b))", ":hints ((\"Goal\" :use (:instance cancel-common)))"),
        ("natp-+", "(implies (and (natp x) (natp y)) (natp (+ x y)))", ":hints ((\"Goal\" :in-theory (enable natp)))"),
        ("natp-*", "(implies (and (natp x) (natp y)) (natp (* x y)))", ":hints ((\"Goal\" :in-theory (enable natp)))"),
        ("posp-implies-natp", "(implies (posp x) (natp x))", ":hints ((\"Goal\" :in-theory (enable posp natp)))"),
        ("<=-reflexive", "(implies (natp x) (<= x x))", ":rule-classes :rewrite"),
        ("<=-transitive", "(implies (and (<= x y) (<= y z)) (<= x z))", ":hints ((\"Goal\" :use (:instance transitivity-of-<=)))"),
        ("<=-antisymmetric", "(implies (and (<= x y) (<= y x)) (equal x y))", ":hints ((\"Goal\" :use (:instance antisymmetry-of-<=)))"),
        ("floor-bounds", "(implies (and (natp x) (posp y)) (and (<= (* y (floor x y)) x) (< x (* y (+ 1 (floor x y))))))", ":hints ((\"Goal\" :in-theory (enable floor)))"),
        ("mod-bounds", "(implies (and (natp x) (posp y)) (< (mod x y) y))", ":hints ((\"Goal\" :in-theory (enable mod)))"),
        ("mod-+-cancel", "(implies (and (natp a) (natp b) (posp n)) (equal (mod (+ a (mod b n)) n) (mod (+ a b) n)))", ":hints ((\"Goal\" :in-theory (enable mod)))"),
        ("expt-+", "(implies (and (natp m) (natp n)) (equal (expt b (+ m n)) (* (expt b m) (expt b n))))", ":hints ((\"Goal\" :induct (expt b m)))"),
        ("evenp-+-2", "(implies (evenp x) (evenp (+ 2 x)))", ":hints ((\"Goal\" :in-theory (enable evenp)))"),
        ("oddp-+-2", "(implies (oddp x) (oddp (+ 2 x)))", ":hints ((\"Goal\" :in-theory (enable oddp)))"),
    ]

    lists = [
        ("true-listp-append", "(implies (true-listp x) (true-listp (append x y)))", ":hints ((\"Goal\" :induct (true-listp x)))"),
        ("append-nil", "(implies (true-listp x) (equal (append x nil) x))", ":hints ((\"Goal\" :induct (true-listp x)))"),
        ("associativity-of-append", "(equal (append (append x y) z) (append x (append y z)))", ":hints ((\"Goal\" :induct (true-listp x)))"),
        ("len-append", "(equal (len (append x y)) (+ (len x) (len y)))", ":hints ((\"Goal\" :induct (true-listp x)))"),
        ("len-revappend", "(equal (len (revappend x y)) (+ (len x) (len y)))", ":hints ((\"Goal\" :induct (revappend x y)))"),
        ("revappend-revappend", "(equal (revappend (revappend x y) z) (revappend y (append x z)))", ":hints ((\"Goal\" :induct (revappend x y)))"),
        ("reverse-reverse", "(implies (true-listp x) (equal (reverse (reverse x)) x))", ":hints ((\"Goal\" :in-theory (enable reverse)))"),
        ("member-append", "(iff (member a (append x y)) (or (member a x) (member a y)))", ":hints ((\"Goal\" :induct (true-listp x)))"),
        ("nth-of-append", "(implies (< (nfix n) (len x)) (equal (nth n (append x y)) (nth n x)))", ":hints ((\"Goal\" :induct (nth n x)))"),
        ("car-cons", "(equal (car (cons x y)) x)", ":rule-classes :rewrite"),
        ("cdr-cons", "(equal (cdr (cons x y)) y)", ":rule-classes :rewrite"),
        ("cons-car-cdr", "(implies (consp x) (equal (cons (car x) (cdr x)) x))", ":rule-classes :rewrite"),
        ("len-nonnegative", "(<= 0 (len x))", ":rule-classes :type-prescription"),
        ("true-listp-revappend", "(implies (true-listp y) (true-listp (revappend x y)))", ":hints ((\"Goal\" :induct (revappend x y)))"),
        ("nthcdr-of-append", "(implies (<= (nfix n) (len x)) (equal (nthcdr n (append x y)) (append (nthcdr n x) y)))", ":hints ((\"Goal\" :induct (nthcdr n x)))"),
    ]

    alists = [
        ("alistp-acons", "(implies (alistp a) (alistp (acons key val a)))", ":hints ((\"Goal\" :in-theory (enable acons alistp)))"),
        ("assoc-of-acons", "(equal (assoc-equal key (acons key val a)) (cons key val))", ":hints ((\"Goal\" :in-theory (enable acons assoc-equal)))"),
        ("assoc-of-acons-diff", "(implies (not (equal k1 k2)) (equal (assoc-equal k1 (acons k2 v a)) (assoc-equal k1 a)))", ":hints ((\"Goal\" :in-theory (enable acons assoc-equal)))"),
        ("strip-cars-acons", "(equal (strip-cars (acons key val a)) (cons key (strip-cars a)))", ":hints ((\"Goal\" :in-theory (enable acons strip-cars)))"),
        ("strip-cdrs-acons", "(equal (strip-cdrs (acons key val a)) (cons val (strip-cdrs a)))", ":hints ((\"Goal\" :in-theory (enable acons strip-cdrs)))"),
    ]

    bitvectors = [
        ("logand-self", "(equal (logand x x) x)", ":hints ((\"Goal\" :in-theory (enable logand)))"),
        ("logand-0", "(equal (logand x 0) 0)", ":hints ((\"Goal\" :in-theory (enable logand)))"),
        ("logior-self", "(equal (logior x x) x)", ":hints ((\"Goal\" :in-theory (enable logior)))"),
        ("logior-0", "(equal (logior x 0) x)", ":hints ((\"Goal\" :in-theory (enable logior)))"),
        ("logxor-self", "(equal (logxor x x) 0)", ":hints ((\"Goal\" :in-theory (enable logxor)))"),
        ("logxor-0", "(equal (logxor x 0) x)", ":hints ((\"Goal\" :in-theory (enable logxor)))"),
        ("lognot-lognot", "(implies (integerp x) (equal (lognot (lognot x)) x))", ":hints ((\"Goal\" :in-theory (enable lognot)))"),
        ("logand-comm", "(equal (logand x y) (logand y x))", ":hints ((\"Goal\" :in-theory (enable logand)))"),
        ("logior-comm", "(equal (logior x y) (logior y x))", ":hints ((\"Goal\" :in-theory (enable logior)))"),
        ("logxor-comm", "(equal (logxor x y) (logxor y x))", ":hints ((\"Goal\" :in-theory (enable logxor)))"),
        ("ash-0", "(equal (ash x 0) (ifix x))", ":hints ((\"Goal\" :in-theory (enable ash)))"),
        ("logbitp-of-logand", "(equal (logbitp n (logand x y)) (and (logbitp n x) (logbitp n y)))", ":hints ((\"Goal\" :in-theory (enable logbitp logand)))"),
        ("unsigned-byte-p-of-logand", "(implies (or (unsigned-byte-p n x) (unsigned-byte-p n y)) (unsigned-byte-p n (logand x y)))", ":hints ((\"Goal\" :in-theory (enable unsigned-byte-p logand)))"),
    ]

    sorting_search = [
        ("orderedp-merge", "(implies (and (orderedp x) (orderedp y)) (orderedp (merge-lists x y)))", ":hints ((\"Goal\" :induct (merge-lists x y)))"),
        ("perm-merge", "(perm (append x y) (merge-lists x y))", ":hints ((\"Goal\" :induct (merge-lists x y)))"),
        ("orderedp-msort", "(orderedp (msort x))", ":hints ((\"Goal\" :induct (msort x)))"),
        ("perm-msort", "(perm x (msort x))", ":hints ((\"Goal\" :induct (msort x)))"),
        ("orderedp-isort", "(orderedp (isort x))", ":hints ((\"Goal\" :induct (isort x)))"),
        ("perm-isort", "(perm x (isort x))", ":hints ((\"Goal\" :induct (isort x)))"),
        ("member-of-sorted", "(implies (and (orderedp x) (member a x) (member b x) (<= a b)) (member b (cdr (member a x))))", ":hints ((\"Goal\" :induct (member a x)))"),
        ("bsearch-correct", "(implies (and (orderedp arr) (member key arr)) (equal (nth (bsearch key arr) arr) key))", ":hints ((\"Goal\" :in-theory (enable bsearch)))"),
    ]

    all_categories = [
        ("arithmetic", arithmetic),
        ("lists", lists),
        ("alists", alists),
        ("bitvectors", bitvectors),
        ("sorting_search", sorting_search),
    ]

    proofs = Dict{String,Any}[]
    for (category, theorems) in all_categories
        for (name, goal, hints) in theorems
            hint_keywords = [m_.captures[1] for m_ in eachmatch(r":(\w+)", hints)]
            push!(proofs, Dict{String,Any}(
                "theorem" => name,
                "goal" => "(defthm $name $goal)",
                "tactic_proof" => "(defthm $name $goal $hints)",
                "tactics" => unique(hint_keywords)[1:min(20, length(unique(hint_keywords)))],
                "source" => "acl2_synthetic/$category",
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

    println("[ACL2] Phase 1: Attempting to download from GitHub ...")
    downloaded = download_acl2_files()
    println("  Downloaded/cached $downloaded files")

    # Widening (2026-04-18): walk a sparse acl2/acl2 clone at
    # external_corpora/acl2_full/ (only `books/` checked out). The
    # ACL2 Community Books are the canonical proof corpus and hold
    # tens of thousands of named theorems across hundreds of books.
    # Accept .lisp and .acl2 files.
    src_files = String[]
    for fname in readdir(EXTERNAL_DIR)
        (endswith(fname, ".lisp") || endswith(fname, ".acl2")) &&
            push!(src_files, joinpath(EXTERNAL_DIR, fname))
    end
    full_root = joinpath(dirname(EXTERNAL_DIR), "acl2_full")
    if isdir(full_root)
        println("[ACL2] Walking full clone at $(full_root) ...")
        for (root, _dirs, files) in walkdir(full_root)
            for fname in files
                (endswith(fname, ".lisp") || endswith(fname, ".acl2")) &&
                    push!(src_files, joinpath(root, fname))
            end
        end
    end
    println("  $(length(src_files)) ACL2 source files to parse")

    processed = 0
    for fpath in src_files
        parsed = parse_acl2_file(fpath)
        append!(all_entries, parsed)
        processed += 1
        if processed % 500 == 0
            println("  processed $(processed)/$(length(src_files)) files — running count: $(length(all_entries))")
        end
    end
    extracted_count = length(all_entries)

    println("[ACL2] Phase 2: Generating synthetic proofs ...")
    synthetic = generate_synthetic_acl2()
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
            "prover" => "ACL2",
            "theorem" => entry["theorem"],
            "goal" => entry["goal"],
            "context" => get(entry, "tactics", get(entry, "hints", String[])),
            "tactic_proof" => get(entry, "tactic_proof", ""),
            "source" => get(entry, "source", "acl2"),
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
        "prover" => "ACL2",
        "total_proofs" => length(output_records),
        "extracted_from_source" => extracted_count,
        "synthetic_added" => length(output_records) - extracted_count,
        "id_range" => [START_ID, current_id - 1],
        "output_file" => OUTPUT_FILE,
    )
    open(STATS_FILE, "w") do fh
        write(fh, JSON3.write(stats))
    end

    println("\n[ACL2] COMPLETE: $(length(output_records)) proofs written to $OUTPUT_FILE")
    println("  Extracted from source: $extracted_count")
    println("  Synthetic: $(length(output_records) - extracted_count)")
    return extracted_count, length(output_records) - extracted_count
end

if abspath(PROGRAM_FILE) == @__FILE__
    run()
end
