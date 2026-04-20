#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# extract_isabelle_tropical.jl
#
# Extract lemma/theorem/instance proofs from the tropical-resource-typing
# Isabelle/HOL theory files and emit ECHIDNA training records.
#
# Source files parsed (all in TROPICAL_SRC_DIR):
#   Tropical_v2.thy          — 950 lines, 0 sorries (primary source)
#   Tropical_Matrices_Full.thy — matrix algebra lemmas with proofs
#   Tropical_Kleene.thy        — Kleene star, star equation, prefixpoint
#   Tropical_CNO.thy           — Certified Null Operation instances
#
# Output: training_data/proof_states_isabelle.jsonl
# ID range: 200000+
#
# Schema matches existing ECHIDNA corpus records:
#   { "id", "prover", "theorem", "goal", "context", "tactic_proof", "source" }

using JSON3

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

const REPO_ROOT       = dirname(dirname(abspath(@__FILE__)))
const OUTPUT_DIR      = joinpath(REPO_ROOT, "training_data")
const OUTPUT_FILE     = joinpath(OUTPUT_DIR, "proof_states_isabelle.jsonl")
const STATS_FILE      = joinpath(OUTPUT_DIR, "stats_isabelle_tropical.json")
const START_ID        = 200000

# Path to the tropical-resource-typing repo (sibling of neural-foundations).
# Adjust if your checkout differs.
const TROPICAL_REPO   = abspath(joinpath(REPO_ROOT, "..", "..", "..", "..", "tropical-resource-typing"))

const THY_FILES = [
    ("Tropical_v2.thy",            "tropical_v2"),
    ("Tropical_Matrices_Full.thy", "tropical_matrices_full"),
    ("Tropical_Kleene.thy",        "tropical_kleene"),
    ("Tropical_CNO.thy",           "tropical_cno"),
]

# ---------------------------------------------------------------------------
# Isabelle tactic names we track for the context field
# ---------------------------------------------------------------------------

const KNOWN_TACTICS = [
    "simp", "simp_all", "auto", "blast", "force", "fastforce",
    "cases", "case", "induction", "induct",
    "rule", "erule", "drule", "frule",
    "apply", "by", "qed", "proof",
    "intro", "elim", "dest",
    "subst", "rewrite", "unfold", "unfolding",
    "show", "have", "obtain", "assume", "fix",
    "contradiction", "absurd", "exI", "conjI", "disjI1", "disjI2",
    "split", "split_ifs",
    "sum.cong", "sum.delta", "sum.swap", "sum.UNION_disjoint",
    "rule antisym", "rule order_antisym",
    "tropical_arith", "tropm_arith",
    "metis", "meson", "smt",
    "arith", "omega", "linarith",
    "transfer",
    "norm_num",
]

"""
    extract_tactics(proof_text::String) -> Vector{String}

Return (deduplicated, ordered) list of tactic names found in a proof block.
"""
function extract_tactics(proof_text::String)::Vector{String}
    found = String[]
    lower = lowercase(proof_text)
    for t in KNOWN_TACTICS
        if occursin(t, lower)
            push!(found, t)
        end
    end
    return unique(found)
end

# ---------------------------------------------------------------------------
# Isabelle .thy parser
# ---------------------------------------------------------------------------

"""
    IsabelleEntry

Represents a single extracted lemma/theorem/instance proof.
"""
struct IsabelleEntry
    name::String
    goal::String        # The statement (everything between name and proof keyword)
    proof::String       # The full proof text
    source_file::String
end

"""
    parse_thy_file(path::String, tag::String) -> Vector{IsabelleEntry}

Parse an Isabelle .thy file and extract lemma/theorem proof pairs.

Handles three common proof styles:
  1. `by (...)` or `by simp` — single-step proof
  2. `proof ... qed` — block proof
  3. `unfolding ... by ...` — rewrite + close

Does NOT parse `instance` blocks (too complex to reliably extract goals).
Skips sorried proofs.
"""
function parse_thy_file(path::String, tag::String)::Vector{IsabelleEntry}
    entries = IsabelleEntry[]
    isfile(path) || (println("  [SKIP] file not found: $path"); return entries)

    content = read(path, String)
    lines   = split(content, '\n')
    nlines  = length(lines)

    i = 1
    while i <= nlines
        line = lines[i]

        # Detect declaration: lemma/theorem/corollary/proposition
        m = match(r"^\s*(lemma|theorem|corollary|proposition)\s+([A-Za-z_][A-Za-z0-9_']*)", line)
        if m === nothing
            i += 1
            continue
        end

        decl_kind = m.captures[1]
        name      = strip(string(m.captures[2]))

        # Collect goal lines: everything from the declaration until we see
        # a proof keyword (`proof`, `by`, `unfolding`, `apply`, `sorry`).
        goal_lines = String[]
        j = i + 1
        while j <= nlines
            gl = lines[j]
            if occursin(r"^\s*(proof|by |unfolding|apply|sorry)\b", gl)
                break
            end
            push!(goal_lines, rstrip(gl))
            j += 1
        end

        goal_text = join(filter(!isempty, goal_lines), " ")
        # Strip leading/trailing whitespace and Isabelle quoting artefacts
        goal_text = replace(goal_text, r"\s+" => " ")
        goal_text = strip(goal_text)

        # Skip if goal is empty (e.g. `lemma foo` followed immediately by `proof`)
        if isempty(goal_text)
            # Still try to grab the statement from the declaration line itself
            rest = replace(line, r"^\s*(lemma|theorem|corollary|proposition)\s+[A-Za-z_][A-Za-z0-9_']*" => "")
            rest = strip(rest)
            goal_text = isempty(rest) ? "(see source)" : rest
        end

        # Collect the proof block starting at line j
        proof_lines = String[]
        proof_start = j

        # Case 1: sorry — skip this entry
        if j <= nlines && occursin(r"^\s*sorry\b", lines[j])
            i = j + 1
            continue
        end

        # Case 2: single-step `by (...)` or `by simp` or `unfolding ... by ...`
        if j <= nlines && occursin(r"^\s*(by|unfolding)\b", lines[j])
            # Grab contiguous by/unfolding lines (sometimes multi-line)
            while j <= nlines && (occursin(r"^\s*(by|unfolding)\b", lines[j]) ||
                                   (j > proof_start && !isempty(strip(lines[j])) &&
                                    !occursin(r"^\s*(lemma|theorem|corollary|proposition|instance|section|subsection|text|end\b)", lines[j])))
                push!(proof_lines, rstrip(lines[j]))
                j += 1
                # Stop if we've consumed more than 10 continuation lines
                j - proof_start > 10 && break
            end
            # One more check: next non-empty line that starts a new declaration ends it
        # Case 3: block proof `proof ... qed`
        elseif j <= nlines && occursin(r"^\s*proof\b", lines[j])
            depth = 0
            while j <= nlines
                pl = lines[j]
                if occursin(r"^\s*proof\b", pl)
                    depth += 1
                elseif occursin(r"^\s*qed\b", pl)
                    depth -= 1
                    push!(proof_lines, rstrip(pl))
                    j += 1
                    depth == 0 && break
                    continue
                end
                # Skip if sorry appears inside block proof
                if occursin(r"\bsorry\b", pl)
                    proof_lines = String[]  # mark as skipped
                    j += 1
                    while j <= nlines && !occursin(r"^\s*qed\b", lines[j])
                        j += 1
                    end
                    j += 1  # skip final qed
                    break
                end
                push!(proof_lines, rstrip(pl))
                j += 1
            end
        # Case 4: apply-style proof
        elseif j <= nlines && occursin(r"^\s*apply\b", lines[j])
            while j <= nlines
                pl = lines[j]
                push!(proof_lines, rstrip(pl))
                j += 1
                occursin(r"^\s*done\b", pl) && break
                occursin(r"^\s*sorry\b", pl) && (proof_lines = String[]; break)
                # Stop at next declaration
                occursin(r"^\s*(lemma|theorem|corollary|proposition|instance|section|subsection)\b", pl) &&
                    (j -= 1; break)
            end
        end

        # Skip sorry entries
        if isempty(proof_lines) || any(pl -> occursin(r"\bsorry\b", pl), proof_lines)
            i = j
            continue
        end

        proof_text = join(proof_lines, "\n")

        push!(entries, IsabelleEntry(name, goal_text, proof_text, tag))
        i = j
    end

    return entries
end

# ---------------------------------------------------------------------------
# Synthetic corpus: high-quality Isabelle/HOL algebra examples
# ---------------------------------------------------------------------------

"""
    synthetic_isabelle_algebra() -> Vector{IsabelleEntry}

Generate synthetic Isabelle/HOL proof entries covering the tactic patterns
most commonly needed for tropical semiring proofs.  These supplement the
extracted proofs and ensure the vocabulary covers key tactics.
"""
function synthetic_isabelle_algebra()::Vector{IsabelleEntry}
    entries = IsabelleEntry[]

    # Format: (name, goal_text, proof_text)
    raw = [
        # --- Nat arithmetic patterns ---
        ("nat_add_comm",
         "\"(m :: nat) + n = n + m\"",
         "by (rule Nat.add_commute)"),
        ("nat_max_idem",
         "\"max (n :: nat) n = n\"",
         "by simp"),
        ("nat_max_comm",
         "\"max (a :: nat) b = max b a\"",
         "by (simp add: max.commute)"),
        ("nat_max_assoc",
         "\"max (max (a :: nat) b) c = max a (max b c)\"",
         "by (simp add: max.assoc)"),
        ("nat_add_distrib_max",
         "\"(k :: nat) + max m n = max (k + m) (k + n)\"",
         "by simp"),

        # --- Typeclass instance proof pattern ---
        ("comm_monoid_add_zero_left",
         "\"(0 :: 'a :: comm_monoid_add) + a = a\"",
         "by simp"),
        ("semiring_distrib_left",
         "\"a * (b + c) = a * b + a * c\" for a b c :: \"'a :: semiring\"",
         "by (rule distrib_left)"),

        # --- Finite set sum patterns (tropical sums) ---
        ("sum_cong_eq",
         "\"f = g \\<Longrightarrow> (\\<Sum> x \\<in> A. f x) = (\\<Sum> x \\<in> A. g x)\"",
         "by simp"),
        ("sum_delta_finite",
         "\"finite A \\<Longrightarrow> j \\<in> A \\<Longrightarrow> (\\<Sum> k \\<in> A. if k = j then f k else 0) = f j\"",
         "by (simp add: sum.delta)"),
        ("sum_union_disjoint",
         "\"finite A \\<Longrightarrow> finite B \\<Longrightarrow> A \\<inter> B = {} \\<Longrightarrow>\n  (\\<Sum> x \\<in> A \\<union> B. f x) = (\\<Sum> x \\<in> A. f x) + (\\<Sum> x \\<in> B. f x)\"",
         "by (rule sum.union_disjoint)"),
        ("sum_swap_double",
         "\"(\\<Sum> i \\<in> A. \\<Sum> j \\<in> B. f i j) = (\\<Sum> j \\<in> B. \\<Sum> i \\<in> A. f i j)\"",
         "by (rule sum.swap)"),
        ("sum_distrib_left",
         "\"c * (\\<Sum> i \\<in> A. f i) = (\\<Sum> i \\<in> A. c * f i)\"",
         "by (rule sum_distrib_left)"),
        ("sum_distrib_right",
         "\"(\\<Sum> i \\<in> A. f i) * c = (\\<Sum> i \\<in> A. f i * c)\"",
         "by (rule sum_distrib_right)"),

        # --- List combinatorics patterns ---
        ("list_length_nonempty",
         "\"w \\<noteq> [] \\<Longrightarrow> 0 < length w\"",
         "by simp"),
        ("hd_in_set",
         "\"w \\<noteq> [] \\<Longrightarrow> hd w \\<in> set w\"",
         "by (simp add: hd_in_set)"),
        ("last_in_set",
         "\"w \\<noteq> [] \\<Longrightarrow> last w \\<in> set w\"",
         "by (simp add: last_in_set)"),
        ("finite_lists_bounded",
         "\"finite A \\<Longrightarrow> finite {w :: nat list . length w = k \\<and> set w \\<subseteq> A}\"",
         "by (rule finite_lists_length_eq) simp"),
        ("distinct_length_le",
         "\"distinct w \\<Longrightarrow> set w \\<subseteq> A \\<Longrightarrow> finite A \\<Longrightarrow>\n  length w \\<le> card A\"",
         "by (rule card_mono[THEN order_trans])\n   (auto simp: distinct_card)"),

        # --- Order / antisymmetry pattern ---
        ("antisym_eq",
         "\"a \\<le> b \\<Longrightarrow> b \\<le> a \\<Longrightarrow> a = b\" for a b :: \"'a :: order\"",
         "by (rule order_antisym)"),

        # --- Induction on nat patterns ---
        ("induction_nat_sum",
         "\"P 0 \\<Longrightarrow> (\\<And> k. P k \\<Longrightarrow> P (Suc k)) \\<Longrightarrow> P n\"",
         "by (rule Nat.nat.induct)"),

        # --- tropical_arith / tropm_arith usage patterns ---
        ("trop_fin_add_fin",
         "\"trop_add (Fin m) (Fin n) = Fin (max m n)\"",
         "by simp"),
        ("trop_mul_fin_fin",
         "\"trop_mul (Fin m) (Fin n) = Fin (m + n)\"",
         "by simp"),
        ("trop_add_neginf_left",
         "\"trop_add NegInf a = a\"",
         "by (cases a) simp_all"),
        ("trop_mul_neginf_left",
         "\"trop_mul NegInf a = NegInf\"",
         "by (cases a) simp_all"),
        ("tropm_add_posinf_left",
         "\"tropm_add PosInf a = a\"",
         "by (cases a) simp_all"),
    ]

    for (name, goal, proof) in raw
        push!(entries, IsabelleEntry(name, goal, proof, "isabelle_synthetic"))
    end

    return entries
end

# ---------------------------------------------------------------------------
# Main pipeline
# ---------------------------------------------------------------------------

function run()
    mkpath(OUTPUT_DIR)

    all_entries = IsabelleEntry[]

    # Phase 1: parse real .thy files
    println("[Isabelle] Phase 1: Parsing tropical-resource-typing theory files ...")
    for (fname, tag) in THY_FILES
        fpath = joinpath(TROPICAL_REPO, fname)
        parsed = parse_thy_file(fpath, tag)
        println("  $(fname): $(length(parsed)) entries extracted")
        append!(all_entries, parsed)
    end

    # Phase 2: supplement with high-quality synthetic entries
    println("[Isabelle] Phase 2: Adding synthetic algebra entries ...")
    synthetic = synthetic_isabelle_algebra()
    existing_names = Set(e.name for e in all_entries)
    added = 0
    for e in synthetic
        if e.name ∉ existing_names
            push!(all_entries, e)
            push!(existing_names, e.name)
            added += 1
        end
    end
    println("  Added $(added) synthetic entries")

    # Deduplicate by name (keep first occurrence)
    seen   = Set{String}()
    unique_entries = IsabelleEntry[]
    for e in all_entries
        e.name ∈ seen && continue
        push!(seen, e.name)
        push!(unique_entries, e)
    end

    println("[Isabelle] Total unique entries: $(length(unique_entries))")

    # Emit JSONL
    current_id = START_ID
    open(OUTPUT_FILE, "w") do fh
        for e in unique_entries
            record = Dict{String,Any}(
                "id"           => current_id,
                "prover"       => "Isabelle",
                "theorem"      => e.name,
                "goal"         => e.goal,
                "context"      => extract_tactics(e.proof),
                "tactic_proof" => first(e.proof, 800),
                "source"       => "tropical_resource_typing/$(e.source_file)",
            )
            println(fh, JSON3.write(record))
            current_id += 1
        end
    end
    println("[Isabelle] Written to $(OUTPUT_FILE)")

    # Stats
    stats = Dict{String,Any}(
        "prover"          => "Isabelle",
        "total_proofs"    => length(unique_entries),
        "from_thy_files"  => length(unique_entries) - added,
        "synthetic_added" => added,
        "id_range"        => [START_ID, current_id - 1],
        "output_file"     => OUTPUT_FILE,
    )
    open(STATS_FILE, "w") do fh
        JSON3.pretty(fh, stats)
    end

    println("[Isabelle] Stats written to $(STATS_FILE)")
    return length(unique_entries)
end

if abspath(PROGRAM_FILE) == abspath(@__FILE__)
    run()
end
