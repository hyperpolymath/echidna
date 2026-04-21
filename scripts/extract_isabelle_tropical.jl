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

using JSON3, Dates

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

const REPO_ROOT       = dirname(dirname(abspath(@__FILE__)))
const OUTPUT_DIR      = joinpath(REPO_ROOT, "training_data")
const OUTPUT_FILE     = joinpath(OUTPUT_DIR, "proof_states_isabelle.jsonl")
const PREMISES_FILE   = joinpath(OUTPUT_DIR, "premises_isabelle_tropical.jsonl")
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

        # --- set_theory (~10) ---
        ("set_union_comm",
         "\"A \\<union> B = B \\<union> A\"",
         "by (rule Un_commute)"),
        ("set_inter_comm",
         "\"A \\<inter> B = B \\<inter> A\"",
         "by (rule Int_commute)"),
        ("set_diff_subset",
         "\"A - B \\<subseteq> A\"",
         "by blast"),
        ("set_image_union",
         "\"f ` (A \\<union> B) = f ` A \\<union> f ` B\"",
         "by (rule image_Un)"),
        ("set_comprehension",
         "\"{x \\<in> A. P x \\<and> Q x} = {x \\<in> A. P x} \\<inter> {x \\<in> A. Q x}\"",
         "by auto"),
        ("set_finite_union",
         "\"finite A \\<Longrightarrow> finite B \\<Longrightarrow> finite (A \\<union> B)\"",
         "by simp"),
        ("set_powerset",
         "\"A \\<in> Pow B \\<Longrightarrow> A \\<subseteq> B\"",
         "by (simp add: Pow_iff)"),
        ("set_disjoint_union",
         "\"A \\<inter> B = {} \\<Longrightarrow> card (A \\<union> B) = card A + card B\"",
         "by (simp add: card_Un_disjoint)"),
        ("set_insert_member",
         "\"x \\<in> insert x A\"",
         "by simp"),
        ("set_collect_mem",
         "\"a \\<in> {x. P x} \\<Longrightarrow> P a\"",
         "by simp"),

        # --- real_analysis (~10) ---
        ("abs_nonneg",
         "\"(0 :: real) \\<le> \\<bar>x\\<bar>\"",
         "by simp"),
        ("abs_triangle",
         "\"\\<bar>(x :: real) + y\\<bar> \\<le> \\<bar>x\\<bar> + \\<bar>y\\<bar>\"",
         "by (rule abs_triangle_ineq)"),
        ("cauchy_schwarz",
         "\"(\\<Sum>i<n. (a i) * (b i))^2 \\<le> (\\<Sum>i<n. (a i)^2) * (\\<Sum>i<n. (b i)^2)\"",
         "by (rule sum_cauchy_schwarz_ineq)"),
        ("sqrt_positive",
         "\"(0 :: real) \\<le> x \\<Longrightarrow> 0 \\<le> sqrt x\"",
         "by simp"),
        ("exp_add",
         "\"exp ((x :: real) + y) = exp x * exp y\"",
         "by (rule exp_add)"),
        ("log_mult",
         "\"0 < x \\<Longrightarrow> 0 < y \\<Longrightarrow> ln (x * y) = ln x + ln (y :: real)\"",
         "by (rule ln_mult)"),
        ("cos_sin_sq",
         "\"(cos x)^2 + (sin x)^2 = (1 :: real)\"",
         "by (rule sin_cos_squared_add [symmetric])"),
        ("limit_sum",
         "\"(f \\<longlongrightarrow> a) F \\<Longrightarrow> (g \\<longlongrightarrow> b) F \\<Longrightarrow>\n  ((\\<lambda>x. f x + g x) \\<longlongrightarrow> a + b) F\"",
         "by (rule tendsto_add)"),
        ("continuous_compose",
         "\"continuous_on A g \\<Longrightarrow> continuous_on B f \\<Longrightarrow> g ` A \\<subseteq> B \\<Longrightarrow>\n  continuous_on A (f \\<circ> g)\"",
         "by (rule continuous_on_compose) auto"),
        ("deriv_chain",
         "\"(f has_real_derivative f') (at x) \\<Longrightarrow>\n  (g has_real_derivative g') (at (f x)) \\<Longrightarrow>\n  ((g \\<circ> f) has_real_derivative g' * f') (at x)\"",
         "by (rule DERIV_chain2)"),

        # --- algebra (~10) ---
        ("group_inverse_unique",
         "\"(a :: 'a :: group_add) + b = 0 \\<Longrightarrow> b = - a\"",
         "by (metis add.left_cancel add.right_inverse)"),
        ("ring_zero_mul",
         "\"(0 :: 'a :: ring) * a = 0\"",
         "by simp"),
        ("field_inv_mul",
         "\"(a :: 'a :: field) \\<noteq> 0 \\<Longrightarrow> inverse a * a = 1\"",
         "by simp"),
        ("monoid_assoc",
         "\"(a :: 'a :: monoid_mult) * b * c = a * (b * c)\"",
         "by (rule mult.assoc)"),
        ("hom_compose",
         "\"group_hom f \\<Longrightarrow> group_hom g \\<Longrightarrow> group_hom (f \\<circ> g)\"",
         "by (auto simp: group_hom_def)"),
        ("kernel_normal",
         "\"group_hom f \\<Longrightarrow> normal (kernel f)\"",
         "by (rule group_hom.kernel_normal)"),
        ("quotient_group",
         "\"normal H \\<Longrightarrow> group (G Mod H)\"",
         "by (rule normal.quotient_group)"),
        ("ideal_sum",
         "\"ideal I \\<Longrightarrow> ideal J \\<Longrightarrow> ideal (I + J)\"",
         "by (rule ideal_sum)"),
        ("polynomial_degree",
         "\"degree (p * q) \\<le> degree p + degree (q :: 'a :: idom poly)\"",
         "by (rule degree_mult_le)"),
        ("vector_space_basis",
         "\"finite B \\<Longrightarrow> independent B \\<Longrightarrow> span B = UNIV \\<Longrightarrow>\n  card B = dim (UNIV :: 'a :: euclidean_space set)\"",
         "by (metis dim_eq_card_independent span_UNIV)"),

        # --- logic (~10) ---
        ("imp_trans",
         "\"(P \\<longrightarrow> Q) \\<Longrightarrow> (Q \\<longrightarrow> R) \\<Longrightarrow> (P \\<longrightarrow> R)\"",
         "by blast"),
        ("contrapositive",
         "\"(P \\<longrightarrow> Q) \\<Longrightarrow> (\\<not> Q \\<longrightarrow> \\<not> P)\"",
         "by blast"),
        ("double_neg",
         "\"\\<not> \\<not> P \\<Longrightarrow> P\"",
         "by blast"),
        ("excluded_middle",
         "\"P \\<or> \\<not> P\"",
         "by blast"),
        ("de_morgan",
         "\"\\<not> (P \\<and> Q) \\<longleftrightarrow> (\\<not> P \\<or> \\<not> Q)\"",
         "by blast"),
        ("forall_conj_distrib",
         "\"(\\<forall>x. P x \\<and> Q x) \\<longleftrightarrow> (\\<forall>x. P x) \\<and> (\\<forall>x. Q x)\"",
         "by blast"),
        ("exists_or_distrib",
         "\"(\\<exists>x. P x \\<or> Q x) \\<longleftrightarrow> (\\<exists>x. P x) \\<or> (\\<exists>x. Q x)\"",
         "by blast"),
        ("proof_by_cases",
         "\"(P \\<Longrightarrow> R) \\<Longrightarrow> (\\<not> P \\<Longrightarrow> R) \\<Longrightarrow> R\"",
         "by blast"),
        ("classical_reductio",
         "\"(\\<not> P \\<Longrightarrow> False) \\<Longrightarrow> P\"",
         "by blast"),
        ("iff_sym",
         "\"(P \\<longleftrightarrow> Q) \\<Longrightarrow> (Q \\<longleftrightarrow> P)\"",
         "by blast"),

        # --- list_advanced (~10) ---
        ("list_induct",
         "\"P [] \\<Longrightarrow> (\\<And>x xs. P xs \\<Longrightarrow> P (x # xs)) \\<Longrightarrow> P ys\"",
         "by (induction ys) auto"),
        ("map_append",
         "\"map f (xs @ ys) = map f xs @ map f ys\"",
         "by simp"),
        ("filter_append",
         "\"filter P (xs @ ys) = filter P xs @ filter P ys\"",
         "by simp"),
        ("concat_map",
         "\"concat (map f xs) = concatMap f xs\"",
         "by (induction xs) simp_all"),
        ("zip_map",
         "\"map fst (zip xs ys) = take (min (length xs) (length ys)) xs\"",
         "by (induction xs ys rule: list_induct2') auto"),
        ("nth_map",
         "\"i < length xs \\<Longrightarrow> (map f xs) ! i = f (xs ! i)\"",
         "by simp"),
        ("take_append",
         "\"take n xs @ drop n xs = xs\"",
         "by simp"),
        ("drop_append",
         "\"n \\<le> length xs \\<Longrightarrow> drop n (xs @ ys) = drop n xs @ ys\"",
         "by simp"),
        ("sorted_insert",
         "\"sorted xs \\<Longrightarrow> sorted (insort x xs)\"",
         "by (simp add: sorted_insort)"),
        ("distinct_append",
         "\"distinct (xs @ ys) \\<longleftrightarrow>\n  distinct xs \\<and> distinct ys \\<and> set xs \\<inter> set ys = {}\"",
         "by (rule distinct_append)"),

        # --- matrix (~10) ---
        ("matrix_add_comm",
         "\"(A :: 'a :: ab_semigroup_add mat) + B = B + A\"",
         "by (simp add: mat_add_comm)"),
        ("matrix_mul_assoc",
         "\"dim_col A = dim_row B \\<Longrightarrow> dim_col B = dim_row C \\<Longrightarrow>\n  (A :: 'a :: semiring_0 mat) * B * C = A * (B * C)\"",
         "by (rule assoc_mult_mat)"),
        ("matrix_transpose_transpose",
         "\"(A\\<^sup>T)\\<^sup>T = A\"",
         "by (rule transpose_transpose)"),
        ("matrix_zero_left",
         "\"dim_row A = n \\<Longrightarrow> dim_col A = m \\<Longrightarrow>\n  (0\\<^sub>m n k :: 'a :: semiring_0 mat) * A = 0\\<^sub>m n m\"",
         "by (rule left_mult_zero_mat)"),
        ("matrix_one_right",
         "\"dim_row A = n \\<Longrightarrow> dim_col A = n \\<Longrightarrow>\n  (A :: 'a :: semiring_1 mat) * 1\\<^sub>m n = A\"",
         "by (rule right_mult_one_mat)"),
        ("matrix_det_transpose",
         "\"det (A\\<^sup>T) = det (A :: 'a :: comm_ring_1 mat)\"",
         "by (rule det_transpose)"),
        ("matrix_trace_add",
         "\"dim_row A = n \\<Longrightarrow> dim_row B = n \\<Longrightarrow>\n  trace (A + B) = trace A + trace (B :: 'a :: comm_monoid_add mat)\"",
         "by (simp add: trace_add)"),
        ("matrix_scalar_mult",
         "\"dim_row A = n \\<Longrightarrow> dim_col A = m \\<Longrightarrow>\n  c \\<cdot>\\<^sub>m (d \\<cdot>\\<^sub>m A) = (c * d) \\<cdot>\\<^sub>m (A :: 'a :: semiring_0 mat)\"",
         "by (rule smult_smult_assoc)"),
        ("matrix_row_col",
         "\"i < dim_row A \\<Longrightarrow> j < dim_col A \\<Longrightarrow>\n  (A :: 'a mat) $$ (i, j) = row A i $ j\"",
         "by (simp add: row_def)"),
        ("matrix_dim_mult",
         "\"dim_row (A * B) = dim_row A\"",
         "by simp"),

        # --- datatype_induction (~10) ---
        ("tree_height_nonneg",
         "\"0 \\<le> height (t :: 'a tree)\"",
         "by (induction t) auto"),
        ("tree_size_mirror",
         "\"size (mirror t) = size (t :: 'a tree)\"",
         "by (induction t) auto"),
        ("bst_insert_ordered",
         "\"bst t \\<Longrightarrow> bst (insert x t)\"",
         "by (induction t) auto"),
        ("list_rev_rev",
         "\"rev (rev xs) = xs\"",
         "by simp"),
        ("even_odd_mutual",
         "\"even n \\<Longrightarrow> odd (Suc n)\"",
         "by simp"),
        ("rose_tree_fold",
         "\"fold_rose f (Node x ts) = f x (map (fold_rose f) ts)\"",
         "by simp"),
        ("option_map_compose",
         "\"map_option f (map_option g x) = map_option (f \\<circ> g) x\"",
         "by (cases x) simp_all"),
        ("sum_type_comm",
         "\"(case s of Inl a \\<Rightarrow> Inr a | Inr b \\<Rightarrow> Inl b) = swap_sum s\"",
         "by (cases s) simp_all"),
        ("prod_type_assoc",
         "\"(fst (fst p), snd (fst p), snd p) = prod_assoc p\"",
         "by (cases p) auto"),
        ("nested_induction",
         "\"P Leaf \\<Longrightarrow> (\\<And>l x r. P l \\<Longrightarrow> P r \\<Longrightarrow> P (Node l x r)) \\<Longrightarrow> P t\"",
         "by (induction t) auto"),

        # --- automation_patterns (~10) ---
        ("auto_solve",
         "\"A \\<subseteq> B \\<Longrightarrow> B \\<subseteq> C \\<Longrightarrow> A \\<subseteq> C\"",
         "by auto"),
        ("simp_only",
         "\"length (xs @ ys) = length xs + length ys\"",
         "by (simp only: length_append)"),
        ("blast_intro",
         "\"\\<lbrakk> \\<forall>x. P x \\<longrightarrow> Q x; P a \\<rbrakk> \\<Longrightarrow> Q a\"",
         "by blast"),
        ("force_cases",
         "\"(x :: nat) = 0 \\<or> (\\<exists>n. x = Suc n)\"",
         "by (cases x) force+"),
        ("fastforce_dest",
         "\"\\<lbrakk> x \\<in> A \\<inter> B; A \\<subseteq> C \\<rbrakk> \\<Longrightarrow> x \\<in> C\"",
         "by fastforce"),
        ("metis_resolve",
         "\"(P \\<longrightarrow> Q) \\<Longrightarrow> P \\<Longrightarrow> Q\"",
         "by (metis mp)"),
        ("smt_arith",
         "\"(x :: int) + y > 0 \\<Longrightarrow> x > 0 \\<or> y > 0\"",
         "by (smt (verit) add_pos_pos)"),
        ("sledgehammer_pattern",
         "\"(a :: 'a :: group_add) + (- a) = 0\"",
         "by (metis add.right_inverse)"),
        ("try_method",
         "\"finite A \\<Longrightarrow> card (insert x A) \\<le> Suc (card A)\"",
         "by (simp add: card_insert_le)"),
        ("method_combinator",
         "\"(x :: nat) \\<le> y \\<Longrightarrow> y \\<le> z \\<Longrightarrow> x \\<le> z\"",
         "by (rule order.trans)"),
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
    premises_records = Dict{String,Any}[]
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
            # Emit premises: Isabelle identifiers from goal
            for hm in eachmatch(r"\b([A-Za-z][A-Za-z0-9_']{1,40})\b", e.goal)
                h = strip(hm.captures[1])
                !isempty(h) && length(h) < 50 && push!(premises_records, Dict{String,Any}(
                    "proof_id"=>current_id, "premise"=>h,
                    "prover"=>"Isabelle", "theorem"=>e.name, "source"=>"isabelle_tropical"))
            end
            current_id += 1
        end
    end
    open(PREMISES_FILE, "w") do fh
        for p in premises_records; println(fh, JSON3.write(p)); end
    end
    println("[Isabelle] Written to $(OUTPUT_FILE)")

    # Stats
    stats = Dict{String,Any}(
        "prover"          => "Isabelle",
        "total_proofs"    => length(unique_entries),
        "premises_count"  => length(premises_records),
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
