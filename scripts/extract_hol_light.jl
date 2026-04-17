#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
#
# Extract proofs from HOL Light corpus and convert to ECHIDNA training format.
#
# Attempts to download from the HOL Light GitHub repository (Examples/ and
# Multivariate/ directories). Falls back to generating high-quality synthetic
# proofs from known HOL Light theorems if the download is unavailable.
#
# HOL Light is a proof assistant for higher-order logic, known for its small
# trusted kernel and the Flyspeck project (formal proof of the Kepler conjecture).
#
# Output: training_data/proof_states_hol_light.jsonl
# ID range: 90000+

using JSON3

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

const REPO_ROOT = dirname(dirname(abspath(@__FILE__)))
const EXTERNAL_DIR = joinpath(REPO_ROOT, "external_corpora", "hol_light")
const OUTPUT_DIR = joinpath(REPO_ROOT, "training_data")
const OUTPUT_FILE = joinpath(OUTPUT_DIR, "proof_states_hol_light.jsonl")
const STATS_FILE = joinpath(OUTPUT_DIR, "stats_hol_light.json")
const START_ID = 90000

# HOL Light source repository
const HOL_LIGHT_RAW_BASE = "https://raw.githubusercontent.com/jrh13/hol-light/master"

# Key files to attempt downloading
const HOL_LIGHT_FILES = [
    "Examples/binary.ml",
    "Examples/combin.ml",
    "Examples/dickson.ml",
    "Examples/floor.ml",
    "Examples/hol88.ml",
    "Examples/forster.ml",
    "Examples/lagrange.ml",
    "Examples/miller_rabin.ml",
    "Examples/pell.ml",
    "Examples/prime.ml",
    "Examples/solovay.ml",
    "Examples/sylvester_gallai.ml",
    "Examples/wo.ml",
    "Multivariate/vectors.ml",
    "Multivariate/determinants.ml",
    "Multivariate/topology.ml",
    "Multivariate/convex.ml",
    "Multivariate/polytope.ml",
    "Multivariate/dimension.ml",
    "Multivariate/derivatives.ml",
    "Multivariate/integration.ml",
    "Multivariate/measure.ml",
    # Core HOL Light kernel and standard library — these are the
    # workhorses. Each carries hundreds of theorems, not tens.
    "arith.ml",
    "nums.ml",
    "int.ml",
    "lists.ml",
    "realarith.ml",
    "real.ml",
    "calc_num.ml",
    "calc_int.ml",
    "calc_rat.ml",
    "iterate.ml",
    "cart.ml",
    "sets.ml",
    "pair.ml",
    "wf.ml",
    "bool.ml",
    "equal.ml",
    "define.ml",
    "class.ml",
    "simp.ml",
    "ind_types.ml",
    "trivia.ml",
    # Library — real-analysis, combinatorics, number theory.
    "Library/analysis.ml",
    "Library/prime.ml",
    "Library/products.ml",
    "Library/sum.ml",
    "Library/permutations.ml",
    "Library/binomial.ml",
    "Library/floor.ml",
    "Library/card.ml",
    "Library/frag.ml",
    "Library/isum.ml",
    "Library/rstc.ml",
    "Library/wo.ml",
    "Library/pocklington.ml",
    "Library/primitive.ml",
    "Library/grouptheory.ml",
    "Library/ringtheory.ml",
    "Library/fieldtheory.ml",
    "Library/gcd.ml",
    "Library/multiplicative.ml",
    "Library/integer.ml",
    "Library/rewrite.ml",
    # Multivariate extensions beyond the initial set.
    "Multivariate/metric.ml",
    "Multivariate/paths.ml",
    "Multivariate/cross.ml",
    "Multivariate/flyspeck.ml",
    "Multivariate/clifford.ml",
    "Multivariate/transcendentals.ml",
    "Multivariate/realanalysis.ml",
    "Multivariate/complexes.ml",
    "Multivariate/canal.ml",
    "Multivariate/cauchy.ml",
    "Multivariate/complex_database.ml",
    "Multivariate/geom.ml",
    "Multivariate/gamma.ml",
    "Multivariate/moretop.ml",
    # 100 theorems project — one file per famous theorem, very
    # dense proof-per-line ratio.
    "100/arithmetic_geometric_mean.ml",
    "100/ballot.ml",
    "100/bernoulli.ml",
    "100/birthday.ml",
    "100/cantor.ml",
    "100/cayley_hamilton.ml",
    "100/ceva.ml",
    "100/chords.ml",
    "100/constructible.ml",
    "100/cosine.ml",
    "100/cubic.ml",
    "100/derangements.ml",
    "100/descartes.ml",
    "100/desargues.ml",
    "100/div3.ml",
    "100/divharmonic.ml",
    "100/e_is_transcendental.ml",
    "100/euler.ml",
    "100/fourier.ml",
    "100/friendship.ml",
    "100/fta.ml",
    "100/heron.ml",
    "100/inclusion_exclusion.ml",
    "100/independence.ml",
    "100/isosceles.ml",
    "100/konigsberg.ml",
    "100/lagrange.ml",
    "100/leibniz.ml",
    "100/liouville.ml",
    "100/minkowski.ml",
    "100/morley.ml",
    "100/pascal.ml",
    "100/perfect.ml",
    "100/pick.ml",
    "100/pnt.ml",
    "100/polyhedron.ml",
    "100/ptolemy.ml",
    "100/pythagoras.ml",
    "100/quartic.ml",
    "100/ratcountable.ml",
    "100/realsuncountable.ml",
    "100/reciprocity.ml",
    "100/sqrt.ml",
    "100/stirling.ml",
    "100/subsequence.ml",
    "100/thales.ml",
    "100/wilson.ml",
    "100/zolotarev.ml",
]

# ---------------------------------------------------------------------------
# Parser
# ---------------------------------------------------------------------------

"""
    parse_hol_light_file(filepath::String) -> Vector{Dict{String,Any}}

Parse a HOL Light .ml file and extract theorem definitions.

HOL Light theorems typically look like:
    let THEOREM_NAME = prove(
      `goal_term`,
      TACTIC_SEQUENCE);;
"""
function parse_hol_light_file(filepath::String)::Vector{Dict{String,Any}}
    results = Dict{String,Any}[]
    content = try
        read(filepath, String)
    catch
        return results
    end

    # Pattern A: `let THEOREM_NAME = prove(\`goal\`, tactic);;`
    # Pattern A2: `let THEOREM_NAME = prove_by_refinement(\`goal\`, [tactic1; tactic2; ...]);;`
    # Pattern B: `let THEOREM_NAME = new_theorem \`goal\`;;`
    # Pattern C: `let THEOREM_NAME = theorem \`goal\` (tactic);;`
    # HOL Light uses backtick-delimited terms. We capture all shapes.
    # Phase 1 widening (2026-04-17): accept both `prove` and
    # `prove_by_refinement`, walk full tactic text without a
    # 500-char truncation gate. See ECHIDNA-VERISIM-STRATEGY todo.
    prove_call_pat = r"let\s+(\w+)\s*=\s*(?:prove|prove_by_refinement)\s*\(\s*`([^`]+)`\s*,\s*(.*?)\)\s*;;"s
    for m in eachmatch(prove_call_pat, content)
        theorem_name = strip(m.captures[1])
        goal_text = replace(strip(m.captures[2]), r"\s+" => " ")
        tactic_text = replace(strip(m.captures[3]), r"\s+" => " ")

        # Extract tactic names (capitalized identifiers before arguments).
        # Previously capped at 20 to keep records compact; raise to 40 to
        # capture the longer refinement-style sequences without overruling
        # the tree-walk intent.
        tactic_names = [k.match for k in eachmatch(r"\b([A-Z][A-Z0-9_]+(?:_TAC)?)\b", tactic_text)]
        # Deduplicate while preserving order
        seen = Set{String}(); unique_t = String[]
        for t in tactic_names
            t ∉ seen && (push!(seen, t); push!(unique_t, t))
            length(unique_t) >= 40 && break
        end

        source_file = basename(filepath)
        push!(results, Dict{String,Any}(
            "theorem" => theorem_name,
            "goal" => goal_text,
            # Raised cap from 500 → 8000 chars so long refinement proofs
            # are preserved. Files larger than 8000 chars are truncated
            # only to protect downstream JSON serialisation budgets.
            "tactic_proof" => first(tactic_text, 8000),
            "tactics" => unique_t,
            "source" => "hol_light/$(source_file)",
        ))
    end

    # Pattern B: `let NAME = new_theorem \`stmt\`;;` and variants
    # (new_axiom, new_specification). These don't have tactics but
    # they do carry a named statement worth indexing.
    source_file = basename(filepath)
    for m in eachmatch(r"let\s+(\w+)\s*=\s*(new_theorem|new_axiom|new_specification)\s*(?:\[[^\]]*\]\s*)?`([^`]+)`\s*;;"s, content)
        theorem_name = strip(m.captures[1])
        construct = strip(m.captures[2])
        goal_text = replace(strip(m.captures[3]), r"\s+" => " ")
        push!(results, Dict{String,Any}(
            "theorem" => theorem_name,
            "goal" => goal_text,
            "tactic_proof" => "",
            "tactics" => [construct],
            "source" => "hol_light/$(source_file)",
        ))
    end

    return results
end

# ---------------------------------------------------------------------------
# Downloader
# ---------------------------------------------------------------------------

"""
    download_hol_light_files() -> Int

Attempt to download HOL Light example files from GitHub.
Returns the number of files successfully downloaded.
"""
function download_hol_light_files()::Int
    downloaded = 0
    for rel_path in HOL_LIGHT_FILES
        url = "$(HOL_LIGHT_RAW_BASE)/$(rel_path)"
        local_path = joinpath(EXTERNAL_DIR, replace(rel_path, "/" => "_"))
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
    generate_synthetic_hol_light() -> Vector{Dict{String,Any}}

Generate high-quality synthetic HOL Light proofs based on well-known
theorems and standard HOL Light tactic idioms.
"""
function generate_synthetic_hol_light()::Vector{Dict{String,Any}}
    # Categories of theorems with realistic HOL Light formulations
    arithmetic_theorems = [
        ("ADD_SYM", "!m n. m + n = n + m", "INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]"),
        ("ADD_ASSOC", "!m n p. m + (n + p) = (m + n) + p", "INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]"),
        ("ADD_0", "!n. 0 + n = n", "INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]"),
        ("MULT_SYM", "!m n. m * n = n * m", "INDUCT_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ARITH_TAC"),
        ("MULT_ASSOC", "!m n p. m * (n * p) = (m * n) * p", "INDUCT_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LEFT_ADD_DISTRIB]"),
        ("MULT_0", "!n. 0 * n = 0", "REWRITE_TAC[MULT_CLAUSES]"),
        ("LEFT_ADD_DISTRIB", "!m n p. m * (n + p) = m * n + m * p", "INDUCT_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; ADD_ASSOC]"),
        ("EXP_ADD", "!m n p. m EXP (n + p) = m EXP n * m EXP p", "INDUCT_TAC THEN ASM_REWRITE_TAC[EXP; ADD_CLAUSES; MULT_CLAUSES; MULT_ASSOC]"),
        ("ADD_SUC", "!m n. m + SUC n = SUC (m + n)", "REWRITE_TAC[ADD_CLAUSES]"),
        ("MULT_SUC", "!m n. m * SUC n = m + m * n", "REWRITE_TAC[MULT_CLAUSES]"),
        ("LE_REFL", "!n. n <= n", "REWRITE_TAC[LE_REFL]"),
        ("LE_TRANS", "!m n p. m <= n /\\ n <= p ==> m <= p", "ARITH_TAC"),
        ("LE_ANTISYM", "!m n. m <= n /\\ n <= m ==> m = n", "ARITH_TAC"),
        ("LT_ADD", "!m n. 0 < n ==> m < m + n", "ARITH_TAC"),
        ("EVEN_ADD", "!m n. EVEN(m + n) <=> (EVEN m <=> EVEN n)", "INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; EVEN]"),
        ("ODD_ADD", "!m n. ODD(m + n) <=> ~(ODD m <=> ODD n)", "REWRITE_TAC[GSYM NOT_EVEN; EVEN_ADD] THEN MESON_TAC[]"),
        ("DIVMOD_EXIST", "!m n. ~(n = 0) ==> ?q r. m = q * n + r /\\ r < n", "MESON_TAC[DIVISION]"),
        ("FACT_LT", "!n. 0 < FACT n", "INDUCT_TAC THEN ASM_REWRITE_TAC[FACT; LT_MULT] THEN ARITH_TAC"),
        ("FIB_ADD", "!m n. fib(m + n + 1) = fib(m + 1) * fib(n + 1) + fib(m) * fib(n)", "INDUCT_TAC THEN ASM_REWRITE_TAC[FIB; ADD_CLAUSES; MULT_CLAUSES]"),
        ("PRIME_2", "prime 2", "REWRITE_TAC[prime] THEN ARITH_TAC"),
    ]

    logic_theorems = [
        ("AND_SYM", "!p q. p /\\ q <=> q /\\ p", "MESON_TAC[]"),
        ("OR_SYM", "!p q. p \\/ q <=> q \\/ p", "MESON_TAC[]"),
        ("IMP_TRANS", "!p q r. (p ==> q) /\\ (q ==> r) ==> (p ==> r)", "MESON_TAC[]"),
        ("CONTRAPOSITIVE", "!p q. (p ==> q) <=> (~q ==> ~p)", "MESON_TAC[]"),
        ("DE_MORGAN_AND", "!p q. ~(p /\\ q) <=> ~p \\/ ~q", "MESON_TAC[]"),
        ("DE_MORGAN_OR", "!p q. ~(p \\/ q) <=> ~p /\\ ~q", "MESON_TAC[]"),
        ("DOUBLE_NEG", "!p. ~~p <=> p", "MESON_TAC[]"),
        ("EXCLUDED_MIDDLE", "!p. p \\/ ~p", "MESON_TAC[]"),
        ("AND_ASSOC", "!p q r. p /\\ (q /\\ r) <=> (p /\\ q) /\\ r", "MESON_TAC[]"),
        ("OR_ASSOC", "!p q r. p \\/ (q \\/ r) <=> (p \\/ q) \\/ r", "MESON_TAC[]"),
        ("IMP_IMP", "!p q r. (p ==> q ==> r) <=> (p /\\ q ==> r)", "MESON_TAC[]"),
        ("FORALL_AND", "!P Q. (!x. P x /\\ Q x) <=> (!x. P x) /\\ (!x. Q x)", "MESON_TAC[]"),
        ("EXISTS_OR", "!P Q. (?x. P x \\/ Q x) <=> (?x. P x) \\/ (?x. Q x)", "MESON_TAC[]"),
        ("NOT_FORALL", "!P. ~(!x. P x) <=> (?x. ~P x)", "MESON_TAC[]"),
        ("NOT_EXISTS", "!P. ~(?x. P x) <=> (!x. ~P x)", "MESON_TAC[]"),
    ]

    set_theorems = [
        ("SUBSET_REFL", "!s:A->bool. s SUBSET s", "SET_TAC[]"),
        ("SUBSET_TRANS", "!s t u:A->bool. s SUBSET t /\\ t SUBSET u ==> s SUBSET u", "SET_TAC[]"),
        ("INTER_COMM", "!s t:A->bool. s INTER t = t INTER s", "SET_TAC[]"),
        ("UNION_COMM", "!s t:A->bool. s UNION t = t UNION s", "SET_TAC[]"),
        ("INTER_ASSOC", "!s t u:A->bool. s INTER (t INTER u) = (s INTER t) INTER u", "SET_TAC[]"),
        ("UNION_ASSOC", "!s t u:A->bool. s UNION (t UNION u) = (s UNION t) UNION u", "SET_TAC[]"),
        ("INTER_SUBSET", "!s t:A->bool. (s INTER t) SUBSET s", "SET_TAC[]"),
        ("SUBSET_UNION", "!s t:A->bool. s SUBSET (s UNION t)", "SET_TAC[]"),
        ("EMPTY_SUBSET", "!s:A->bool. EMPTY SUBSET s", "SET_TAC[]"),
        ("SUBSET_EMPTY", "!s:A->bool. s SUBSET EMPTY <=> s = EMPTY", "SET_TAC[]"),
        ("UNION_EMPTY", "!s:A->bool. s UNION EMPTY = s", "SET_TAC[]"),
        ("INTER_UNIV", "!s:A->bool. s INTER UNIV = s", "SET_TAC[]"),
        ("DE_MORGAN_INTER", "!s t:A->bool. UNIV DIFF (s INTER t) = (UNIV DIFF s) UNION (UNIV DIFF t)", "SET_TAC[]"),
        ("ABSORPTION_UNION", "!s t:A->bool. s SUBSET t ==> s UNION t = t", "SET_TAC[]"),
        ("DISJOINT_SYM", "!s t:A->bool. DISJOINT s t <=> DISJOINT t s", "SET_TAC[DISJOINT]"),
    ]

    list_theorems = [
        ("APPEND_NIL", "!l:(A)list. APPEND l [] = l", "LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND]"),
        ("APPEND_ASSOC", "!l1 l2 l3:(A)list. APPEND l1 (APPEND l2 l3) = APPEND (APPEND l1 l2) l3", "LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND]"),
        ("LENGTH_APPEND", "!l1 l2:(A)list. LENGTH(APPEND l1 l2) = LENGTH l1 + LENGTH l2", "LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH; APPEND; ADD_CLAUSES]"),
        ("REVERSE_REVERSE", "!l:(A)list. REVERSE(REVERSE l) = l", "LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[REVERSE; REVERSE_APPEND]"),
        ("MAP_APPEND", "!f l1 l2:(A)list. MAP f (APPEND l1 l2) = APPEND (MAP f l1) (MAP f l2)", "LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; APPEND]"),
        ("LENGTH_MAP", "!f l:(A)list. LENGTH(MAP f l) = LENGTH l", "LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; LENGTH]"),
        ("MAP_ID", "!l:(A)list. MAP (\\x. x) l = l", "LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP]"),
        ("FILTER_APPEND", "!P l1 l2:(A)list. FILTER P (APPEND l1 l2) = APPEND (FILTER P l1) (FILTER P l2)", "LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER; APPEND] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[APPEND]"),
        ("MEM_APPEND", "!x l1 l2:(A)list. MEM x (APPEND l1 l2) <=> MEM x l1 \\/ MEM x l2", "LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MEM; APPEND] THEN MESON_TAC[]"),
        ("ALL_APPEND", "!P l1 l2:(A)list. ALL P (APPEND l1 l2) <=> ALL P l1 /\\ ALL P l2", "LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; APPEND] THEN MESON_TAC[]"),
    ]

    real_analysis = [
        ("REAL_ADD_SYM", "!x y. x + y = y + x", "REAL_ARITH_TAC"),
        ("REAL_ADD_ASSOC", "!x y z. x + (y + z) = (x + y) + z", "REAL_ARITH_TAC"),
        ("REAL_MUL_SYM", "!x y. x * y = y * x", "REAL_ARITH_TAC"),
        ("REAL_LE_TOTAL", "!x y. x <= y \\/ y <= x", "REAL_ARITH_TAC"),
        ("ABS_TRIANGLE", "!x y. abs(x + y) <= abs(x) + abs(y)", "REAL_ARITH_TAC"),
        ("ABS_POS", "!x. &0 <= abs(x)", "REAL_ARITH_TAC"),
        ("ABS_ZERO", "!x. abs(x) = &0 <=> x = &0", "REAL_ARITH_TAC"),
        ("REAL_POW_ADD", "!x m n. x pow (m + n) = x pow m * x pow n", "INDUCT_TAC THEN ASM_REWRITE_TAC[real_pow; ADD_CLAUSES; REAL_MUL_LID; REAL_MUL_ASSOC]"),
        ("SQRT_POW_2", "!x. &0 <= x ==> sqrt(x) pow 2 = x", "MESON_TAC[SQRT_POW2]"),
        ("REAL_COMPLETE", "!P. (?x. P x) /\\ (?M. !x. P x ==> x <= M) ==> ?s. (!x. P x ==> x <= s) /\\ !M. (!x. P x ==> x <= M) ==> s <= M", "REWRITE_TAC[REAL_COMPLETE]"),
        ("LIM_CONST", "!net c. (\\x. c) --> c", "REWRITE_TAC[LIM; dist; REAL_SUB_REFL; ABS_0]"),
        ("LIM_ADD", "!net f g l m. f --> l /\\ g --> m ==> (\\x. f x + g x) --> l + m", "REWRITE_TAC[LIM] THEN MESON_TAC[ABS_TRIANGLE; REAL_ARITH]"),
        ("CONTINUOUS_ADD", "!f g x. f continuous_at x /\\ g continuous_at x ==> (\\y. f y + g y) continuous_at x", "REWRITE_TAC[continuous_at] THEN MESON_TAC[LIM_ADD]"),
        ("IVT", "!f a b. f continuous_on real_interval[a,b] /\\ f(a) <= &0 /\\ &0 <= f(b) ==> ?c. a <= c /\\ c <= b /\\ f(c) = &0", "MATCH_MP_TAC IVT_INCREASING THEN ASM_REWRITE_TAC[]"),
        ("MVT", "!f f' a b. (!x. a <= x /\\ x <= b ==> (f has_real_derivative f' x) (atreal x within real_interval[a,b])) /\\ a < b ==> ?c. a < c /\\ c < b /\\ f(b) - f(a) = f'(c) * (b - a)", "MATCH_MP_TAC REAL_MVT_VERY_SIMPLE THEN ASM_REWRITE_TAC[]"),
    ]

    topology_theorems = [
        ("OPEN_EMPTY", "open({}:real^N->bool)", "REWRITE_TAC[OPEN_EMPTY]"),
        ("OPEN_UNIV", "open((:real^N))", "REWRITE_TAC[OPEN_UNIV]"),
        ("OPEN_INTER", "!s t:real^N->bool. open s /\\ open t ==> open(s INTER t)", "MESON_TAC[OPEN_INTER]"),
        ("OPEN_UNION", "!s t:real^N->bool. open s /\\ open t ==> open(s UNION t)", "MESON_TAC[OPEN_UNION]"),
        ("CLOSED_EMPTY", "closed({}:real^N->bool)", "REWRITE_TAC[CLOSED_EMPTY]"),
        ("CLOSED_UNIV", "closed((:real^N))", "REWRITE_TAC[CLOSED_UNIV]"),
        ("CLOSED_INTER", "!s t:real^N->bool. closed s /\\ closed t ==> closed(s INTER t)", "MESON_TAC[CLOSED_INTER]"),
        ("COMPACT_IMP_CLOSED", "!s:real^N->bool. compact s ==> closed s", "MESON_TAC[COMPACT_IMP_CLOSED]"),
        ("COMPACT_IMP_BOUNDED", "!s:real^N->bool. compact s ==> bounded s", "MESON_TAC[COMPACT_IMP_BOUNDED]"),
        ("HEINE_BOREL", "!s:real^N->bool. compact s <=> closed s /\\ bounded s", "REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED]"),
        ("CONNECTED_INTERVAL", "!a b:real^N. connected(interval[a,b])", "REWRITE_TAC[CONVEX_CONNECTED; CONVEX_INTERVAL]"),
        ("BROUWER_FIXED_POINT", "!f s:real^N->bool. compact s /\\ convex s /\\ ~(s = {}) /\\ f continuous_on s /\\ IMAGE f s SUBSET s ==> ?x. x IN s /\\ f x = x", "MATCH_MP_TAC BROUWER_FIXED_POINT THEN ASM_REWRITE_TAC[]"),
    ]

    # Combine all theorem categories
    all_categories = [
        ("arithmetic", arithmetic_theorems),
        ("logic", logic_theorems),
        ("sets", set_theorems),
        ("lists", list_theorems),
        ("real_analysis", real_analysis),
        ("topology", topology_theorems),
    ]

    proofs = Dict{String,Any}[]
    for (category, theorems) in all_categories
        for (name, goal, tactic) in theorems
            # Extract tactic names from the tactic string
            tactic_names = [k.match for k in eachmatch(r"\b([A-Z][A-Z_]+(?:_TAC)?)\b", tactic)]
            seen = Set{String}(); unique_t = String[]
            for t in tactic_names
                t ∉ seen && (push!(seen, t); push!(unique_t, t))
            end

            push!(proofs, Dict{String,Any}(
                "theorem" => name,
                "goal" => goal,
                "tactic_proof" => tactic,
                "tactics" => unique_t,
                "source" => "hol_light_synthetic/$(category)",
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

    # Phase 1: try downloading real HOL Light files
    println("[HOL Light] Phase 1: Attempting to download from GitHub ...")
    downloaded = download_hol_light_files()
    println("  Downloaded/cached $(downloaded) files")

    # Parse whatever we got
    for fname in readdir(EXTERNAL_DIR)
        if endswith(fname, ".ml")
            fpath = joinpath(EXTERNAL_DIR, fname)
            parsed = parse_hol_light_file(fpath)
            append!(all_entries, parsed)
            if !isempty(parsed)
                println("  Parsed $(length(parsed)) theorems from $(fname)")
            end
        end
    end
    extracted_count = length(all_entries)

    # Phase 2: always add synthetic data (supplements real data)
    println("[HOL Light] Phase 2: Generating synthetic proofs ...")
    synthetic = generate_synthetic_hol_light()
    # Avoid duplicates by theorem name
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

    # Assign IDs and normalise schema
    current_id = START_ID
    output_records = Dict{String,Any}[]
    for entry in all_entries
        record = Dict{String,Any}(
            "id" => current_id,
            "prover" => "HOLLight",
            "theorem" => entry["theorem"],
            "goal" => entry["goal"],
            "context" => get(entry, "tactics", String[]),
            "tactic_proof" => get(entry, "tactic_proof", ""),
            "source" => get(entry, "source", "hol_light"),
        )
        push!(output_records, record)
        current_id += 1
    end

    # Write output
    open(OUTPUT_FILE, "w") do fh
        for rec in output_records
            println(fh, JSON3.write(rec))
        end
    end

    # Write stats
    stats = Dict{String,Any}(
        "prover" => "HOLLight",
        "total_proofs" => length(output_records),
        "extracted_from_source" => extracted_count,
        "synthetic_added" => length(output_records) - extracted_count,
        "id_range" => [START_ID, current_id - 1],
        "output_file" => OUTPUT_FILE,
    )
    open(STATS_FILE, "w") do fh
        JSON3.pretty(fh, stats)
    end

    println("\n[HOL Light] COMPLETE: $(length(output_records)) proofs written to $(OUTPUT_FILE)")
    println("  Extracted from source: $(extracted_count)")
    println("  Synthetic: $(length(output_records) - extracted_count)")
    return (extracted_count, length(output_records) - extracted_count)
end

if abspath(PROGRAM_FILE) == abspath(@__FILE__)
    run()
end
