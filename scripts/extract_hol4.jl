#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
#
# Extract proofs from HOL4 corpus and convert to ECHIDNA training format.
#
# Attempts to download HOL4 example files from GitHub. Falls back to generating
# high-quality synthetic HOL4 proofs from standard theories (arithmetic, lists,
# sets, booleans, strings, CakeML-style verification).
#
# HOL4 is an interactive proof assistant in the HOL family, used extensively in
# the CakeML project (verified ML compiler) and seL4 (verified OS kernel).
#
# Output: training_data/proof_states_hol4.jsonl
# ID range: 91000+

using JSON3

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

const REPO_ROOT = dirname(dirname(abspath(@__FILE__)))
const EXTERNAL_DIR = joinpath(REPO_ROOT, "external_corpora", "hol4")
const OUTPUT_DIR = joinpath(REPO_ROOT, "training_data")
const OUTPUT_FILE = joinpath(OUTPUT_DIR, "proof_states_hol4.jsonl")
const STATS_FILE = joinpath(OUTPUT_DIR, "stats_hol4.json")
const START_ID = 91000

const HOL4_RAW_BASE = "https://raw.githubusercontent.com/HOL-Theorem-Prover/HOL/develop"
const HOL4_FILES = [
    # Original ten — kept for continuity.
    "examples/algebra/groupScript.sml",
    "examples/algebra/ringScript.sml",
    "examples/algorithms/sortingScript.sml",
    "examples/set-theory/zfcScript.sml",
    "src/num/theories/arithmeticScript.sml",
    "src/list/src/listScript.sml",
    "src/boss/boolScript.sml",
    "src/string/stringScript.sml",
    "src/pred_set/src/pred_setScript.sml",
    "src/real/realScript.sml",
    # Core theories — dense with named theorems.
    "src/num/theories/whileScript.sml",
    "src/num/theories/prim_recScript.sml",
    "src/num/theories/numeralScript.sml",
    "src/num/extra_theories/numpairScript.sml",
    "src/num/extra_theories/divScript.sml",
    "src/num/extra_theories/gcdScript.sml",
    "src/integer/integerScript.sml",
    "src/integer/int_arithScript.sml",
    "src/real/realaxScript.sml",
    "src/real/realSimpsScript.sml",
    "src/rational/ratScript.sml",
    "src/relation/relationScript.sml",
    "src/path/pathScript.sml",
    "src/res_quan/src/res_quanScript.sml",
    "src/list/src/rich_listScript.sml",
    "src/list/src/sortingScript.sml",
    "src/list/src/indexedListsScript.sml",
    "src/string/asciiScript.sml",
    "src/pred_set/src/pred_setpp.sml",
    "src/finite_map/finite_mapScript.sml",
    "src/sort/sortingScript.sml",
    "src/quotient/src/quotientScript.sml",
    "src/bag/bagScript.sml",
    # Algebra examples — long, many theorems.
    "examples/algebra/lib/groupIsoScript.sml",
    "examples/algebra/lib/groupMapScript.sml",
    "examples/algebra/lib/monoidScript.sml",
    "examples/algebra/lib/fieldScript.sml",
    "examples/algebra/lib/polyScript.sml",
    "examples/algebra/lib/polyFieldScript.sml",
    "examples/algebra/lib/polyRingScript.sml",
    "examples/algebra/finite_group/finiteGroupScript.sml",
    "examples/algebra/finite_group/subGroupScript.sml",
    # Number theory, graph theory, combinatorics.
    "examples/numberTheory/primeScript.sml",
    "examples/numberTheory/divisibilityScript.sml",
    "examples/graph/dag_graphScript.sml",
    # CakeML-adjacent verification.
    "examples/ARM/v7/arm_coretypesScript.sml",
    "examples/bootstrap/cakemlScript.sml",
    # Probability, measure, logic.
    "examples/probability/probabilityScript.sml",
    "examples/probability/sigma_algebraScript.sml",
    "examples/probability/lebesgueScript.sml",
    "examples/logic/modal-logic/modalLogicScript.sml",
    "examples/logic/temporal-deep/TemporalScript.sml",
    # seL4 / verified-systems style.
    "examples/separation-logic/stack/stackScript.sml",
    "examples/separation-logic/hoare-triple/hoare_logicScript.sml",
]

# ---------------------------------------------------------------------------
# Parser
# ---------------------------------------------------------------------------

"""
    parse_hol4_file(filepath::String) -> Vector{Dict{String,Any}}

Parse a HOL4 *Script.sml file and extract theorem definitions.

HOL4 theorems typically look like:
    val THEOREM_NAME = store_thm("THEOREM_NAME",
      ``goal_term``,
      tactic_sequence);

Or the newer style:
    Theorem THEOREM_NAME:
      goal_term
    Proof
      tactic_sequence
    QED
"""
# Phase 1 widening (2026-04-17): HOL4 extractor previously used a
# narrow tactic-keyword gate (`\w+_TAC|Induct_on|rw|fs|simp|metis_tac|
# decide_tac|PROVE_TAC`). That gate dropped every tactic-name NOT on
# the list — qsuff_tac, spose_not_then, drule_then, gvs, rpt, etc. —
# leaving the `tactics` field effectively empty for most theorems.
# We now accept any lower-snake-case or CamelCase identifier plus the
# full set of HOL4 tacticals, and only drop obvious noise (single-letter
# tokens, string literals).
const HOL4_TACTIC_PAT = r"\b([a-z][a-z0-9_]{2,}|[A-Z][a-zA-Z0-9_]+)\b"

"""
    hol4_tactic_names(tactic::String) -> Vector{String}

Pull plausible tactic / tactical identifiers out of a proof body.
Deduplicated, order-preserving, capped at 40 entries (raised from 20
to reflect the widened gate).
"""
function hol4_tactic_names(tactic::String)::Vector{String}
    matches = [k.match for k in eachmatch(HOL4_TACTIC_PAT, tactic)]
    seen = Set{String}(); unique_t = String[]
    for t in matches
        t ∉ seen && (push!(seen, t); push!(unique_t, t))
        length(unique_t) >= 40 && break
    end
    return unique_t
end

function parse_hol4_file(filepath::String)::Vector{Dict{String,Any}}
    results = Dict{String,Any}[]
    content = try
        read(filepath, String)
    catch
        return results
    end

    fname = basename(filepath)

    # Pattern 1: store_thm style
    for m in eachmatch(r"store_thm\s*\(\s*\"(\w+)\"\s*,\s*``([^`]+)``\s*,\s*(.*?)\)\s*;"s, content)
        name = strip(m.captures[1])
        goal = replace(strip(m.captures[2]), r"\s+" => " ")
        tactic = replace(strip(m.captures[3]), r"\s+" => " ")
        push!(results, Dict{String,Any}(
            "theorem" => name,
            "goal" => goal,
            "tactic_proof" => first(tactic, 8000),
            "tactics" => hol4_tactic_names(tactic),
            "source" => "hol4/$(fname)",
        ))
    end

    # Pattern 2: Theorem/Proof/QED style (plus optional [simp] tag).
    for m in eachmatch(r"Theorem\s+(\w+)(?:\s*\[[^\]]*\])?\s*:\s*(.*?)\s*Proof\s*(.*?)\s*QED"s, content)
        name = strip(m.captures[1])
        goal = replace(strip(m.captures[2]), r"\s+" => " ")
        tactic = replace(strip(m.captures[3]), r"\s+" => " ")
        push!(results, Dict{String,Any}(
            "theorem" => name,
            "goal" => goal,
            "tactic_proof" => first(tactic, 8000),
            "tactics" => hol4_tactic_names(tactic),
            "source" => "hol4/$(fname)",
        ))
    end

    # Pattern 2b: Triviality (same shape as Theorem but lightweight).
    for m in eachmatch(r"Triviality\s+(\w+)(?:\s*\[[^\]]*\])?\s*:\s*(.*?)\s*Proof\s*(.*?)\s*QED"s, content)
        name = strip(m.captures[1])
        goal = replace(strip(m.captures[2]), r"\s+" => " ")
        tactic = replace(strip(m.captures[3]), r"\s+" => " ")
        push!(results, Dict{String,Any}(
            "theorem" => name,
            "goal" => goal,
            "tactic_proof" => first(tactic, 8000),
            "tactics" => hol4_tactic_names(tactic),
            "source" => "hol4/$(fname)",
        ))
    end

    # Pattern 3: Definition / End — named definitions carry a
    # meaningful equation that is training context for HOL4.
    for m in eachmatch(r"Definition\s+(\w+)(?:\s*\[[^\]]*\])?\s*:\s*(.*?)\s*(?:Termination.*?)?End"s, content)
        name = strip(m.captures[1])
        body = replace(strip(m.captures[2]), r"\s+" => " ")
        push!(results, Dict{String,Any}(
            "theorem" => name,
            "goal" => body,
            "tactic_proof" => "",
            "tactics" => ["Definition"],
            "source" => "hol4/$(fname)",
        ))
    end

    # Pattern 3b: Inductive / CoInductive (same End terminator).
    for m in eachmatch(r"(Co)?Inductive\s+(\w+)\s*:\s*(.*?)\s*End"s, content)
        coflag = m.captures[1] === nothing ? "" : "Co"
        name = strip(m.captures[2])
        body = replace(strip(m.captures[3]), r"\s+" => " ")
        push!(results, Dict{String,Any}(
            "theorem" => name,
            "goal" => body,
            "tactic_proof" => "",
            "tactics" => ["$(coflag)Inductive"],
            "source" => "hol4/$(fname)",
        ))
    end

    # Pattern 4: val NAME = prove (older style with () terminator).
    for m in eachmatch(r"val\s+(\w+)\s*=\s*prove\s*\(\s*``([^`]+)``\s*,\s*(.*?)\)\s*;"s, content)
        name = strip(m.captures[1])
        goal = replace(strip(m.captures[2]), r"\s+" => " ")
        tactic = replace(strip(m.captures[3]), r"\s+" => " ")
        push!(results, Dict{String,Any}(
            "theorem" => name,
            "goal" => goal,
            "tactic_proof" => first(tactic, 8000),
            "tactics" => hol4_tactic_names(tactic),
            "source" => "hol4/$(fname)",
        ))
    end

    # Pattern 4b: val NAME = Q.prove / Q.store_thm (Quotation variants).
    for m in eachmatch(r"val\s+(\w+)\s*=\s*Q\.(?:prove|store_thm)\s*\(\s*(?:\"\w+\"\s*,\s*)?`([^`]+)`\s*,\s*(.*?)\)\s*;"s, content)
        name = strip(m.captures[1])
        goal = replace(strip(m.captures[2]), r"\s+" => " ")
        tactic = replace(strip(m.captures[3]), r"\s+" => " ")
        push!(results, Dict{String,Any}(
            "theorem" => name,
            "goal" => goal,
            "tactic_proof" => first(tactic, 8000),
            "tactics" => hol4_tactic_names(tactic),
            "source" => "hol4/$(fname)",
        ))
    end

    return results
end

# ---------------------------------------------------------------------------
# Downloader
# ---------------------------------------------------------------------------

"""
    download_hol4_files() -> Int

Attempt to download HOL4 source files from GitHub.
"""
function download_hol4_files()::Int
    downloaded = 0
    for rel_path in HOL4_FILES
        url = "$(HOL4_RAW_BASE)/$(rel_path)"
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
    generate_synthetic_hol4() -> Vector{Dict{String,Any}}

Generate high-quality synthetic HOL4 proofs using realistic SML
tactic syntax and standard HOL4 library theorems.
"""
function generate_synthetic_hol4()::Vector{Dict{String,Any}}
    arithmetic = [
        ("ADD_COMM", "!m n. m + n = n + m", "Induct_on `m` >> rw[ADD_CLAUSES]"),
        ("ADD_ASSOC", "!m n p. m + (n + p) = (m + n) + p", "Induct_on `m` >> rw[ADD_CLAUSES]"),
        ("MULT_COMM", "!m n. m * n = n * m", "Induct_on `m` >> rw[MULT_CLAUSES] >> decide_tac"),
        ("MULT_ASSOC", "!m n p. m * (n * p) = (m * n) * p", "Induct_on `m` >> rw[MULT_CLAUSES, LEFT_ADD_DISTRIB]"),
        ("LEFT_ADD_DISTRIB", "!m n p. m * (n + p) = m * n + m * p", "Induct_on `m` >> rw[MULT_CLAUSES, ADD_ASSOC]"),
        ("EXP_ADD", "!b m n. b ** (m + n) = b ** m * b ** n", "Induct_on `m` >> rw[EXP, MULT_CLAUSES, MULT_ASSOC]"),
        ("LESS_EQ_REFL", "!n. n <= n", "rw[LESS_EQ_REFL]"),
        ("LESS_EQ_TRANS", "!m n p. m <= n /\\ n <= p ==> m <= p", "metis_tac[LESS_EQ_TRANS]"),
        ("LESS_EQ_ANTISYM", "!m n. m <= n /\\ n <= m ==> (m = n)", "decide_tac"),
        ("DIVMOD_ID", "!n. 0 < n ==> (n DIV n = 1)", "rw[DIV_SELF]"),
        ("MOD_LESS", "!m n. 0 < n ==> m MOD n < n", "metis_tac[MOD_LESS]"),
        ("EVEN_OR_ODD", "!n. EVEN n \\/ ODD n", "Induct_on `n` >> fs[EVEN, ODD]"),
        ("NOT_EVEN_AND_ODD", "!n. ~(EVEN n /\\ ODD n)", "Induct_on `n` >> fs[EVEN, ODD]"),
        ("SUC_NOT_ZERO", "!n. ~(SUC n = 0)", "rw[NOT_SUC]"),
        ("PRE_SUC", "!n. PRE (SUC n) = n", "rw[PRE]"),
        ("ADD_SUC", "!m n. m + SUC n = SUC (m + n)", "rw[ADD_CLAUSES]"),
        ("MULT_SUC", "!m n. m * SUC n = m + m * n", "rw[MULT_CLAUSES]"),
        ("ZERO_LT_SUC", "!n. 0 < SUC n", "decide_tac"),
        ("LT_IMP_LE", "!m n. m < n ==> m <= n", "decide_tac"),
        ("LE_LT_OR_EQ", "!m n. m <= n <=> m < n \\/ (m = n)", "decide_tac"),
    ]

    lists = [
        ("APPEND_NIL", "!l. APPEND l [] = l", "Induct_on `l` >> rw[APPEND]"),
        ("APPEND_ASSOC", "!l1 l2 l3. APPEND l1 (APPEND l2 l3) = APPEND (APPEND l1 l2) l3", "Induct_on `l1` >> rw[APPEND]"),
        ("LENGTH_APPEND", "!l1 l2. LENGTH (APPEND l1 l2) = LENGTH l1 + LENGTH l2", "Induct_on `l1` >> rw[APPEND, LENGTH, ADD_CLAUSES]"),
        ("REVERSE_APPEND", "!l1 l2. REVERSE (APPEND l1 l2) = APPEND (REVERSE l2) (REVERSE l1)", "Induct_on `l1` >> rw[REVERSE, APPEND, APPEND_NIL, APPEND_ASSOC]"),
        ("REVERSE_REVERSE", "!l. REVERSE (REVERSE l) = l", "Induct_on `l` >> rw[REVERSE, REVERSE_APPEND, APPEND]"),
        ("MAP_APPEND", "!f l1 l2. MAP f (APPEND l1 l2) = APPEND (MAP f l1) (MAP f l2)", "Induct_on `l1` >> rw[MAP, APPEND]"),
        ("LENGTH_MAP", "!f l. LENGTH (MAP f l) = LENGTH l", "Induct_on `l` >> rw[MAP, LENGTH]"),
        ("MAP_MAP", "!f g l. MAP f (MAP g l) = MAP (f o g) l", "Induct_on `l` >> rw[MAP]"),
        ("FILTER_APPEND", "!P l1 l2. FILTER P (APPEND l1 l2) = APPEND (FILTER P l1) (FILTER P l2)", "Induct_on `l1` >> rw[FILTER, APPEND] >> Cases_on `P h` >> rw[APPEND]"),
        ("MEM_APPEND", "!x l1 l2. MEM x (APPEND l1 l2) <=> MEM x l1 \\/ MEM x l2", "Induct_on `l1` >> rw[MEM, APPEND] >> metis_tac[]"),
        ("EVERY_APPEND", "!P l1 l2. EVERY P (APPEND l1 l2) <=> EVERY P l1 /\\ EVERY P l2", "Induct_on `l1` >> rw[EVERY, APPEND] >> metis_tac[]"),
        ("FLAT_APPEND", "!l1 l2. FLAT (APPEND l1 l2) = APPEND (FLAT l1) (FLAT l2)", "Induct_on `l1` >> rw[FLAT, APPEND, APPEND_ASSOC]"),
        ("HD_APPEND", "!l1 l2. l1 <> [] ==> (HD (APPEND l1 l2) = HD l1)", "Cases_on `l1` >> rw[APPEND, HD]"),
        ("EL_MAP", "!n f l. n < LENGTH l ==> (EL n (MAP f l) = f (EL n l))", "Induct_on `n` >> Cases_on `l` >> rw[MAP, EL, HD, TL, LENGTH]"),
        ("NULL_EQ", "!l. NULL l <=> (l = [])", "Cases_on `l` >> rw[NULL]"),
    ]

    sets = [
        ("IN_UNION", "!x s t. x IN (s UNION t) <=> x IN s \\/ x IN t", "rw[UNION_DEF, GSPECIFICATION] >> metis_tac[]"),
        ("IN_INTER", "!x s t. x IN (s INTER t) <=> x IN s /\\ x IN t", "rw[INTER_DEF, GSPECIFICATION]"),
        ("SUBSET_REFL", "!s. s SUBSET s", "rw[SUBSET_DEF]"),
        ("SUBSET_TRANS", "!s t u. s SUBSET t /\\ t SUBSET u ==> s SUBSET u", "rw[SUBSET_DEF] >> metis_tac[]"),
        ("UNION_COMM", "!s t. s UNION t = t UNION s", "rw[EXTENSION, IN_UNION] >> metis_tac[]"),
        ("INTER_COMM", "!s t. s INTER t = t INTER s", "rw[EXTENSION, IN_INTER] >> metis_tac[]"),
        ("UNION_ASSOC", "!s t u. s UNION (t UNION u) = (s UNION t) UNION u", "rw[EXTENSION, IN_UNION] >> metis_tac[]"),
        ("INTER_ASSOC", "!s t u. s INTER (t INTER u) = (s INTER t) INTER u", "rw[EXTENSION, IN_INTER] >> metis_tac[]"),
        ("UNION_EMPTY", "!s. s UNION EMPTY = s", "rw[EXTENSION, IN_UNION, NOT_IN_EMPTY]"),
        ("INTER_UNIV", "!s. s INTER UNIV = s", "rw[EXTENSION, IN_INTER, IN_UNIV]"),
        ("EMPTY_SUBSET", "!s. EMPTY SUBSET s", "rw[SUBSET_DEF, NOT_IN_EMPTY]"),
        ("SUBSET_UNION", "!s t. s SUBSET (s UNION t)", "rw[SUBSET_DEF, IN_UNION]"),
        ("INTER_SUBSET", "!s t. (s INTER t) SUBSET s", "rw[SUBSET_DEF, IN_INTER]"),
        ("CARD_UNION_DISJOINT", "!s t. FINITE s /\\ FINITE t /\\ DISJOINT s t ==> (CARD (s UNION t) = CARD s + CARD t)", "metis_tac[CARD_UNION]"),
        ("FINITE_EMPTY", "FINITE EMPTY", "rw[FINITE_EMPTY]"),
    ]

    booleans = [
        ("CONJ_COMM", "!p q. p /\\ q <=> q /\\ p", "metis_tac[]"),
        ("DISJ_COMM", "!p q. p \\/ q <=> q \\/ p", "metis_tac[]"),
        ("IMP_ANTISYM", "!p q. (p ==> q) /\\ (q ==> p) ==> (p <=> q)", "metis_tac[]"),
        ("CONTRAPOSITIVE", "!p q. (p ==> q) <=> (~q ==> ~p)", "metis_tac[]"),
        ("DE_MORGAN1", "!p q. ~(p /\\ q) <=> ~p \\/ ~q", "metis_tac[]"),
        ("DE_MORGAN2", "!p q. ~(p \\/ q) <=> ~p /\\ ~q", "metis_tac[]"),
        ("DOUBLE_NEG", "!p. ~~p <=> p", "metis_tac[]"),
        ("EXCLUDED_MIDDLE", "!p. p \\/ ~p", "metis_tac[]"),
        ("COND_TRUE", "!x y. (if T then x else y) = x", "rw[]"),
        ("COND_FALSE", "!x y. (if F then x else y) = y", "rw[]"),
        ("AND_CLAUSES", "!p. (T /\\ p <=> p) /\\ (p /\\ T <=> p) /\\ (F /\\ p <=> F) /\\ (p /\\ F <=> F)", "rw[]"),
        ("OR_CLAUSES", "!p. (T \\/ p <=> T) /\\ (p \\/ T <=> T) /\\ (F \\/ p <=> p) /\\ (p \\/ F <=> p)", "rw[]"),
        ("IMP_CLAUSES", "!p. (T ==> p <=> p) /\\ (p ==> T <=> T) /\\ (F ==> p <=> T) /\\ (p ==> p <=> T)", "rw[]"),
        ("FORALL_CONJ", "!P Q. (!x. P x /\\ Q x) <=> (!x. P x) /\\ (!x. Q x)", "metis_tac[]"),
        ("EXISTS_DISJ", "!P Q. (?x. P x \\/ Q x) <=> (?x. P x) \\/ (?x. Q x)", "metis_tac[]"),
    ]

    sorting = [
        ("SORTED_CONS", "!R x l. SORTED R (x::l) <=> SORTED R l /\\ (!y. MEM y l ==> R x y)", "rw[SORTED_DEF] >> metis_tac[]"),
        ("SORTED_APPEND", "!R l1 l2. transitive R ==> (SORTED R (l1 ++ l2) <=> SORTED R l1 /\\ SORTED R l2 /\\ !x y. MEM x l1 /\\ MEM y l2 ==> R x y)", "Induct_on `l1` >> rw[SORTED_DEF, APPEND, MEM] >> metis_tac[]"),
        ("PERM_REFL", "!l. PERM l l", "rw[PERM_REFL]"),
        ("PERM_SYM", "!l1 l2. PERM l1 l2 ==> PERM l2 l1", "metis_tac[PERM_SYM]"),
        ("PERM_TRANS", "!l1 l2 l3. PERM l1 l2 /\\ PERM l2 l3 ==> PERM l1 l3", "metis_tac[PERM_TRANS]"),
        ("PERM_LENGTH", "!l1 l2. PERM l1 l2 ==> (LENGTH l1 = LENGTH l2)", "metis_tac[PERM_LENGTH]"),
        ("QSORT_SORTED", "!R l. total R /\\ transitive R ==> SORTED R (QSORT R l)", "metis_tac[QSORT_SORTED]"),
        ("QSORT_PERM", "!R l. PERM l (QSORT R l)", "metis_tac[QSORT_PERM]"),
        ("QSORT_MEM", "!R x l. MEM x (QSORT R l) <=> MEM x l", "metis_tac[QSORT_PERM, PERM_MEM_EQ]"),
        ("QSORT_STABLE", "!R l. SORTED R l ==> (QSORT R l = l)", "Induct_on `l` >> rw[QSORT_DEF, SORTED_DEF] >> metis_tac[SORTED_EQ]"),
    ]

    cakeml_style = [
        ("EVAL_INT_ADD", "!n1 n2. eval_exp env (Add (Lit (IntLit n1)) (Lit (IntLit n2))) = Rval (Litv (IntLit (n1 + n2)))", "rw[eval_exp_def, do_app_def]"),
        ("TYPE_SOUNDNESS", "!e t env. type_of env e = SOME t ==> ?v. eval_exp env e = Rval v /\\ value_type v t", "Induct_on `e` >> rw[type_of_def, eval_exp_def] >> metis_tac[]"),
        ("COMPILER_CORRECTNESS", "!e env. semantics env e <> Fail ==> observed (compile e) = observed (eval e)", "metis_tac[compiler_correct]"),
        ("ENV_LOOKUP", "!x v env. lookup x ((x,v)::env) = SOME v", "rw[lookup_def]"),
        ("ENV_LOOKUP_OTHER", "!x y v env. x <> y ==> (lookup x ((y,v)::env) = lookup x env)", "rw[lookup_def]"),
    ]

    all_categories = [
        ("arithmetic", arithmetic),
        ("lists", lists),
        ("sets", sets),
        ("booleans", booleans),
        ("sorting", sorting),
        ("cakeml_style", cakeml_style),
    ]

    proofs = Dict{String,Any}[]
    for (category, theorems) in all_categories
        for (name, goal, tactic) in theorems
            push!(proofs, Dict{String,Any}(
                "theorem" => name,
                "goal" => goal,
                "tactic_proof" => tactic,
                "tactics" => hol4_tactic_names(tactic),
                "source" => "hol4_synthetic/$(category)",
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

    println("[HOL4] Phase 1: Attempting to download from GitHub ...")
    downloaded = download_hol4_files()
    println("  Downloaded/cached $(downloaded) files")

    # Phase 1 widening (2026-04-18, echidna follow-up): additionally
    # walk a CakeML clone at external_corpora/hol4_cakeml/ when
    # present. CakeML is a verified ML compiler written in HOL4;
    # its basis / compiler / semantics / translator / candle trees
    # hold hundreds of *Script.sml files with real HOL4 proofs.
    sml_files = String[]
    for fname in readdir(EXTERNAL_DIR)
        endswith(fname, ".sml") && push!(sml_files, joinpath(EXTERNAL_DIR, fname))
    end
    cakeml_root = joinpath(dirname(EXTERNAL_DIR), "hol4_cakeml")
    if isdir(cakeml_root)
        println("[HOL4] Walking CakeML clone at $(cakeml_root) ...")
        for (root, _dirs, files) in walkdir(cakeml_root)
            for fname in files
                endswith(fname, ".sml") && push!(sml_files, joinpath(root, fname))
            end
        end
    end
    # 2026-04-18 (echidna#12 100K push): HOL4 full tree at
    # HOL-Theorem-Prover/HOL ships ~1 357 *Script.sml files — the
    # main HOL4 distribution, separate from the CakeML-specific
    # clone above. Walk it too when present.
    hol4_full = joinpath(dirname(EXTERNAL_DIR), "hol4-full")
    if isdir(hol4_full)
        println("[HOL4] Walking HOL4 full-tree clone at $(hol4_full) ...")
        for (root, _dirs, files) in walkdir(hol4_full)
            for fname in files
                endswith(fname, ".sml") && push!(sml_files, joinpath(root, fname))
            end
        end
    end
    println("  $(length(sml_files)) HOL4 source files to parse")

    processed = 0
    for fpath in sml_files
        # 2026-04-18 (echidna#12 100K push): large auto-generated
        # machine-code model files (arm/mips/riscv/cheri/x64) trigger
        # PCRE catastrophic backtracking; skip anything >2 MB.
        fsize = try filesize(fpath) catch; 0 end
        if fsize > 2_000_000
            processed += 1
            continue
        end
        parsed = try
            parse_hol4_file(fpath)
        catch
            Dict{String,Any}[]
        end
        append!(all_entries, parsed)
        processed += 1
        if processed % 100 == 0
            println("  processed $(processed)/$(length(sml_files)) files — running count: $(length(all_entries))")
        end
    end
    extracted_count = length(all_entries)

    println("[HOL4] Phase 2: Generating synthetic proofs ...")
    synthetic = generate_synthetic_hol4()
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
            "prover" => "HOL4",
            "theorem" => entry["theorem"],
            "goal" => entry["goal"],
            "context" => get(entry, "tactics", String[]),
            "tactic_proof" => get(entry, "tactic_proof", ""),
            "source" => get(entry, "source", "hol4"),
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
        "prover" => "HOL4",
        "total_proofs" => length(output_records),
        "extracted_from_source" => extracted_count,
        "synthetic_added" => length(output_records) - extracted_count,
        "id_range" => [START_ID, current_id - 1],
        "output_file" => OUTPUT_FILE,
    )
    open(STATS_FILE, "w") do fh
        JSON3.pretty(fh, stats)
    end

    println("\n[HOL4] COMPLETE: $(length(output_records)) proofs written to $(OUTPUT_FILE)")
    println("  Extracted from source: $(extracted_count)")
    println("  Synthetic: $(length(output_records) - extracted_count)")
    return (extracted_count, length(output_records) - extracted_count)
end

if abspath(PROGRAM_FILE) == abspath(@__FILE__)
    run()
end
