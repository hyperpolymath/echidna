#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2026 ECHIDNA Project Team
#
# Extract proofs from Mizar Mathematical Library (MML) and convert to ECHIDNA
# training format.
#
# Attempts to download from the MML GitHub mirror. Falls back to generating
# high-quality synthetic Mizar proofs.
#
# Mizar is a formal language for writing mathematical proofs in a readable,
# declarative style. The MML contains over 60,000 theorems across all areas
# of mathematics.
#
# Output: training_data/proof_states_mizar.jsonl
# ID range: 94000+

using JSON3

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

const REPO_ROOT = dirname(dirname(abspath(@__FILE__)))
const EXTERNAL_DIR = joinpath(REPO_ROOT, "external_corpora", "mizar")
const OUTPUT_DIR = joinpath(REPO_ROOT, "training_data")
const OUTPUT_FILE = joinpath(OUTPUT_DIR, "proof_states_mizar.jsonl")
const STATS_FILE = joinpath(OUTPUT_DIR, "stats_mizar.json")
const START_ID = 94000

# Mizar MML articles (some key ones)
const MIZAR_RAW = "https://raw.githubusercontent.com/MizarProject/mml/master"
const MIZAR_FILES = [
    "abcmiz_0.miz", "absvalue.miz", "algstr_0.miz", "arytm_0.miz",
    "arytm_1.miz", "arytm_3.miz", "binop_1.miz", "boole.miz",
    "card_1.miz", "complex1.miz", "enumset1.miz", "finseq_1.miz",
    "finset_1.miz", "funct_1.miz", "funct_2.miz", "group_1.miz",
    "int_1.miz", "lattices.miz", "membered.miz", "nat_1.miz",
    "numbers.miz", "ordinal1.miz", "orders_1.miz", "partfun1.miz",
    "pre_topc.miz", "prob_1.miz", "real_1.miz", "relat_1.miz",
    "relset_1.miz", "ring_1.miz", "seq_1.miz", "square_1.miz",
    "struct_0.miz", "subset_1.miz", "tops_1.miz", "tarski.miz",
    "topreal1.miz", "topsp_1.miz", "vectsp_1.miz", "xboole_0.miz",
    "xreal_0.miz", "zfmisc_1.miz",
]

# ---------------------------------------------------------------------------
# Parser
# ---------------------------------------------------------------------------

"""
    parse_mizar_file(filepath::String) -> Vector{Dict{String,Any}}

Parse a Mizar .miz file and extract theorem/registration/definition blocks.

Mizar proofs are structured as:
    theorem ThName:
      statement
    proof
      ...
    end;
"""
function parse_mizar_file(filepath::String)::Vector{Dict{String,Any}}
    results = Dict{String,Any}[]
    content = try
        read(filepath, String)
    catch
        return results
    end

    # Pattern: theorem [Label:] statement proof ... end;
    for m in eachmatch(r"theorem\s+(?:(\w+)\s*:)?\s*(.*?)\s*proof\s*(.*?)\s*end\s*;"si, content)
        label = m.captures[1] !== nothing ? m.captures[1] : "anonymous"
        statement = first(replace(strip(m.captures[2]), r"\s+" => " "), 300)
        proof_body = first(replace(strip(m.captures[3]), r"\s+" => " "), 500)

        # Extract Mizar proof steps
        steps = [lowercase(k.match) for k in eachmatch(
            r"\b(assume|let|take|consider|thus|hence|suppose|per cases|set|reconsider|hereby)\b"i,
            proof_body
        )]
        seen = Set{String}(); unique_steps = String[]
        for s in steps
            s ∉ seen && (push!(seen, s); push!(unique_steps, s))
        end

        push!(results, Dict{String,Any}(
            "theorem" => label,
            "goal" => statement,
            "tactic_proof" => proof_body,
            "tactics" => unique_steps,
            "source" => "mizar/$(basename(filepath))",
        ))
    end

    # Also extract registrations (important Mizar concept)
    for (i, m) in enumerate(eachmatch(r"registration\s*(.*?)\s*end\s*;"si, content))
        body = first(replace(strip(m.captures[1]), r"\s+" => " "), 300)
        if !isempty(body)
            push!(results, Dict{String,Any}(
                "theorem" => "registration_$(i-1)",
                "goal" => body,
                "tactic_proof" => "",
                "tactics" => ["registration"],
                "source" => "mizar/$(basename(filepath))",
            ))
        end
    end

    # Widening (2026-04-18): Mizar has many more named constructs
    # than `theorem` + `registration`. Capture `definition`, `scheme`,
    # `notation`, `reserve`, and the full-paragraph `theorem :: NAME`
    # form without a proof (axioms / held-as-obvious claims).
    def_pat = r"definition\s*(.*?)\s*end\s*;"si
    scheme_pat = r"scheme\s+(\w+)\s*\{(.*?)\}\s*:\s*(.*?)\s*proof\s*(.*?)\s*end\s*;"si
    notation_pat = r"notation\s*(.*?)\s*end\s*;"si
    reserve_pat = r"reserve\s+(.+?)\s+for\s+(.+?);"s
    axiom_thm_pat = r"theorem\s+(?:(\w+)\s*:)?\s*(.*?);(?!\s*proof)"s

    for (i, m) in enumerate(eachmatch(def_pat, content))
        body = first(replace(strip(m.captures[1]), r"\s+" => " "), 400)
        isempty(body) && continue
        push!(results, Dict{String,Any}(
            "theorem" => "definition_$(basename(filepath))_$(i)",
            "goal" => body,
            "tactic_proof" => "",
            "tactics" => ["definition"],
            "source" => "mizar/$(basename(filepath))",
        ))
    end
    for m in eachmatch(scheme_pat, content)
        name = strip(m.captures[1])
        args = first(replace(strip(m.captures[2]), r"\s+" => " "), 200)
        stmt = first(replace(strip(m.captures[3]), r"\s+" => " "), 300)
        push!(results, Dict{String,Any}(
            "theorem" => name,
            "goal" => stmt,
            "tactic_proof" => first(replace(strip(m.captures[4]), r"\s+" => " "), 500),
            "tactics" => ["scheme"],
            "scheme_args" => args,
            "source" => "mizar/$(basename(filepath))",
        ))
    end
    for (i, m) in enumerate(eachmatch(notation_pat, content))
        body = first(replace(strip(m.captures[1]), r"\s+" => " "), 300)
        isempty(body) && continue
        push!(results, Dict{String,Any}(
            "theorem" => "notation_$(basename(filepath))_$(i)",
            "goal" => body,
            "tactic_proof" => "",
            "tactics" => ["notation"],
            "source" => "mizar/$(basename(filepath))",
        ))
    end
    for (i, m) in enumerate(eachmatch(reserve_pat, content))
        vars = strip(String(m.captures[1]))
        ty = strip(String(m.captures[2]))
        push!(results, Dict{String,Any}(
            "theorem" => "reserve_$(basename(filepath))_$(i)",
            "goal" => "$(vars) for $(ty)",
            "tactic_proof" => "",
            "tactics" => ["reserve"],
            "source" => "mizar/$(basename(filepath))",
        ))
    end

    return results
end

# ---------------------------------------------------------------------------
# Downloader
# ---------------------------------------------------------------------------

"""
    download_mizar_files() -> Int

Attempt to download Mizar MML articles.
"""
function download_mizar_files()::Int
    downloaded = 0
    for fname in MIZAR_FILES
        url = "$(MIZAR_RAW)/$(fname)"
        local_path = joinpath(EXTERNAL_DIR, fname)
        if isfile(local_path)
            downloaded += 1
            continue
        end
        try
            download(url, local_path)
            downloaded += 1
            println("  Downloaded: $(fname)")
        catch exc
            println("  Skipped $(fname): $(exc)")
        end
    end
    return downloaded
end

# ---------------------------------------------------------------------------
# Synthetic generation
# ---------------------------------------------------------------------------

"""
    generate_synthetic_mizar() -> Vector{Dict{String,Any}}

Generate high-quality synthetic Mizar proofs.

Mizar uses a structured, readable proof language with keywords like
assume, let, take, consider, thus, hence, suppose, per cases,
set, reconsider, hereby, thesis, and ... by reference.
"""
function generate_synthetic_mizar()::Vector{Dict{String,Any}}
    set_theory = [
        ("union_comm", "for A, B being set holds A \\/ B = B \\/ A",
         "let A, B be set; thus A \\/ B = B \\/ A by XBOOLE_0:def 3;"),
        ("inter_comm", "for A, B being set holds A /\\ B = B /\\ A",
         "let A, B be set; thus A /\\ B = B /\\ A by XBOOLE_0:def 4;"),
        ("union_assoc", "for A, B, C being set holds A \\/ (B \\/ C) = (A \\/ B) \\/ C",
         "let A, B, C be set; thus thesis by XBOOLE_1:4;"),
        ("inter_assoc", "for A, B, C being set holds A /\\ (B /\\ C) = (A /\\ B) /\\ C",
         "let A, B, C be set; thus thesis by XBOOLE_1:16;"),
        ("union_empty", "for A being set holds A \\/ {} = A",
         "let A be set; thus thesis by XBOOLE_1:1;"),
        ("inter_univ", "for A being set holds A /\\ A = A",
         "let A be set; thus thesis by XBOOLE_1:17;"),
        ("subset_refl", "for A being set holds A c= A",
         "let A be set; let x be object; assume x in A; thus x in A;"),
        ("subset_trans", "for A, B, C being set st A c= B & B c= C holds A c= C",
         "let A, B, C be set; assume A1: A c= B; assume A2: B c= C; let x be object; assume x in A; then x in B by A1; hence x in C by A2;"),
        ("subset_union_left", "for A, B being set holds A c= A \\/ B",
         "let A, B be set; let x be object; assume x in A; hence x in A \\/ B by XBOOLE_0:def 3;"),
        ("subset_inter_left", "for A, B being set holds A /\\ B c= A",
         "let A, B be set; let x be object; assume x in A /\\ B; hence x in A by XBOOLE_0:def 4;"),
        ("de_morgan_union", "for A, B, X being set holds X \\ (A \\/ B) = (X \\ A) /\\ (X \\ B)",
         "let A, B, X be set; thus thesis by XBOOLE_1:53;"),
        ("de_morgan_inter", "for A, B, X being set holds X \\ (A /\\ B) = (X \\ A) \\/ (X \\ B)",
         "let A, B, X be set; thus thesis by XBOOLE_1:54;"),
        ("empty_subset", "for A being set holds {} c= A",
         "let A be set; thus {} c= A by XBOOLE_1:2;"),
        ("subset_antisym", "for A, B being set st A c= B & B c= A holds A = B",
         "let A, B be set; assume A c= B; assume B c= A; thus A = B by XBOOLE_0:def 10;"),
        ("power_set_member", "for A, B being set st A c= B holds A in bool B",
         "let A, B be set; assume A c= B; thus A in bool B by ZFMISC_1:def 1;"),
    ]

    natural_numbers = [
        ("nat_add_comm", "for m, n being Nat holds m + n = n + m",
         "let m, n be Nat; thus m + n = n + m by XCMPLX_0:def 3;"),
        ("nat_add_assoc", "for m, n, k being Nat holds (m + n) + k = m + (n + k)",
         "let m, n, k be Nat; thus (m + n) + k = m + (n + k) by XCMPLX_1:1;"),
        ("nat_mul_comm", "for m, n being Nat holds m * n = n * m",
         "let m, n be Nat; thus m * n = n * m by XCMPLX_0:def 4;"),
        ("nat_mul_assoc", "for m, n, k being Nat holds (m * n) * k = m * (n * k)",
         "let m, n, k be Nat; thus (m * n) * k = m * (n * k) by XCMPLX_1:4;"),
        ("nat_distrib", "for m, n, k being Nat holds m * (n + k) = m * n + m * k",
         "let m, n, k be Nat; thus m * (n + k) = m * n + m * k by XCMPLX_1:8;"),
        ("nat_add_zero", "for n being Nat holds n + 0 = n",
         "let n be Nat; thus n + 0 = n;"),
        ("nat_mul_zero", "for n being Nat holds n * 0 = 0",
         "let n be Nat; thus n * 0 = 0;"),
        ("nat_mul_one", "for n being Nat holds n * 1 = n",
         "let n be Nat; thus n * 1 = n;"),
        ("nat_le_refl", "for n being Nat holds n <= n",
         "let n be Nat; thus n <= n;"),
        ("nat_le_antisym", "for m, n being Nat st m <= n & n <= m holds m = n",
         "let m, n be Nat; assume A1: m <= n; assume A2: n <= m; thus m = n by A1, A2, XXREAL_0:1;"),
        ("nat_le_trans", "for m, n, k being Nat st m <= n & n <= k holds m <= k",
         "let m, n, k be Nat; assume m <= n; assume n <= k; hence m <= k by XXREAL_0:2;"),
        ("nat_lt_succ", "for n being Nat holds n < n + 1",
         "let n be Nat; thus n < n + 1 by NAT_1:13;"),
        ("nat_induction_schema", "for P being Nat-defined Function st P.0 is true & (for n being Nat st P.n is true holds P.(n+1) is true) holds for n being Nat holds P.n is true",
         "let P be Nat-defined Function; assume A1: P.0 is true; assume A2: for n being Nat st P.n is true holds P.(n+1) is true; defpred Q[Nat] means P.\$1 is true; A3: Q[0] by A1; A4: for n being Nat st Q[n] holds Q[n+1] by A2; thus for n being Nat holds Q[n] from NAT_1:sch 2(A3, A4);"),
        ("nat_well_ordering", "for X being non empty Subset of NAT ex m being Nat st m in X & for n being Nat st n in X holds m <= n",
         "let X be non empty Subset of NAT; thus thesis by NAT_1:def 1;"),
        ("nat_div_mod", "for a being Nat, b being non zero Nat holds a = b * (a div b) + (a mod b)",
         "let a be Nat, b be non zero Nat; thus a = b * (a div b) + (a mod b) by NAT_D:def 1, NAT_D:def 2;"),
    ]

    real_numbers = [
        ("real_add_comm", "for x, y being Real holds x + y = y + x",
         "let x, y be Real; thus x + y = y + x by XCMPLX_0:def 3;"),
        ("real_mul_comm", "for x, y being Real holds x * y = y * x",
         "let x, y be Real; thus x * y = y * x by XCMPLX_0:def 4;"),
        ("real_add_inv", "for x being Real holds x + (-x) = 0",
         "let x be Real; thus x + (-x) = 0 by XCMPLX_0:def 6;"),
        ("real_mul_inv", "for x being non zero Real holds x * x\" = 1",
         "let x be non zero Real; thus x * x\" = 1 by XCMPLX_0:def 7;"),
        ("real_abs_nonneg", "for x being Real holds |.x.| >= 0",
         "let x be Real; thus |.x.| >= 0 by ABSVALUE:4;"),
        ("real_abs_zero", "for x being Real holds |.x.| = 0 iff x = 0",
         "let x be Real; thus |.x.| = 0 iff x = 0 by ABSVALUE:2;"),
        ("real_triangle", "for x, y being Real holds |.x + y.| <= |.x.| + |.y.|",
         "let x, y be Real; thus |.x + y.| <= |.x.| + |.y.| by ABSVALUE:13;"),
        ("real_sq_nonneg", "for x being Real holds x ^2 >= 0",
         "let x be Real; thus x ^2 >= 0 by XREAL_1:63;"),
        ("real_archimedes", "for x being positive Real ex n being Nat st x < n",
         "let x be positive Real; thus ex n being Nat st x < n by INT_1:37;"),
        ("real_complete", "for A being non empty bounded_above Subset of REAL ex s being Real st s is_least_upper_bound_of A",
         "let A be non empty bounded_above Subset of REAL; thus thesis by XXREAL_2:28;"),
    ]

    functions = [
        ("func_comp_assoc", "for f, g, h being Function st rng h c= dom g & rng g c= dom f holds (f * g) * h = f * (g * h)",
         "let f, g, h be Function; assume A1: rng h c= dom g; assume A2: rng g c= dom f; thus (f * g) * h = f * (g * h) by A1, A2, RELAT_1:36;"),
        ("func_id_comp", "for f being Function holds f * (id dom f) = f",
         "let f be Function; thus f * (id dom f) = f by FUNCT_1:22;"),
        ("func_injective_comp", "for f, g being Function st f is one-to-one & g is one-to-one & rng g c= dom f holds f * g is one-to-one",
         "let f, g be Function; assume A1: f is one-to-one; assume A2: g is one-to-one; assume A3: rng g c= dom f; thus f * g is one-to-one by A1, A2, A3, FUNCT_1:27;"),
        ("func_surjective_comp", "for f, g being Function st f is onto & g is onto holds f * g is onto",
         "let f, g be Function; assume f is onto; assume g is onto; thus f * g is onto by FUNCT_1:28;"),
        ("func_inverse", "for f being one-to-one Function holds f \" * f = id dom f",
         "let f be one-to-one Function; thus f \" * f = id dom f by FUNCT_1:44;"),
        ("func_image_union", "for f being Function, A, B being set holds f.:( A \\/ B) = f.:A \\/ f.:B",
         "let f be Function, A, B be set; thus f.:(A \\/ B) = f.:A \\/ f.:B by RELAT_1:120;"),
        ("func_image_inter_inj", "for f being one-to-one Function, A, B being set holds f.:(A /\\ B) = f.:A /\\ f.:B",
         "let f be one-to-one Function, A, B be set; thus f.:(A /\\ B) = f.:A /\\ f.:B by FUNCT_1:72;"),
        ("func_preimage_union", "for f being Function, A, B being set holds f\"(A \\/ B) = f\"A \\/ f\"B",
         "let f be Function, A, B be set; thus f\"(A \\/ B) = f\"A \\/ f\"B by RELAT_1:171;"),
    ]

    topology = [
        ("open_empty", "for T being TopSpace holds {} is open Subset of T",
         "let T be TopSpace; thus {} is open Subset of T by PRE_TOPC:def 2;"),
        ("open_carrier", "for T being TopSpace holds [#]T is open Subset of T",
         "let T be TopSpace; thus [#]T is open Subset of T by PRE_TOPC:def 2;"),
        ("open_union", "for T being TopSpace, F being Subset-Family of T st for A being Subset of T st A in F holds A is open holds union F is open Subset of T",
         "let T be TopSpace; let F be Subset-Family of T; assume for A being Subset of T st A in F holds A is open; thus union F is open Subset of T by PRE_TOPC:def 2;"),
        ("closed_empty", "for T being TopSpace holds {} is closed Subset of T",
         "let T be TopSpace; thus {} is closed Subset of T by PRE_TOPC:3;"),
        ("closed_carrier", "for T being TopSpace holds [#]T is closed Subset of T",
         "let T be TopSpace; thus [#]T is closed Subset of T by PRE_TOPC:3;"),
        ("closure_subset", "for T being TopSpace, A being Subset of T holds A c= Cl A",
         "let T be TopSpace, A be Subset of T; thus A c= Cl A by PRE_TOPC:18;"),
        ("closure_closed", "for T being TopSpace, A being Subset of T holds Cl A is closed",
         "let T be TopSpace, A be Subset of T; thus Cl A is closed by PRE_TOPC:def 6;"),
        ("continuous_preimage_open", "for f being continuous Function of T1, T2, V being open Subset of T2 holds f\"V is open Subset of T1",
         "let f be continuous Function of T1, T2; let V be open Subset of T2; thus f\"V is open Subset of T1 by TOPS_2:43;"),
        ("compact_closed_subset", "for T being compact TopSpace, A being closed Subset of T holds A is compact",
         "let T be compact TopSpace; let A be closed Subset of T; thus A is compact by COMPTS_1:8;"),
        ("connected_image", "for f being continuous Function of T1, T2 st T1 is connected holds f.:[#]T1 is connected Subset of T2",
         "let f be continuous Function of T1, T2; assume T1 is connected; thus f.:[#]T1 is connected Subset of T2 by CONNSP_1:15;"),
    ]

    algebra = [
        ("group_id_unique", "for G being Group holds for e1, e2 being Element of G st (for a being Element of G holds e1 * a = a & a * e1 = a) & (for a being Element of G holds e2 * a = a & a * e2 = a) holds e1 = e2",
         "let G be Group; let e1, e2 be Element of G; assume A1: for a being Element of G holds e1 * a = a & a * e1 = a; assume A2: for a being Element of G holds e2 * a = a & a * e2 = a; thus e1 = e1 * e2 by A2 .= e2 by A1;"),
        ("group_inv_unique", "for G being Group, a, b1, b2 being Element of G st a * b1 = 1_G & a * b2 = 1_G holds b1 = b2",
         "let G be Group; let a, b1, b2 be Element of G; assume A1: a * b1 = 1_G; assume A2: a * b2 = 1_G; thus b1 = (a\\\") * a * b1 by GROUP_1:def 5 .= (a\\\") * (a * b1) by GROUP_1:def 3 .= (a\\\") * 1_G by A1 .= a\\\" by GROUP_1:def 4 .= (a\\\") * (a * b2) by A2 .= (a\\\") * a * b2 by GROUP_1:def 3 .= 1_G * b2 by GROUP_1:def 5 .= b2 by GROUP_1:def 4;"),
        ("group_inv_inv", "for G being Group, a being Element of G holds (a\\\")\\\" = a",
         "let G be Group; let a be Element of G; thus (a\\\")\\\" = a by GROUP_1:8;"),
        ("group_inv_prod", "for G being Group, a, b being Element of G holds (a * b)\\\" = b\\\" * a\\\"",
         "let G be Group; let a, b be Element of G; thus (a * b)\\\" = b\\\" * a\\\" by GROUP_1:17;"),
        ("subgroup_criterion", "for G being Group, H being non empty Subset of G st (for a, b being Element of G st a in H & b in H holds a * b\\\" in H) holds H is Subgroup of G",
         "let G be Group; let H be non empty Subset of G; assume for a, b being Element of G st a in H & b in H holds a * b\\\" in H; thus H is Subgroup of G by GROUP_2:52;"),
        ("ring_add_comm", "for R being Ring, a, b being Element of R holds a + b = b + a",
         "let R be Ring; let a, b be Element of R; thus a + b = b + a by RLVECT_1:2;"),
        ("ring_mul_assoc", "for R being Ring, a, b, c being Element of R holds (a * b) * c = a * (b * c)",
         "let R be Ring; let a, b, c be Element of R; thus (a * b) * c = a * (b * c) by GROUP_1:def 3;"),
        ("ring_distrib_left", "for R being Ring, a, b, c being Element of R holds a * (b + c) = a * b + a * c",
         "let R be Ring; let a, b, c be Element of R; thus a * (b + c) = a * b + a * c by VECTSP_1:def 7;"),
    ]

    sequences = [
        ("seq_convergent", "for seq being Real_Sequence st seq is convergent holds for e being Real st e > 0 ex N being Nat st for n being Nat st n >= N holds |.seq.n - lim seq.| < e",
         "let seq be Real_Sequence; assume A1: seq is convergent; let e be Real; assume A2: e > 0; thus ex N being Nat st for n being Nat st n >= N holds |.seq.n - lim seq.| < e by A1, A2, SEQ_2:def 7;"),
        ("seq_monotone_incr", "for seq being Real_Sequence st seq is increasing & seq is bounded_above holds seq is convergent",
         "let seq be Real_Sequence; assume A1: seq is increasing; assume A2: seq is bounded_above; thus seq is convergent by A1, A2, SEQ_4:37;"),
        ("seq_bounded_convergent", "for seq being Real_Sequence st seq is convergent holds seq is bounded",
         "let seq be Real_Sequence; assume seq is convergent; hence seq is bounded by SEQ_2:13;"),
        ("seq_bolzano_weierstrass", "for seq being Real_Sequence st seq is bounded ex seq1 being subsequence of seq st seq1 is convergent",
         "let seq be Real_Sequence; assume A1: seq is bounded; consider seq1 being subsequence of seq such that A2: seq1 is monotone by A1, SEQ_4:39; take seq1; seq1 is bounded by A1, SEQ_4:27; hence seq1 is convergent by A2, SEQ_4:37, SEQ_4:38;"),
        ("seq_cauchy_criterion", "for seq being Real_Sequence holds seq is convergent iff seq is Cauchy",
         "let seq be Real_Sequence; thus seq is convergent iff seq is Cauchy by SEQ_4:25;"),
        ("seq_limit_add", "for seq1, seq2 being Real_Sequence st seq1 is convergent & seq2 is convergent holds lim (seq1 + seq2) = lim seq1 + lim seq2",
         "let seq1, seq2 be Real_Sequence; assume A1: seq1 is convergent; assume A2: seq2 is convergent; thus lim (seq1 + seq2) = lim seq1 + lim seq2 by A1, A2, SEQ_2:6;"),
        ("seq_limit_mul", "for seq1, seq2 being Real_Sequence st seq1 is convergent & seq2 is convergent holds lim (seq1 (#) seq2) = (lim seq1) * (lim seq2)",
         "let seq1, seq2 be Real_Sequence; assume A1: seq1 is convergent; assume A2: seq2 is convergent; thus lim (seq1 (#) seq2) = (lim seq1) * (lim seq2) by A1, A2, SEQ_2:8;"),
        ("seq_subsequence_limit", "for seq being Real_Sequence, seq1 being subsequence of seq st seq is convergent holds seq1 is convergent & lim seq1 = lim seq",
         "let seq be Real_Sequence; let seq1 be subsequence of seq; assume A1: seq is convergent; thus seq1 is convergent by A1, SEQ_4:17; hence lim seq1 = lim seq by A1, SEQ_4:17;"),
        ("seq_series_convergent", "for seq being Real_Sequence st seq is summable holds Partial_Sums seq is convergent",
         "let seq be Real_Sequence; assume seq is summable; hence Partial_Sums seq is convergent by SERIES_1:def 2;"),
        ("seq_ratio_test", "for seq being Real_Sequence st (ex N being Nat st for n being Nat st n >= N holds |.seq.(n+1).| / |.seq.n.| < 1) holds seq is summable",
         "let seq be Real_Sequence; assume ex N being Nat st for n being Nat st n >= N holds |.seq.(n+1).| / |.seq.n.| < 1; hence seq is summable by SERIES_1:24;"),
        ("seq_comparison_test", "for seq1, seq2 being Real_Sequence st (for n being Nat holds |.seq1.n.| <= seq2.n) & seq2 is summable holds seq1 is summable",
         "let seq1, seq2 be Real_Sequence; assume A1: for n being Nat holds |.seq1.n.| <= seq2.n; assume A2: seq2 is summable; thus seq1 is summable by A1, A2, SERIES_1:20;"),
        ("seq_harmonic_divergent", "for seq being Real_Sequence st for n being Nat holds seq.n = 1 / (n + 1) holds not seq is summable",
         "let seq be Real_Sequence; assume A1: for n being Nat holds seq.n = 1 / (n + 1); set P = Partial_Sums seq; assume A2: seq is summable; then P is convergent by SERIES_1:def 2; consider M being Real such that A3: for n being Nat holds P.n <= M by RSSPACE:7; per cases; suppose M > 0; consider N being Nat such that A4: P.N > M by A1, SEQ_4:6; thus contradiction by A3, A4; end; suppose M <= 0; P.0 = seq.0 by SERIES_1:def 1 .= 1 / (0 + 1) by A1 .= 1; hence contradiction by A3; end;"),
    ]

    lattices = [
        ("lattice_join_comm", "for L being Lattice, a, b being Element of L holds a \"\\\/\" b = b \"\\\/\" a",
         "let L be Lattice; let a, b be Element of L; thus a \"\\\/\" b = b \"\\\/\" a by LATTICES:def 1;"),
        ("lattice_meet_comm", "for L being Lattice, a, b being Element of L holds a \"/\\\" b = b \"/\\\" a",
         "let L be Lattice; let a, b be Element of L; thus a \"/\\\" b = b \"/\\\" a by LATTICES:def 2;"),
        ("lattice_join_assoc", "for L being Lattice, a, b, c being Element of L holds a \"\\\/\" (b \"\\\/\" c) = (a \"\\\/\" b) \"\\\/\" c",
         "let L be Lattice; let a, b, c be Element of L; thus a \"\\\/\" (b \"\\\/\" c) = (a \"\\\/\" b) \"\\\/\" c by LATTICES:def 5;"),
        ("lattice_meet_assoc", "for L being Lattice, a, b, c being Element of L holds a \"/\\\" (b \"/\\\" c) = (a \"/\\\" b) \"/\\\" c",
         "let L be Lattice; let a, b, c be Element of L; thus a \"/\\\" (b \"/\\\" c) = (a \"/\\\" b) \"/\\\" c by LATTICES:def 7;"),
        ("lattice_absorption_join", "for L being Lattice, a, b being Element of L holds a \"\\\/\" (a \"/\\\" b) = a",
         "let L be Lattice; let a, b be Element of L; thus a \"\\\/\" (a \"/\\\" b) = a by LATTICES:def 8;"),
        ("lattice_absorption_meet", "for L being Lattice, a, b being Element of L holds a \"/\\\" (a \"\\\/\" b) = a",
         "let L be Lattice; let a, b be Element of L; thus a \"/\\\" (a \"\\\/\" b) = a by LATTICES:def 9;"),
        ("lattice_distributive", "for L being distributive Lattice, a, b, c being Element of L holds a \"/\\\" (b \"\\\/\" c) = (a \"/\\\" b) \"\\\/\" (a \"/\\\" c)",
         "let L be distributive Lattice; let a, b, c be Element of L; thus a \"/\\\" (b \"\\\/\" c) = (a \"/\\\" b) \"\\\/\" (a \"/\\\" c) by LATTICES:def 11;"),
        ("lattice_complemented", "for L being complemented bounded Lattice, a being Element of L ex b being Element of L st a \"\\\/\" b = Top L & a \"/\\\" b = Bottom L",
         "let L be complemented bounded Lattice; let a be Element of L; thus ex b being Element of L st a \"\\\/\" b = Top L & a \"/\\\" b = Bottom L by LATTICES:def 19;"),
        ("lattice_bounded", "for L being bounded Lattice, a being Element of L holds a \"\\\/\" (Bottom L) = a & a \"/\\\" (Top L) = a",
         "let L be bounded Lattice; let a be Element of L; thus a \"\\\/\" (Bottom L) = a by LATTICES:39; thus a \"/\\\" (Top L) = a by LATTICES:41;"),
        ("lattice_modular", "for L being modular Lattice, a, b, c being Element of L st a [= c holds a \"\\\/\" (b \"/\\\" c) = (a \"\\\/\" b) \"/\\\" c",
         "let L be modular Lattice; let a, b, c be Element of L; assume a [= c; hence a \"\\\/\" (b \"/\\\" c) = (a \"\\\/\" b) \"/\\\" c by LATTICES:def 12;"),
    ]

    metric_spaces = [
        ("metric_dist_nonneg", "for M being MetrSpace, p, q being Point of M holds dist(p, q) >= 0",
         "let M be MetrSpace; let p, q be Point of M; thus dist(p, q) >= 0 by METRIC_1:5;"),
        ("metric_dist_sym", "for M being MetrSpace, p, q being Point of M holds dist(p, q) = dist(q, p)",
         "let M be MetrSpace; let p, q be Point of M; thus dist(p, q) = dist(q, p) by METRIC_1:def 1;"),
        ("metric_triangle_ineq", "for M being MetrSpace, p, q, r being Point of M holds dist(p, r) <= dist(p, q) + dist(q, r)",
         "let M be MetrSpace; let p, q, r be Point of M; thus dist(p, r) <= dist(p, q) + dist(q, r) by METRIC_1:4;"),
        ("metric_dist_zero", "for M being MetrSpace, p, q being Point of M holds dist(p, q) = 0 iff p = q",
         "let M be MetrSpace; let p, q be Point of M; thus dist(p, q) = 0 iff p = q by METRIC_1:2, METRIC_1:1;"),
        ("metric_open_ball_open", "for M being MetrSpace, p being Point of M, r being positive Real holds Ball(p, r) is open Subset of TopSpaceMetr M",
         "let M be MetrSpace; let p be Point of M; let r be positive Real; thus Ball(p, r) is open Subset of TopSpaceMetr M by TBSP_1:16;"),
        ("metric_cauchy_convergent", "for M being MetrSpace, seq being sequence of M st M is complete & seq is Cauchy holds seq is convergent",
         "let M be MetrSpace; let seq be sequence of M; assume A1: M is complete; assume A2: seq is Cauchy; thus seq is convergent by A1, A2, TBSP_1:def 6;"),
        ("metric_complete_closed", "for M being MetrSpace, A being Subset of M st M is complete & A is closed holds A is complete",
         "let M be MetrSpace; let A be Subset of M; assume A1: M is complete; assume A2: A is closed; let seq be sequence of M such that A3: rng seq c= A and A4: seq is Cauchy; seq is convergent by A1, A4, TBSP_1:def 6; consider p being Point of M such that A5: seq is_convergent_in_metrspace_to p by TBSP_1:def 4; p in A by A2, A3, A5, TBSP_1:8; hence thesis;"),
        ("metric_compact_sequentially", "for M being MetrSpace, A being Subset of M st A is compact holds for seq being sequence of M st rng seq c= A ex seq1 being subsequence of seq st seq1 is convergent",
         "let M be MetrSpace; let A be Subset of M; assume A1: A is compact; let seq be sequence of M; assume rng seq c= A; thus ex seq1 being subsequence of seq st seq1 is convergent by A1, TBSP_1:def 9;"),
        ("metric_lipschitz_continuous", "for M1, M2 being MetrSpace, f being Function of M1, M2, L being positive Real st for p, q being Point of M1 holds dist(f.p, f.q) <= L * dist(p, q) holds f is continuous",
         "let M1, M2 be MetrSpace; let f be Function of M1, M2; let L be positive Real; assume A1: for p, q being Point of M1 holds dist(f.p, f.q) <= L * dist(p, q); let p be Point of M1; let e be Real; assume A2: e > 0; set d = e / L; take d; thus d > 0 by A2; let q be Point of M1; assume dist(p, q) < d; dist(f.p, f.q) <= L * dist(p, q) by A1; hence dist(f.p, f.q) < e by XREAL_1:68;"),
        ("metric_equiv_open_sets", "for M1, M2 being MetrSpace st the TopStruct of TopSpaceMetr M1 = the TopStruct of TopSpaceMetr M2 holds for A being Subset of M1 holds A is open Subset of TopSpaceMetr M1 iff A is open Subset of TopSpaceMetr M2",
         "let M1, M2 be MetrSpace; assume A1: the TopStruct of TopSpaceMetr M1 = the TopStruct of TopSpaceMetr M2; let A be Subset of M1; thus A is open Subset of TopSpaceMetr M1 iff A is open Subset of TopSpaceMetr M2 by A1, PRE_TOPC:def 2;"),
    ]

    finite_sequences = [
        ("finseq_empty", "for D being non empty set holds <*>D is FinSequence of D & len (<*>D) = 0",
         "let D be non empty set; thus <*>D is FinSequence of D; thus len (<*>D) = 0 by FINSEQ_1:def 3;"),
        ("finseq_concat_len", "for f, g being FinSequence holds len (f ^ g) = len f + len g",
         "let f, g be FinSequence; thus len (f ^ g) = len f + len g by FINSEQ_1:22;"),
        ("finseq_concat_assoc", "for f, g, h being FinSequence holds (f ^ g) ^ h = f ^ (g ^ h)",
         "let f, g, h be FinSequence; thus (f ^ g) ^ h = f ^ (g ^ h) by FINSEQ_1:32;"),
        ("finseq_rev_rev", "for f being FinSequence holds Rev (Rev f) = f",
         "let f be FinSequence; thus Rev (Rev f) = f by FINSEQ_1:48;"),
        ("finseq_rev_len", "for f being FinSequence holds len (Rev f) = len f",
         "let f be FinSequence; thus len (Rev f) = len f by FINSEQ_1:46;"),
        ("finseq_singleton", "for x being object holds <*x*> is FinSequence & len <*x*> = 1",
         "let x be object; thus <*x*> is FinSequence; thus len <*x*> = 1 by FINSEQ_1:39;"),
        ("finseq_dom_range", "for f being FinSequence holds dom f = Seg len f",
         "let f be FinSequence; thus dom f = Seg len f by FINSEQ_1:def 3;"),
        ("finseq_rng_subset", "for D being set, f being FinSequence of D holds rng f c= D",
         "let D be set; let f be FinSequence of D; thus rng f c= D by FINSEQ_1:def 4;"),
        ("finseq_perm_len", "for f, g being FinSequence st g is Permutation of f holds len g = len f",
         "let f, g be FinSequence; assume g is Permutation of f; hence len g = len f by FINSEQ_2:32;"),
        ("finseq_concat_empty", "for f being FinSequence holds f ^ (<*> the carrier of REAL) = f",
         "let f be FinSequence; thus f ^ (<*> the carrier of REAL) = f by FINSEQ_1:34;"),
    ]

    ordinals = [
        ("ordinal_lt_irrefl", "for A being Ordinal holds not A in A",
         "let A be Ordinal; thus not A in A by ORDINAL1:5;"),
        ("ordinal_lt_trans", "for A, B, C being Ordinal st A in B & B in C holds A in C",
         "let A, B, C be Ordinal; assume A1: A in B; assume A2: B in C; thus A in C by A1, A2, ORDINAL1:10;"),
        ("ordinal_trichotomy", "for A, B being Ordinal holds A in B or A = B or B in A",
         "let A, B be Ordinal; thus A in B or A = B or B in A by ORDINAL1:16;"),
        ("ordinal_succ_gt", "for A being Ordinal holds A in succ A",
         "let A be Ordinal; thus A in succ A by ORDINAL1:6;"),
        ("ordinal_succ_ordinal", "for A being Ordinal holds succ A is Ordinal",
         "let A be Ordinal; thus succ A is Ordinal by ORDINAL1:def 4;"),
        ("ordinal_limit_not_succ", "for A being Ordinal st A is limit_ordinal & A <> {} holds not ex B being Ordinal st A = succ B",
         "let A be Ordinal; assume A1: A is limit_ordinal; assume A2: A <> {}; assume ex B being Ordinal st A = succ B; then consider B being Ordinal such that A3: A = succ B; thus contradiction by A1, A3, ORDINAL1:def 5;"),
        ("ordinal_transfinite_ind", "for P being Ordinal-defined Function st (for A being Ordinal st (for B being Ordinal st B in A holds P.B is true) holds P.A is true) holds for A being Ordinal holds P.A is true",
         "let P be Ordinal-defined Function; assume A1: for A being Ordinal st (for B being Ordinal st B in A holds P.B is true) holds P.A is true; defpred Q[Ordinal] means P.\$1 is true; A2: for A being Ordinal st (for B being Ordinal st B in A holds Q[B]) holds Q[A] by A1; thus for A being Ordinal holds Q[A] from ORDINAL1:sch 3(A2);"),
        ("ordinal_add_zero", "for A being Ordinal holds A + {} = A",
         "let A be Ordinal; thus A + {} = A by ORDINAL2:27;"),
        ("ordinal_add_succ", "for A, B being Ordinal holds A + succ B = succ (A + B)",
         "let A, B be Ordinal; thus A + succ B = succ (A + B) by ORDINAL2:28;"),
        ("ordinal_mul_zero", "for A being Ordinal holds A *^ {} = {}",
         "let A be Ordinal; thus A *^ {} = {} by ORDINAL2:35;"),
    ]

    measure_theory = [
        ("measure_sigma_algebra_empty", "for S being SigmaField of X holds {} in S",
         "let S be SigmaField of X; thus {} in S by PROB_1:4;"),
        ("measure_sigma_algebra_compl", "for S being SigmaField of X, A being set st A in S holds X \\ A in S",
         "let S be SigmaField of X; let A be set; assume A in S; hence X \\ A in S by PROB_1:def 1;"),
        ("measure_sigma_algebra_union", "for S being SigmaField of X, A being SetSequence of X st (for n being Nat holds A.n in S) holds union rng A in S",
         "let S be SigmaField of X; let A be SetSequence of X; assume for n being Nat holds A.n in S; hence union rng A in S by PROB_1:def 1;"),
        ("measure_nonneg", "for S being SigmaField of X, M being Measure of S, A being set st A in S holds M.A >= 0",
         "let S be SigmaField of X; let M be Measure of S; let A be set; assume A in S; thus M.A >= 0 by SUPINF_2:42, MEASURE1:def 2;"),
        ("measure_empty_zero", "for S being SigmaField of X, M being Measure of S holds M.{} = 0",
         "let S be SigmaField of X; let M be Measure of S; thus M.{} = 0 by MEASURE1:def 2;"),
        ("measure_countable_additivity", "for S being SigmaField of X, M being Measure of S, A being SetSequence of X st A is mutually-disjoint & (for n being Nat holds A.n in S) holds M.(union rng A) = SUM(M * A)",
         "let S be SigmaField of X; let M be Measure of S; let A be SetSequence of X; assume A1: A is mutually-disjoint; assume A2: for n being Nat holds A.n in S; thus M.(union rng A) = SUM(M * A) by A1, A2, MEASURE1:def 2;"),
        ("measure_monotone", "for S being SigmaField of X, M being Measure of S, A, B being set st A in S & B in S & A c= B holds M.A <= M.B",
         "let S be SigmaField of X; let M be Measure of S; let A, B be set; assume A1: A in S; assume A2: B in S; assume A3: A c= B; reconsider C = B \\ A as Element of S by A1, A2, PROB_1:def 1; M.B = M.A + M.C by A1, A3, MEASURE1:22; hence M.A <= M.B by SUPINF_2:42, MEASURE1:def 2;"),
        ("measure_subadditivity", "for S being SigmaField of X, M being Measure of S, A being SetSequence of X st (for n being Nat holds A.n in S) holds M.(union rng A) <= SUM(M * A)",
         "let S be SigmaField of X; let M be Measure of S; let A be SetSequence of X; assume for n being Nat holds A.n in S; hence M.(union rng A) <= SUM(M * A) by MEASURE1:31;"),
        ("measurable_function_preimage", "for S being SigmaField of X, f being Function of X, REAL, a being Real st f is S-measurable holds f\"(].a, +infty.[) in S",
         "let S be SigmaField of X; let f be Function of X, REAL; let a be Real; assume f is S-measurable; hence f\"(].a, +infty.[) in S by MEASURE1:def 7;"),
        ("measure_continuity_below", "for S being SigmaField of X, M being Measure of S, A being SetSequence of X st (for n being Nat holds A.n in S) & A is non-descending holds M.(union rng A) = lim (M * A)",
         "let S be SigmaField of X; let M be Measure of S; let A be SetSequence of X; assume A1: for n being Nat holds A.n in S; assume A2: A is non-descending; thus M.(union rng A) = lim (M * A) by A1, A2, MEASURE1:32;"),
    ]

    all_categories = [
        ("set_theory", set_theory),
        ("natural_numbers", natural_numbers),
        ("real_numbers", real_numbers),
        ("functions", functions),
        ("topology", topology),
        ("algebra", algebra),
        ("sequences", sequences),
        ("lattices", lattices),
        ("metric_spaces", metric_spaces),
        ("finite_sequences", finite_sequences),
        ("ordinals", ordinals),
        ("measure_theory", measure_theory),
    ]

    proofs = Dict{String,Any}[]
    for (category, theorems) in all_categories
        for (name, goal, proof_body) in theorems
            steps = [lowercase(k.match) for k in eachmatch(
                r"\b(assume|let|take|consider|thus|hence|suppose|per cases|set|reconsider|hereby|defpred)\b"i,
                proof_body
            )]
            seen = Set{String}(); unique_steps = String[]
            for s in steps
                s ∉ seen && (push!(seen, s); push!(unique_steps, s))
                length(unique_steps) >= 20 && break
            end
            push!(proofs, Dict{String,Any}(
                "theorem" => name,
                "goal" => "theorem $(name): $(goal)",
                "tactic_proof" => "proof $(proof_body) end;",
                "tactics" => unique_steps,
                "source" => "mizar_synthetic/$(category)",
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

    # Phase 1 strategy (2026-04-18, echidna#14): prefer a full MML
    # clone (MizarSystem/MML on GitHub, ~ 1 150 .miz files under
    # `mml/`) over the legacy hand-picked downloader list. If the full
    # clone isn't present, fall back to the narrow downloader so the
    # extractor still does something.
    mml_subdir = joinpath(EXTERNAL_DIR, "mml")
    if isdir(mml_subdir)
        println("[Mizar] Phase 1: Walking full MML clone at $(mml_subdir) ...")
    else
        println("[Mizar] Phase 1: No MML clone found — falling back to curated downloader ...")
        downloaded = download_mizar_files()
        println("  Downloaded/cached $(downloaded) files")
    end

    miz_files = String[]
    for (root, _dirs, files) in walkdir(EXTERNAL_DIR)
        for fname in files
            endswith(fname, ".miz") && push!(miz_files, joinpath(root, fname))
        end
    end
    println("  Found $(length(miz_files)) .miz files under $(EXTERNAL_DIR)")

    processed = 0
    for fpath in miz_files
        parsed = parse_mizar_file(fpath)
        append!(all_entries, parsed)
        processed += 1
        if processed % 200 == 0
            println("  processed $(processed)/$(length(miz_files)) files — running theorem count: $(length(all_entries))")
        end
    end
    extracted_count = length(all_entries)

    println("[Mizar] Phase 2: Generating synthetic proofs ...")
    synthetic = generate_synthetic_mizar()
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
            "prover" => "Mizar",
            "theorem" => entry["theorem"],
            "goal" => entry["goal"],
            "context" => get(entry, "tactics", String[]),
            "tactic_proof" => get(entry, "tactic_proof", ""),
            "source" => get(entry, "source", "mizar"),
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
        "prover" => "Mizar",
        "total_proofs" => length(output_records),
        "extracted_from_source" => extracted_count,
        "synthetic_added" => length(output_records) - extracted_count,
        "id_range" => [START_ID, current_id - 1],
        "output_file" => OUTPUT_FILE,
    )
    open(STATS_FILE, "w") do fh
        JSON3.pretty(fh, stats)
    end

    println("\n[Mizar] COMPLETE: $(length(output_records)) proofs written to $(OUTPUT_FILE)")
    println("  Extracted from source: $(extracted_count)")
    println("  Synthetic: $(length(output_records) - extracted_count)")
    return (extracted_count, length(output_records) - extracted_count)
end

if abspath(PROGRAM_FILE) == abspath(@__FILE__)
    run()
end
