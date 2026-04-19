#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
#
# Extract proofs from F* (Project Everest) and convert to ECHIDNA training format.
#
# Attempts to download from the F* GitHub repository (examples/ dir). Falls back
# to generating high-quality synthetic F* proofs.
#
# F* is a general-purpose ML-like functional programming language with effects
# aimed at program verification. It is used in Project Everest for verified
# cryptographic libraries (HACL*, EverCrypt, miTLS).
#
# Output: training_data/proof_states_fstar.jsonl
# ID range: 97000+

using JSON3
using Downloads

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

const REPO_ROOT = dirname(dirname(abspath(@__FILE__)))
const EXTERNAL_DIR = joinpath(REPO_ROOT, "external_corpora", "fstar")
const OUTPUT_DIR = joinpath(REPO_ROOT, "training_data")
const OUTPUT_FILE = joinpath(OUTPUT_DIR, "proof_states_fstar.jsonl")
const STATS_FILE = joinpath(OUTPUT_DIR, "stats_fstar.json")
const START_ID = 97000

const FSTAR_RAW = "https://raw.githubusercontent.com/FStarLang/FStar/master"
const FSTAR_FILES = [
    "examples/algorithms/BinarySearch.fst",
    "examples/algorithms/InsertionSort.fst",
    "examples/algorithms/QuickSort.fst",
    "examples/algorithms/MergeSort.fst",
    "examples/data_structures/BinomialQueue.fst",
    "examples/data_structures/RBTree.fst",
    "examples/crypto/Hacl.fst",
    "examples/micro-benchmarks/Arith.fst",
    "examples/micro-benchmarks/Nat.fst",
    "examples/termination/Ackermann.fst",
    "examples/termination/Fibonacci.fst",
    "ulib/FStar.List.Tot.fst",
    "ulib/FStar.Seq.Base.fst",
    "ulib/FStar.Math.Lemmas.fst",
]

"""
    parse_fstar_file(filepath::String) -> Vector{Dict{String,Any}}

Parse an F* .fst file and extract val/let definitions with specs.
"""
function parse_fstar_file(filepath::String)::Vector{Dict{String,Any}}
    results = Dict{String,Any}[]
    local content::String
    try
        content = read(filepath, String)
    catch
        return results
    end

    # val declarations with refinement types
    val_pattern = r"val\s+(\w+)\s*:\s*(.*?)(?=\nval\s|\nlet\s|\ntype\s|\nopen\s|\nmodule\s|\z)"s
    for m in eachmatch(Regex(val_pattern, "s"), content)
        name = strip(m.captures[1])
        sig = replace(strip(m.captures[2]), r"\s+" => " ")
        sig = sig[1:min(400, length(sig))]
        if isempty(sig) || length(sig) < 5
            continue
        end
        keywords = [m_.match for m_ in eachmatch(r"\b(Tot|Lemma|Pure|ST|Stack|GTot|requires|ensures|decreases|modifies)\b", sig)]
        push!(results, Dict{String,Any}(
            "theorem" => name,
            "goal" => sig,
            "tactics" => unique(keywords)[1:min(20, length(unique(keywords)))],
            "source" => "fstar/$(basename(filepath))",
        ))
    end

    # let with refinement types or Lemma
    let_pattern = r"let\s+(?:rec\s+)?(\w+)\s*(?::.*?)?\s*=\s*(.*?)(?=\nlet\s|\nval\s|\ntype\s|\z)"s
    for m in eachmatch(Regex(let_pattern, "s"), content)
        name = strip(m.captures[1])
        body = replace(strip(m.captures[2]), r"\s+" => " ")
        body = body[1:min(300, length(body))]
        if occursin("Lemma", body) || occursin("assert", body) || occursin("calc", body)
            keywords = [m_.match for m_ in eachmatch(r"\b(Lemma|assert|calc|assume|admit|Classical)\b", body)]
            push!(results, Dict{String,Any}(
                "theorem" => "$(name)_impl",
                "goal" => body[1:min(200, length(body))],
                "tactics" => unique(keywords)[1:min(20, length(unique(keywords)))],
                "source" => "fstar/$(basename(filepath))",
            ))
        end
    end

    return results
end

"""
    download_fstar_files() -> Int

Attempt to download F* source files.
"""
function download_fstar_files()::Int
    downloaded = 0
    for rel_path in FSTAR_FILES
        url = "$FSTAR_RAW/$rel_path"
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
    generate_synthetic_fstar() -> Vector{Dict{String,Any}}

Generate high-quality synthetic F* proofs.
"""
function generate_synthetic_fstar()::Vector{Dict{String,Any}}
    arithmetic = [
        ("add_comm", "val add_comm: a:int -> b:int -> Lemma (a + b == b + a)", "let add_comm a b = ()"),
        ("add_assoc", "val add_assoc: a:int -> b:int -> c:int -> Lemma ((a + b) + c == a + (b + c))", "let add_assoc a b c = ()"),
        ("mul_comm", "val mul_comm: a:int -> b:int -> Lemma (a * b == b * a)", "let mul_comm a b = ()"),
        ("mul_assoc", "val mul_assoc: a:int -> b:int -> c:int -> Lemma ((a * b) * c == a * (b * c))", "let mul_assoc a b c = ()"),
        ("distributive", "val distributive: a:int -> b:int -> c:int -> Lemma (a * (b + c) == a * b + a * c)", "let distributive a b c = ()"),
        ("add_zero_r", "val add_zero_r: a:int -> Lemma (a + 0 == a)", "let add_zero_r a = ()"),
        ("mul_one_r", "val mul_one_r: a:int -> Lemma (a * 1 == a)", "let mul_one_r a = ()"),
        ("mul_zero_r", "val mul_zero_r: a:int -> Lemma (a * 0 == 0)", "let mul_zero_r a = ()"),
        ("pow_add", "val pow_add: b:nat -> m:nat -> n:nat -> Lemma (ensures pow b (m + n) == pow b m * pow b n) (decreases m)", "let rec pow_add b m n = if m = 0 then () else pow_add b (m - 1) n"),
        ("pow_mul", "val pow_mul: b:nat -> m:nat -> n:nat -> Lemma (ensures pow b (m * n) == pow (pow b m) n) (decreases n)", "let rec pow_mul b m n = if n = 0 then () else (pow_add b m (m * (n - 1)); pow_mul b m (n - 1))"),
        ("mod_add", "val mod_add: a:int -> b:int -> n:pos -> Lemma ((a + b) % n == ((a % n) + (b % n)) % n)", "let mod_add a b n = FStar.Math.Lemmas.lemma_mod_plus_distr_l a b n"),
        ("div_exact", "val div_exact: a:nat -> b:pos -> Lemma (requires a % b == 0) (ensures a / b * b == a)", "let div_exact a b = FStar.Math.Lemmas.lemma_div_exact a b"),
    ]

    lists = [
        ("append_nil", "val append_nil: #a:Type -> l:list a -> Lemma (l @ [] == l)", "let rec append_nil #a l = match l with | [] -> () | _::tl -> append_nil tl"),
        ("append_assoc", "val append_assoc: #a:Type -> l1:list a -> l2:list a -> l3:list a -> Lemma ((l1 @ l2) @ l3 == l1 @ (l2 @ l3))", "let rec append_assoc #a l1 l2 l3 = match l1 with | [] -> () | _::tl -> append_assoc tl l2 l3"),
        ("length_append", "val length_append: #a:Type -> l1:list a -> l2:list a -> Lemma (length (l1 @ l2) == length l1 + length l2)", "let rec length_append #a l1 l2 = match l1 with | [] -> () | _::tl -> length_append tl l2"),
        ("rev_rev", "val rev_rev: #a:Type -> l:list a -> Lemma (rev (rev l) == l)", "let rec rev_rev #a l = match l with | [] -> () | hd::tl -> rev_append_rev tl [hd]; rev_rev tl"),
        ("map_append", "val map_append: #a:Type -> #b:Type -> f:(a -> b) -> l1:list a -> l2:list a -> Lemma (map f (l1 @ l2) == map f l1 @ map f l2)", "let rec map_append #a #b f l1 l2 = match l1 with | [] -> () | _::tl -> map_append f tl l2"),
        ("length_map", "val length_map: #a:Type -> #b:Type -> f:(a -> b) -> l:list a -> Lemma (length (map f l) == length l)", "let rec length_map #a #b f l = match l with | [] -> () | _::tl -> length_map f tl"),
        ("mem_append", "val mem_append: #a:eqtype -> x:a -> l1:list a -> l2:list a -> Lemma (mem x (l1 @ l2) <==> mem x l1 || mem x l2)", "let rec mem_append #a x l1 l2 = match l1 with | [] -> () | _::tl -> mem_append x tl l2"),
        ("filter_append", "val filter_append: #a:Type -> f:(a -> bool) -> l1:list a -> l2:list a -> Lemma (filter f (l1 @ l2) == filter f l1 @ filter f l2)", "let rec filter_append #a f l1 l2 = match l1 with | [] -> () | hd::tl -> filter_append f tl l2"),
        ("fold_left_append", "val fold_left_append: #a:Type -> #b:Type -> f:(b -> a -> b) -> init:b -> l1:list a -> l2:list a -> Lemma (fold_left f init (l1 @ l2) == fold_left f (fold_left f init l1) l2)", "let rec fold_left_append #a #b f init l1 l2 = match l1 with | [] -> () | hd::tl -> fold_left_append f (f init hd) tl l2"),
        ("for_all_append", "val for_all_append: #a:Type -> f:(a -> bool) -> l1:list a -> l2:list a -> Lemma (for_all f (l1 @ l2) <==> for_all f l1 && for_all f l2)", "let rec for_all_append #a f l1 l2 = match l1 with | [] -> () | _::tl -> for_all_append f tl l2"),
    ]

    crypto_verification = [
        ("aead_encrypt_decrypt", "val aead_encrypt_decrypt: k:key -> n:nonce -> p:plaintext -> ad:aad -> Lemma (ensures (let c = aead_encrypt k n p ad in aead_decrypt k n c ad == Some p))", ""),
        ("hmac_verify", "val hmac_verify: k:key -> m:msg -> t:tag -> Lemma (requires t == hmac k m) (ensures verify_hmac k m t == true)", ""),
        ("hash_collision_resistance", "val hash_collision_resistance: m1:msg -> m2:msg -> Lemma (requires m1 <> m2) (ensures hash m1 <> hash m2) [SMTPat (hash m1); SMTPat (hash m2)]", ""),
        ("kdf_extract_length", "val kdf_extract_length: salt:bytes -> ikm:bytes -> Lemma (ensures length (kdf_extract salt ikm) == hash_length)", ""),
        ("chacha20_involutive", "val chacha20_involutive: k:key -> n:nonce -> ctr:nat -> p:bytes -> Lemma (ensures chacha20 k n ctr (chacha20 k n ctr p) == p)", ""),
    ]

    effects_and_state = [
        ("incr_spec", "val incr: r:ref int -> ST unit (requires fun h -> True) (ensures fun h0 _ h1 -> sel h1 r == sel h0 r + 1)", "let incr r = r := !r + 1"),
        ("swap_spec", "val swap: r1:ref int -> r2:ref int -> ST unit (requires fun h -> True) (ensures fun h0 _ h1 -> sel h1 r1 == sel h0 r2 /\\ sel h1 r2 == sel h0 r1)", "let swap r1 r2 = let t = !r1 in r1 := !r2; r2 := t"),
        ("factorial_spec", "val factorial: n:nat -> Tot (r:nat{r >= 1})", "let rec factorial n = if n = 0 then 1 else n * factorial (n - 1)"),
        ("fibonacci_spec", "val fibonacci: n:nat -> Tot nat (decreases n)", "let rec fibonacci n = if n <= 1 then n else fibonacci (n - 1) + fibonacci (n - 2)"),
        ("alloc_and_free", "val alloc_and_free: n:nat -> ST unit (requires fun h -> True) (ensures fun h0 _ h1 -> modifies Set.empty h0 h1)", "let alloc_and_free n = let r = alloc n in free r"),
    ]

    refinement_types = [
        ("nat_positive", "val nat_positive: n:nat{n > 0} -> Tot (r:nat{r >= 0})", "let nat_positive n = n - 1"),
        ("bounded_add", "val bounded_add: a:nat{a < 100} -> b:nat{b < 100} -> Tot (r:nat{r < 200})", "let bounded_add a b = a + b"),
        ("safe_div", "val safe_div: a:int -> b:int{b <> 0} -> Tot int", "let safe_div a b = a / b"),
        ("vector_index", "val vector_index: #n:nat -> v:vector n -> i:nat{i < n} -> Tot elem", "let vector_index #n v i = Seq.index v i"),
        ("sorted_insert", "val sorted_insert: x:int -> l:list int{sorted l} -> Tot (r:list int{sorted r /\\ length r == length l + 1})", ""),
        ("non_empty_head", "val non_empty_head: #a:Type -> l:list a{Cons? l} -> Tot a", "let non_empty_head #a l = match l with | hd::_ -> hd"),
        ("matrix_mult_dims", "val matrix_mult: #m:nat -> #n:nat -> #p:nat -> matrix m n -> matrix n p -> Tot (matrix m p)", ""),
        ("well_typed_eval", "val well_typed_eval: #t:typ -> e:exp{has_type e t} -> Tot (v:value{value_type v t})", ""),
    ]

    termination = [
        ("ackermann", "val ackermann: m:nat -> n:nat -> Tot nat (decreases %[m; n])", "let rec ackermann m n = if m = 0 then n + 1 else if n = 0 then ackermann (m - 1) 1 else ackermann (m - 1) (ackermann m (n - 1))"),
        ("gcd_termination", "val gcd: a:nat -> b:nat{a > 0 || b > 0} -> Tot (r:pos) (decreases b)", "let rec gcd a b = if b = 0 then a else gcd b (a % b)"),
        ("collatz_steps", "val collatz_steps: n:pos -> Tot nat (decreases %[n; if n = 1 then 0 else 1])", ""),
        ("mutual_even", "val mutual_even: n:nat -> Tot bool (decreases n)\nval mutual_odd: n:nat -> Tot bool (decreases n)", "let rec mutual_even n = if n = 0 then true else mutual_odd (n - 1)\nand mutual_odd n = if n = 0 then false else mutual_even (n - 1)"),
    ]

    sequences = [
        ("seq_append_length", "val seq_append_length: #a:Type -> s1:Seq.seq a -> s2:Seq.seq a -> Lemma (Seq.length (Seq.append s1 s2) == Seq.length s1 + Seq.length s2)", "let seq_append_length #a s1 s2 = Seq.lemma_len_append s1 s2"),
        ("seq_slice_slice", "val seq_slice_slice: #a:Type -> s:Seq.seq a -> i:nat -> j:nat{i <= j} -> k:nat -> l:nat{k <= l /\\ l <= j - i} -> Lemma (Seq.slice (Seq.slice s i j) k l == Seq.slice s (i + k) (i + l))", "let seq_slice_slice #a s i j k l = Seq.lemma_slice_slice s i j k l"),
        ("seq_create_index", "val seq_create_index: #a:Type -> n:nat -> v:a -> i:nat{i < n} -> Lemma (Seq.index (Seq.create n v) i == v)", "let seq_create_index #a n v i = ()"),
        ("seq_upd_index", "val seq_upd_index: #a:Type -> s:Seq.seq a -> i:nat{i < Seq.length s} -> v:a -> j:nat{j < Seq.length s} -> Lemma (Seq.index (Seq.upd s i v) j == (if i = j then v else Seq.index s j))", "let seq_upd_index #a s i v j = ()"),
        ("seq_equal_intro", "val seq_equal_intro: #a:Type -> s1:Seq.seq a -> s2:Seq.seq a -> Lemma (requires Seq.length s1 == Seq.length s2 /\\ (forall (i:nat{i < Seq.length s1}). Seq.index s1 i == Seq.index s2 i)) (ensures Seq.equal s1 s2)", "let seq_equal_intro #a s1 s2 = Seq.lemma_eq_intro s1 s2"),
        ("seq_mem_append", "val seq_mem_append: #a:eqtype -> x:a -> s1:Seq.seq a -> s2:Seq.seq a -> Lemma (Seq.mem x (Seq.append s1 s2) <==> Seq.mem x s1 || Seq.mem x s2)", "let seq_mem_append #a x s1 s2 = Seq.lemma_mem_append s1 s2"),
        ("seq_count_append", "val seq_count_append: #a:eqtype -> x:a -> s1:Seq.seq a -> s2:Seq.seq a -> Lemma (Seq.count x (Seq.append s1 s2) == Seq.count x s1 + Seq.count x s2)", "let seq_count_append #a x s1 s2 = Seq.lemma_count_append x s1 s2"),
        ("seq_sort_permutation", "val seq_sort_permutation: #a:eqtype -> f:(a -> a -> Tot int) -> s:Seq.seq a -> Lemma (ensures Seq.permutation a (Seq.sortWith f s) s)", "let seq_sort_permutation #a f s = Seq.lemma_sortWith_permutation f s"),
        ("seq_unsnoc", "val seq_unsnoc: #a:Type -> s:Seq.seq a{Seq.length s > 0} -> Tot (Seq.seq a & a)", "let seq_unsnoc #a s = Seq.un_snoc s"),
        ("seq_cons_head_tail", "val seq_cons_head_tail: #a:Type -> s:Seq.seq a{Seq.length s > 0} -> Lemma (Seq.cons (Seq.head s) (Seq.tail s) == s)", "let seq_cons_head_tail #a s = Seq.lemma_cons_head_tail s"),
        ("seq_map_seq", "val seq_map_seq: #a:Type -> #b:Type -> f:(a -> Tot b) -> s:Seq.seq a -> i:nat{i < Seq.length s} -> Lemma (Seq.index (Seq.map_seq f s) i == f (Seq.index s i))", "let seq_map_seq #a #b f s i = Seq.map_seq_index f s i"),
        ("seq_init_index", "val seq_init_index: #a:Type -> n:nat -> f:(i:nat{i < n} -> Tot a) -> i:nat{i < n} -> Lemma (Seq.index (Seq.init n f) i == f i)", "let seq_init_index #a n f i = Seq.init_index n f i"),
    ]

    buffers = [
        ("buffer_live", "val buffer_live: #a:Type -> h:HS.mem -> b:B.buffer a -> Lemma (requires B.live h b) (ensures B.length b >= 0 /\\ B.live h b)", "let buffer_live #a h b = ()"),
        ("buffer_read_write", "val buffer_read_write: #a:Type -> b:B.buffer a -> i:UInt32.t{UInt32.v i < B.length b} -> v:a -> h0:HS.mem -> Lemma (requires B.live h0 b) (ensures (let h1 = B.g_upd b (UInt32.v i) v h0 in B.get h1 b (UInt32.v i) == v))", "let buffer_read_write #a b i v h0 = ()"),
        ("buffer_modifies_only", "val buffer_modifies_only: #a:Type -> b:B.buffer a -> h0:HS.mem -> h1:HS.mem -> Lemma (requires B.modifies (B.loc_buffer b) h0 h1) (ensures B.modifies (B.loc_buffer b) h0 h1)", "let buffer_modifies_only #a b h0 h1 = ()"),
        ("buffer_disjoint", "val buffer_disjoint: #a:Type -> #b:Type -> b1:B.buffer a -> b2:B.buffer b -> h0:HS.mem -> h1:HS.mem -> v:a -> Lemma (requires B.live h0 b1 /\\ B.live h0 b2 /\\ B.disjoint b1 b2 /\\ B.modifies (B.loc_buffer b1) h0 h1) (ensures B.as_seq h1 b2 == B.as_seq h0 b2)", "let buffer_disjoint #a #b b1 b2 h0 h1 v = B.modifies_buffer_elim b2 (B.loc_buffer b1) h0 h1"),
        ("buffer_as_seq_gsub", "val buffer_as_seq_gsub: #a:Type -> b:B.buffer a -> i:UInt32.t -> len:UInt32.t{UInt32.v i + UInt32.v len <= B.length b} -> h:HS.mem -> Lemma (requires B.live h b) (ensures B.as_seq h (B.gsub b i len) == Seq.slice (B.as_seq h b) (UInt32.v i) (UInt32.v i + UInt32.v len))", "let buffer_as_seq_gsub #a b i len h = ()"),
        ("buffer_concat", "val buffer_concat: #a:Type -> b1:B.buffer a -> b2:B.buffer a -> h:HS.mem -> Lemma (requires B.live h b1 /\\ B.live h b2 /\\ B.disjoint b1 b2) (ensures B.length b1 + B.length b2 >= 0)", "let buffer_concat #a b1 b2 h = ()"),
        ("stack_alloc_free", "val stack_alloc_free: unit -> ST unit (requires fun h -> True) (ensures fun h0 _ h1 -> modifies Set.empty h0 h1)", "let stack_alloc_free () = push_frame (); let b = B.alloca 0uy 16ul in let _ = b.(0ul) in pop_frame ()"),
        ("buffer_frame", "val buffer_frame: #a:Type -> #b:Type -> buf:B.buffer a -> other:B.buffer b -> h0:HS.mem -> h1:HS.mem -> Lemma (requires B.live h0 buf /\\ B.live h0 other /\\ B.disjoint buf other /\\ B.modifies (B.loc_buffer other) h0 h1) (ensures B.as_seq h0 buf == B.as_seq h1 buf /\\ B.live h1 buf)", "let buffer_frame #a #b buf other h0 h1 = B.modifies_buffer_elim buf (B.loc_buffer other) h0 h1"),
        ("buffer_loc_disjoint", "val buffer_loc_disjoint: #a:Type -> #b:Type -> b1:B.buffer a -> b2:B.buffer b -> Lemma (requires B.disjoint b1 b2) (ensures B.loc_disjoint (B.loc_buffer b1) (B.loc_buffer b2))", "let buffer_loc_disjoint #a #b b1 b2 = B.loc_disjoint_buffer b1 b2"),
        ("buffer_length_gsub", "val buffer_length_gsub: #a:Type -> b:B.buffer a -> i:UInt32.t -> len:UInt32.t{UInt32.v i + UInt32.v len <= B.length b} -> Lemma (B.length (B.gsub b i len) == UInt32.v len)", "let buffer_length_gsub #a b i len = ()"),
    ]

    monotonic_state = [
        ("witnessed_stable", "val witnessed_stable: #a:Type -> #rel:Preorder.preorder a -> r:mref a rel -> p:(a -> Type0){stable p rel} -> h:HS.mem -> Lemma (requires p (HS.sel h r)) (ensures witnessed r p)", "let witnessed_stable #a #rel r p h = gst_witness r p"),
        ("recall_witnessed", "val recall_witnessed: #a:Type -> #rel:Preorder.preorder a -> r:mref a rel -> p:(a -> Type0){stable p rel} -> ST unit (requires fun h -> witnessed r p) (ensures fun h0 _ h1 -> h0 == h1 /\\ p (HS.sel h1 r))", "let recall_witnessed #a #rel r p = gst_recall r p"),
        ("gst_witness", "val gst_witness: #a:Type -> #rel:Preorder.preorder a -> r:mref a rel -> p:(a -> Type0){stable p rel} -> ST unit (requires fun h -> p (HS.sel h r)) (ensures fun h0 _ h1 -> h0 == h1 /\\ witnessed r p)", "let gst_witness #a #rel r p = witness_p r p"),
        ("stable_predicate", "val stable_predicate: #a:Type -> #rel:Preorder.preorder a -> p:(a -> Type0) -> Lemma (requires forall (x y : a). p x /\\ rel x y ==> p y) (ensures stable p rel)", "let stable_predicate #a #rel p = ()"),
        ("monotonic_ref_read", "val monotonic_ref_read: #a:Type -> #rel:Preorder.preorder a -> r:mref a rel -> ST a (requires fun h -> True) (ensures fun h0 v h1 -> h0 == h1 /\\ v == HS.sel h1 r)", "let monotonic_ref_read #a #rel r = !r"),
        ("monotonic_ref_write", "val monotonic_ref_write: #a:Type -> #rel:Preorder.preorder a -> r:mref a rel -> v:a -> ST unit (requires fun h -> rel (HS.sel h r) v) (ensures fun h0 _ h1 -> HS.sel h1 r == v /\\ modifies (Set.singleton (HS.frameOf r)) h0 h1)", "let monotonic_ref_write #a #rel r v = r := v"),
        ("token_fresh", "val token_fresh: #a:Type -> #rel:Preorder.preorder a -> r:mref a rel -> h:HS.mem -> Lemma (requires HS.contains h r) (ensures HS.frameOf r `HS.is_in` HS.get_hmap h)", "let token_fresh #a #rel r h = ()"),
        ("region_contains", "val region_contains: #a:Type -> #rel:Preorder.preorder a -> r:mref a rel -> h:HS.mem -> Lemma (requires HS.contains h r) (ensures HS.live_region h (HS.frameOf r))", "let region_contains #a #rel r h = ()"),
    ]

    tactics = [
        ("norm_spec", "val norm_spec: a:nat -> b:nat -> Lemma (normalize_term (a + 0) == a)", "let norm_spec a b = assert (normalize_term (a + 0) == a) by (let _ = norm [delta; zeta; primops] in trefl ())"),
        ("canon_semiring", "val canon_semiring: a:int -> b:int -> c:int -> Lemma (a * (b + c) == a * b + a * c)", "let canon_semiring a b c = assert (a * (b + c) == a * b + a * c) by (canon_semiring_int ())"),
        ("trefl_lemma", "val trefl_lemma: a:int -> Lemma (a == a)", "let trefl_lemma a = assert (a == a) by trefl ()"),
        ("mapply_lemma", "val mapply_lemma: a:int -> b:int -> Lemma (requires a == b) (ensures a + 0 == b)", "let mapply_lemma a b = assert (a + 0 == b) by (mapply (`FStar.Math.Lemmas.add_zero_r); assumption ())"),
        ("smt_lemma", "val smt_lemma: a:nat -> b:nat -> Lemma (a + b >= a)", "let smt_lemma a b = assert (a + b >= a) by smt ()"),
        ("pointwise_lemma", "val pointwise_lemma: a:int -> b:int -> c:int -> Lemma ((a + b) + c == a + (b + c))", "let pointwise_lemma a b c = assert ((a + b) + c == a + (b + c)) by (pointwise (fun () -> trefl ()); trefl ())"),
        ("grewrite_lemma", "val grewrite_lemma: a:int -> b:int -> Lemma (requires a == b) (ensures a + 1 == b + 1)", "let grewrite_lemma a b = assert (a + 1 == b + 1) by (grewrite (quote a) (quote b); assumption (); trefl ())"),
        ("tadmit_placeholder", "val tadmit_placeholder: a:int -> b:int -> Lemma (a * b == b * a)", "let tadmit_placeholder a b = assert (a * b == b * a) by tadmit ()"),
    ]

    dependent_types = [
        ("vector_head", "val vector_head: #a:Type -> #n:nat{n > 0} -> v:vector a (n + 1) -> Tot a", "let vector_head #a #n v = Seq.index v 0"),
        ("vector_cons_snoc", "val vector_cons_snoc: #a:Type -> #n:nat -> x:a -> v:vector a n -> Lemma (length (cons x v) == n + 1 /\\ head (cons x v) == x)", "let vector_cons_snoc #a #n x v = ()"),
        ("matrix_mult_assoc", "val matrix_mult_assoc: #m:nat -> #n:nat -> #p:nat -> #q:nat -> a:matrix m n -> b:matrix n p -> c:matrix p q -> Lemma (mat_mult (mat_mult a b) c == mat_mult a (mat_mult b c))", ""),
        ("sized_list_append", "val sized_list_append: #a:Type -> #m:nat -> #n:nat -> l1:sized_list a m -> l2:sized_list a n -> Tot (sized_list a (m + n))", "let rec sized_list_append #a #m #n l1 l2 = match l1 with | SNil -> l2 | SCons x xs -> SCons x (sized_list_append xs l2)"),
        ("bounded_nat_add", "val bounded_nat_add: #bound:nat -> a:bounded_nat bound -> b:bounded_nat bound{a + b <= bound} -> Tot (bounded_nat bound)", "let bounded_nat_add #bound a b = a + b"),
        ("indexed_sum", "val indexed_sum: #n:nat -> f:(i:nat{i < n} -> Tot nat) -> Tot nat (decreases n)", "let rec indexed_sum #n f = if n = 0 then 0 else f (n - 1) + indexed_sum #(n - 1) (fun i -> f i)"),
        ("heterogeneous_list", "val heterogeneous_list: ts:list Type -> Type", "let rec heterogeneous_list ts = match ts with | [] -> unit | t :: rest -> t & heterogeneous_list rest"),
        ("witness_exists", "val witness_exists: #a:Type -> #p:(a -> Type0) -> x:a -> pf:p x -> Tot (dtuple2 a p)", "let witness_exists #a #p x pf = (| x, pf |)"),
        ("refinement_subtyping", "val refinement_subtyping: x:nat{x > 5} -> Tot (y:int{y > 0})", "let refinement_subtyping x = x"),
        ("coercion_lemma", "val coercion_lemma: #a:Type -> #p:(a -> Type0) -> #q:(a -> Type0) -> x:a{p x} -> Lemma (requires forall (y:a). p y ==> q y) (ensures q x)", "let coercion_lemma #a #p #q x = ()"),
    ]

    all_categories = [
        ("arithmetic", arithmetic),
        ("lists", lists),
        ("crypto", crypto_verification),
        ("effects", effects_and_state),
        ("refinement", refinement_types),
        ("termination", termination),
        ("sequences", sequences),
        ("buffers", buffers),
        ("monotonic_state", monotonic_state),
        ("tactics", tactics),
        ("dependent_types", dependent_types),
    ]

    proofs = Dict{String,Any}[]
    for (category, entries) in all_categories
        for entry in entries
            name = entry[1]
            sig = entry[2]
            impl = length(entry) > 2 ? entry[3] : ""

            keywords = [m_.match for m_ in eachmatch(r"\b(Lemma|Tot|Pure|ST|GTot|requires|ensures|decreases|modifies|SMTPat)\b", sig)]
            push!(proofs, Dict{String,Any}(
                "theorem" => name,
                "goal" => sig,
                "tactic_proof" => impl,
                "tactics" => unique(keywords)[1:min(20, length(unique(keywords)))],
                "source" => "fstar_synthetic/$category",
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

    println("[F*] Phase 1: Attempting to download from GitHub ...")
    downloaded = download_fstar_files()
    println("  Downloaded/cached $downloaded files")

    for fname in readdir(EXTERNAL_DIR)
        if endswith(fname, ".fst")
            fpath = joinpath(EXTERNAL_DIR, fname)
            parsed = parse_fstar_file(fpath)
            append!(all_entries, parsed)
            if !isempty(parsed)
                println("  Parsed $(length(parsed)) from $fname")
            end
        end
    end
    extracted_count = length(all_entries)

    println("[F*] Phase 2: Generating synthetic proofs ...")
    synthetic = generate_synthetic_fstar()
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
            "prover" => "FStar",
            "theorem" => entry["theorem"],
            "goal" => entry["goal"],
            "context" => get(entry, "tactics", String[]),
            "tactic_proof" => get(entry, "tactic_proof", ""),
            "source" => get(entry, "source", "fstar"),
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
        "prover" => "FStar",
        "total_proofs" => length(output_records),
        "extracted_from_source" => extracted_count,
        "synthetic_added" => length(output_records) - extracted_count,
        "id_range" => [START_ID, current_id - 1],
    )
    open(STATS_FILE, "w") do fh
        write(fh, JSON3.write(stats))
    end

    println("\n[F*] COMPLETE: $(length(output_records)) proofs written to $OUTPUT_FILE")
    return extracted_count, length(output_records) - extracted_count
end

if abspath(PROGRAM_FILE) == @__FILE__
    run()
end
