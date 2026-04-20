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

    # Phase 1 widening (2026-04-18, echidna#16): previously the
    # extractor skipped every declaration that did not carry at least
    # one spec clause, dropping body-only lemmas and methods whose
    # postconditions are implicit. The signature alone (name, params,
    # return type) is still valuable training signal; keep it even
    # when no requires/ensures/decreases clauses are present.
    pattern = r"(lemma|method|function|predicate|twostate lemma|ghost method|ghost function|least lemma|greatest lemma)\s+(\w+)\s*(?:<[^>]*>)?\s*\((.*?)\)(?:\s*:\s*([^{]+?))?\s*((?:\s*(?:requires|ensures|decreases|modifies|reads|invariant)\s+[^{]*?)*?)(?:\s*\{|\s*$)"s

    for m in eachmatch(pattern, content)
        kind = strip(m.captures[1])
        name = strip(m.captures[2])
        params = replace(strip(something(m.captures[3], "")), r"\s+" => " ")
        ret_type_raw = something(m.captures[4], "")
        ret_type = replace(strip(ret_type_raw), r"\s+" => " ")
        specs = strip(something(m.captures[5], ""))

        specs_clean = replace(specs, r"\s+" => " ")
        # `first(s, n)` is safe for multi-byte strings; the prior
        # `specs_clean[1:min(400, length(specs_clean))]` would crash
        # on any UTF-8 char straddling the truncation boundary.
        specs_clean = first(specs_clean, 400)
        spec_keywords = [lowercase(m_.match) for m_ in eachmatch(
            r"\b(requires|ensures|decreases|modifies|reads|invariant)\b"i, specs)]

        goal = isempty(specs_clean) ?
            "$(kind) $(name)$(isempty(ret_type) ? "" : " : " * ret_type)" :
            specs_clean

        push!(results, Dict{String,Any}(
            "theorem" => name,
            "goal" => goal,
            "kind" => kind,
            "params" => first(params, 200),
            "return_type" => first(ret_type, 80),
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

    map_lemmas = [
        ("MapPutGet", "method MapPutGet<K,V>(m: map<K,V>, k: K, v: V)\n  ensures k in m[k := v]\n  ensures m[k := v][k] == v\n{}", ["ensures"]),
        ("MapRemoveAbsent", "lemma MapRemoveAbsent<K,V>(m: map<K,V>, k: K)\n  requires k !in m\n  ensures m - {k} == m\n{}", ["requires", "ensures"]),
        ("MapDomainSubset", "lemma MapDomainSubset<K,V>(m1: map<K,V>, m2: map<K,V>)\n  requires forall k :: k in m1 ==> k in m2 && m1[k] == m2[k]\n  ensures m1.Keys <= m2.Keys\n{}", ["requires", "ensures"]),
        ("MapDisjointMerge", "lemma MapDisjointMerge<K,V>(m1: map<K,V>, m2: map<K,V>)\n  requires m1.Keys !! m2.Keys\n  ensures |m1 + m2| == |m1| + |m2|\n{}", ["requires", "ensures"]),
        ("MapKeysValues", "lemma MapKeysValues<K,V>(m: map<K,V>)\n  ensures |m.Keys| == |m.Values|\n{}", ["ensures"]),
        ("MapContainsAfterUpdate", "lemma MapContainsAfterUpdate<K,V>(m: map<K,V>, k: K, v: V, k': K)\n  requires k' in m\n  ensures k' in m[k := v]\n{}", ["requires", "ensures"]),
        ("MapEmptyKeys", "lemma MapEmptyKeys<K,V>()\n  ensures (map[]: map<K,V>).Keys == {}\n{}", ["ensures"]),
        ("MapUpdateIdempotent", "lemma MapUpdateIdempotent<K,V>(m: map<K,V>, k: K, v: V)\n  ensures m[k := v][k := v] == m[k := v]\n{}", ["ensures"]),
    ]

    loop_invariants = [
        ("LinearSearch", "method LinearSearch(a: array<int>, key: int) returns (idx: int)\n  ensures 0 <= idx ==> idx < a.Length && a[idx] == key\n  ensures idx < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != key\n{\n  var i := 0;\n  while i < a.Length\n    invariant 0 <= i <= a.Length\n    invariant forall j :: 0 <= j < i ==> a[j] != key\n  {\n    if a[i] == key { return i; }\n    i := i + 1;\n  }\n  return -1;\n}", ["ensures", "invariant"]),
        ("SumArray", "method SumArray(a: array<int>) returns (s: int)\n  ensures s == Sum(a[..], 0, a.Length)\n{\n  s := 0;\n  var i := 0;\n  while i < a.Length\n    invariant 0 <= i <= a.Length\n    invariant s == Sum(a[..], 0, i)\n  {\n    s := s + a[i];\n    i := i + 1;\n  }\n}", ["ensures", "invariant"]),
        ("MaxElement", "method MaxElement(a: array<int>) returns (m: int)\n  requires a.Length > 0\n  ensures forall i :: 0 <= i < a.Length ==> a[i] <= m\n  ensures exists i :: 0 <= i < a.Length && a[i] == m\n{\n  m := a[0];\n  var i := 1;\n  while i < a.Length\n    invariant 1 <= i <= a.Length\n    invariant forall j :: 0 <= j < i ==> a[j] <= m\n    invariant exists j :: 0 <= j < i && a[j] == m\n  {\n    if a[i] > m { m := a[i]; }\n    i := i + 1;\n  }\n}", ["requires", "ensures", "invariant"]),
        ("CountOccurrences", "method CountOccurrences(a: array<int>, key: int) returns (c: int)\n  ensures c == |set i | 0 <= i < a.Length && a[i] == key|\n{\n  c := 0;\n  var i := 0;\n  while i < a.Length\n    invariant 0 <= i <= a.Length\n    invariant c == |set j | 0 <= j < i && a[j] == key|\n  {\n    if a[i] == key { c := c + 1; }\n    i := i + 1;\n  }\n}", ["ensures", "invariant"]),
        ("ReverseInPlace", "method ReverseInPlace(a: array<int>)\n  modifies a\n  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i])\n{\n  var lo, hi := 0, a.Length - 1;\n  while lo < hi\n    invariant 0 <= lo && hi < a.Length\n    invariant lo + hi == a.Length - 1\n    invariant forall i :: 0 <= i < lo ==> a[i] == old(a[a.Length - 1 - i])\n    invariant forall i :: hi < i < a.Length ==> a[i] == old(a[a.Length - 1 - i])\n    invariant forall i :: lo <= i <= hi ==> a[i] == old(a[i])\n  {\n    a[lo], a[hi] := a[hi], a[lo];\n    lo, hi := lo + 1, hi - 1;\n  }\n}", ["modifies", "ensures", "invariant"]),
        ("CopyArray", "method CopyArray(src: array<int>) returns (dst: array<int>)\n  ensures dst.Length == src.Length\n  ensures forall i :: 0 <= i < src.Length ==> dst[i] == src[i]\n  ensures fresh(dst)\n{\n  dst := new int[src.Length];\n  var i := 0;\n  while i < src.Length\n    invariant 0 <= i <= src.Length\n    invariant forall j :: 0 <= j < i ==> dst[j] == src[j]\n  {\n    dst[i] := src[i];\n    i := i + 1;\n  }\n}", ["ensures", "invariant"]),
        ("Partition", "method Partition(a: array<int>, lo: int, hi: int) returns (p: int)\n  requires 0 <= lo < hi <= a.Length\n  modifies a\n  ensures lo <= p < hi\n  ensures forall i :: lo <= i < p ==> a[i] <= a[p]\n  ensures forall i :: p < i < hi ==> a[i] > a[p]\n  ensures multiset(a[lo..hi]) == multiset(old(a[lo..hi]))\n{}", ["requires", "modifies", "ensures"]),
        ("TwoSum", "method TwoSum(a: array<int>, target: int) returns (i: int, j: int)\n  requires Sorted(a, 0, a.Length)\n  ensures 0 <= i < j < a.Length ==> a[i] + a[j] == target\n{\n  i, j := 0, a.Length - 1;\n  while i < j\n    invariant 0 <= i && j < a.Length\n    invariant forall p, q :: 0 <= p < i && i <= q < a.Length ==> a[p] + a[q] != target\n  {\n    if a[i] + a[j] == target { return; }\n    else if a[i] + a[j] < target { i := i + 1; }\n    else { j := j - 1; }\n  }\n  return -1, -1;\n}", ["requires", "ensures", "invariant"]),
    ]

    inductive_proofs = [
        ("SumFormula", "lemma SumFormula(n: nat)\n  ensures 2 * SumTo(n) == n * (n + 1)\n  decreases n\n{\n  if n == 0 { } else { SumFormula(n - 1); }\n}", ["ensures", "decreases"]),
        ("PowerMonotone", "lemma PowerMonotone(b: nat, m: nat, n: nat)\n  requires b >= 2 && m <= n\n  ensures Pow(b, m) <= Pow(b, n)\n  decreases n - m\n{\n  if m == n { } else { PowerMonotone(b, m, n - 1); }\n}", ["requires", "ensures", "decreases"]),
        ("ListFlatten", "lemma ListFlatten<T>(l1: List<T>, l2: List<T>)\n  ensures Length(Append(l1, l2)) == Length(l1) + Length(l2)\n  decreases l1\n{\n  match l1 { case Nil => case Cons(_, tl) => ListFlatten(tl, l2); }\n}", ["ensures", "decreases"]),
        ("TreeHeight", "lemma TreeHeight(t: Tree)\n  ensures Height(t) >= 0\n  decreases t\n{\n  match t {\n    case Leaf => {}\n    case Node(l, _, r) => { TreeHeight(l); TreeHeight(r); }\n  }\n}", ["ensures", "decreases"]),
        ("FibMonotone", "lemma FibMonotone(m: nat, n: nat)\n  requires m <= n && m >= 1\n  ensures Fib(m) <= Fib(n)\n  decreases n - m\n{\n  if m == n { } else { FibMonotone(m, n - 1); FibPositive(n - 2); }\n}", ["requires", "ensures", "decreases"]),
        ("StrongInduction", "lemma StrongInduction(n: nat, P: nat -> bool)\n  requires forall k: nat :: (forall j: nat :: j < k ==> P(j)) ==> P(k)\n  ensures P(n)\n  decreases n\n{\n  forall j: nat | j < n ensures P(j) { StrongInduction(j, P); }\n}", ["requires", "ensures", "decreases"]),
        ("BinomialTheorem", "lemma BinomialTheorem(x: int, y: int, n: nat)\n  ensures Pow(x + y, n) == Sum(k => Choose(n, k) * Pow(x, n - k) * Pow(y, k), 0, n)\n  decreases n\n{}", ["ensures", "decreases"]),
    ]

    ghost_state = [
        ("GhostCounter", "method GhostCounter(n: nat) returns (r: nat)\n  ensures r == n\n{\n  r := 0;\n  ghost var g := 0;\n  while r < n\n    invariant r == g && r <= n\n  {\n    r := r + 1;\n    g := g + 1;\n  }\n}", ["ensures", "invariant"]),
        ("FrameCondition", "method FrameCondition(a: array<int>, b: array<int>, i: nat)\n  requires a != b && i < a.Length\n  modifies a\n  ensures b[..] == old(b[..])\n  ensures forall j :: 0 <= j < a.Length && j != i ==> a[j] == old(a[j])\n{\n  a[i] := a[i] + 1;\n}", ["requires", "modifies", "ensures"]),
        ("ReprValid", "class Node {\n  var val: int\n  var next: Node?\n  ghost var repr: set<Node>\n  predicate Valid()\n    reads this, repr\n  {\n    this in repr &&\n    (next != null ==> next in repr && next.repr < repr && next.Valid())\n  }\n}", ["reads"]),
        ("AllocFresh", "method AllocFresh() returns (r: array<int>)\n  ensures fresh(r)\n  ensures r.Length == 10\n  ensures forall i :: 0 <= i < 10 ==> r[i] == 0\n{\n  r := new int[10];\n}", ["ensures"]),
        ("GhostSequence", "method GhostSequence(a: array<int>)\n  modifies a\n  ensures a[..] == Reverse(old(a[..]))\n{\n  ghost var original := a[..];\n  ReverseInPlace(a);\n}", ["modifies", "ensures"]),
    ]

    type_refinement = [
        ("NonNullArray", "type NonNullArray = a: array<int> | a.Length > 0 witness *", []),
        ("PositiveInt", "type Positive = n: int | n > 0 witness 1", []),
        ("BoundedInt", "type Bounded = n: int | 0 <= n < 256 witness 0", []),
        ("EvenNat", "type EvenNat = n: nat | n % 2 == 0 witness 0", []),
        ("SortedSeq", "type SortedSeq = s: seq<int> | forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j] witness []", []),
        ("NonEmptySeq", "type NonEmptySeq<T> = s: seq<T> | |s| > 0 witness *", []),
        ("UniqueSeq", "type UniqueSeq<T(==)> = s: seq<T> | forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j] witness []", []),
        ("Percentage", "type Percentage = r: real | 0.0 <= r <= 100.0 witness 0.0", []),
    ]

    concurrency_specs = [
        ("MutexSpec", "class Mutex {\n  ghost var locked: bool\n  method Acquire()\n    requires !locked\n    modifies this\n    ensures locked\n  {\n    locked := true;\n  }\n  method Release()\n    requires locked\n    modifies this\n    ensures !locked\n  {\n    locked := false;\n  }\n}", ["requires", "modifies", "ensures"]),
        ("TokenRing", "method TokenRing(nodes: array<bool>, holder: nat)\n  requires holder < nodes.Length\n  requires nodes[holder] == true\n  requires forall i :: 0 <= i < nodes.Length && i != holder ==> nodes[i] == false\n  modifies nodes\n  ensures nodes[(holder + 1) % nodes.Length] == true\n  ensures forall i :: 0 <= i < nodes.Length && i != (holder + 1) % nodes.Length ==> nodes[i] == false\n{}", ["requires", "modifies", "ensures"]),
        ("AtomicIncrement", "method AtomicIncrement(x: int) returns (y: int)\n  ensures y == x + 1\n{\n  y := x + 1;\n}", ["ensures"]),
        ("CompareAndSwap", "method CAS(r: ref<int>, expected: int, desired: int) returns (success: bool)\n  modifies r\n  ensures success ==> old(r.val) == expected && r.val == desired\n  ensures !success ==> r.val == old(r.val)\n{}", ["modifies", "ensures"]),
    ]

    all_categories = [
        ("arithmetic", arithmetic_lemmas),
        ("sequences", sequence_lemmas),
        ("sets", set_lemmas),
        ("sorting", sorting_search),
        ("data_structures", data_structures),
        ("termination", termination),
        ("maps", map_lemmas),
        ("loops", loop_invariants),
        ("induction", inductive_proofs),
        ("ghost", ghost_state),
        ("types", type_refinement),
        ("concurrency", concurrency_specs),
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

    # Phase 1 strategy (2026-04-18, echidna#16): prefer a full
    # dafny-lang/dafny sparse clone (`Test/` + `Source/IntegrationTests/`)
    # — thousands of .dfy files. Fall back to the curated downloader
    # only if nothing is on disk.
    #
    # Phase 2 widening (2026-04-18 late): also walk sibling vendored
    # corpora that ship significant real-world Dafny proofs — AWS
    # Encryption SDK, AWS Cryptographic Material Providers Library,
    # Dafny-VMC (randomised programs), and the dafny-lang/libraries
    # standard library. Each adds hundreds of proofs.
    dfy_roots = String[EXTERNAL_DIR]
    for sibling in ("dafny-libraries", "dafny-vmc",
                     "aws-encryption-sdk-dafny", "aws-cmpl")
        cand = joinpath(dirname(EXTERNAL_DIR), sibling)
        isdir(cand) && push!(dfy_roots, cand)
    end
    dfy_files = String[]
    for root_dir in dfy_roots
        for (root, _dirs, files) in walkdir(root_dir)
            for f in files
                endswith(f, ".dfy") && push!(dfy_files, joinpath(root, f))
            end
        end
    end
    if isempty(dfy_files)
        println("[Dafny] Phase 1: No corpus found — running curated downloader ...")
        downloaded = download_dafny_files()
        println("  Downloaded/cached $downloaded files")
        for f in readdir(EXTERNAL_DIR)
            endswith(f, ".dfy") && push!(dfy_files, joinpath(EXTERNAL_DIR, f))
        end
    else
        println("[Dafny] Phase 1: Found $(length(dfy_files)) .dfy files under $(EXTERNAL_DIR) ...")
    end

    processed = 0
    for fpath in dfy_files
        parsed = parse_dafny_file(fpath)
        append!(all_entries, parsed)
        processed += 1
        if processed % 200 == 0
            println("  processed $(processed)/$(length(dfy_files)) files — running count: $(length(all_entries))")
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
