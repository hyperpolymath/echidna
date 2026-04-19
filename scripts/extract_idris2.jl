#!/usr/bin/env julia
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
#
# Extract proofs from Idris2 stdlib and tests, convert to ECHIDNA training format.
#
# Attempts to download from the Idris2 GitHub repository (libs/ and tests/ dirs).
# Falls back to generating high-quality synthetic Idris2 proofs.
#
# Idris2 is a dependently-typed functional programming language with first-class
# support for theorem proving. It features linear types (Quantities) and an
# elaborator reflection system for metaprogramming.
#
# Output: training_data/proof_states_idris2.jsonl
# ID range: 98000+

using JSON3
using Downloads

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

const REPO_ROOT = dirname(dirname(abspath(@__FILE__)))
const EXTERNAL_DIR = joinpath(REPO_ROOT, "external_corpora", "idris2")
const OUTPUT_DIR = joinpath(REPO_ROOT, "training_data")
const OUTPUT_FILE = joinpath(OUTPUT_DIR, "proof_states_idris2.jsonl")
const STATS_FILE = joinpath(OUTPUT_DIR, "stats_idris2.json")
const START_ID = 98000

const IDRIS2_RAW = "https://raw.githubusercontent.com/idris-lang/Idris2/main"
const IDRIS2_FILES = [
    "libs/prelude/Prelude/Types.idr",
    "libs/prelude/Prelude/Basics.idr",
    "libs/prelude/Prelude/EqOrd.idr",
    "libs/prelude/Prelude/Interfaces.idr",
    "libs/prelude/Prelude/Num.idr",
    "libs/base/Data/List.idr",
    "libs/base/Data/Nat.idr",
    "libs/base/Data/Vect.idr",
    "libs/base/Data/Fin.idr",
    "libs/base/Data/SnocList.idr",
    "libs/base/Decidable/Equality.idr",
    "libs/contrib/Data/Nat/Factor.idr",
    "libs/contrib/Data/List/Elem.idr",
    "libs/contrib/Data/Vect/Sort.idr",
    "tests/idris2/basic/basic001/Test.idr",
    "tests/idris2/basic/basic002/Test.idr",
]

"""
    parse_idris2_file(filepath::String) -> Vector{Dict{String,Any}}

Parse an Idris2 .idr file and extract public export function/data patterns.
"""
function parse_idris2_file(filepath::String)::Vector{Dict{String,Any}}
    results = Dict{String,Any}[]
    local content::String
    try
        content = read(filepath, String)
    catch
        return results
    end

    # Type signature followed by implementation
    # Pattern: name : type
    sig_pattern = r"^(\w+)\s*:\s*(.*?)$"m

    for m in eachmatch(sig_pattern, content)
        name = strip(m.captures[1])
        sig = replace(strip(m.captures[2]), r"\s+" => " ")
        sig = sig[1:min(300, length(sig))]

        # Skip imports, module declarations, etc.
        if name in ("module", "import", "data", "record", "interface", "implementation", "where", "namespace", "mutual", "parameters")
            continue
        end

        # Look for proof-relevant types
        if any(kw -> occursin(kw, sig), ["Void", "Dec", "Equal", "So", "LTE", "GTE", "Elem", "contra", "Refl", "DecEq", "Uninhabited"])
            keywords = [m_.match for m_ in eachmatch(r"\b(Void|Dec|Equal|So|LTE|GTE|Elem|Refl|DecEq|Uninhabited|Vect|Nat|Fin|DPair|Not)\b", sig)]
            push!(results, Dict{String,Any}(
                "theorem" => name,
                "goal" => sig,
                "tactics" => unique(keywords)[1:min(20, length(unique(keywords)))],
                "source" => "idris2/$(basename(filepath))",
            ))
        end
    end

    return results
end

"""
    download_idris2_files() -> Int

Attempt to download Idris2 source files.
"""
function download_idris2_files()::Int
    downloaded = 0
    for rel_path in IDRIS2_FILES
        url = "$IDRIS2_RAW/$rel_path"
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
    generate_synthetic_idris2() -> Vector{Dict{String,Any}}

Generate high-quality synthetic Idris2 proofs using dependent types.
"""
function generate_synthetic_idris2()::Vector{Dict{String,Any}}
    equality_proofs = [
        ("plusZeroRightNeutral", "plusZeroRightNeutral : (n : Nat) -> n + 0 = n", "plusZeroRightNeutral Z = Refl\nplusZeroRightNeutral (S k) = cong S (plusZeroRightNeutral k)"),
        ("plusSuccRightSucc", "plusSuccRightSucc : (left : Nat) -> (right : Nat) -> S (left + right) = left + S right", "plusSuccRightSucc Z right = Refl\nplusSuccRightSucc (S k) right = cong S (plusSuccRightSucc k right)"),
        ("plusCommutative", "plusCommutative : (left : Nat) -> (right : Nat) -> left + right = right + left", "plusCommutative Z right = sym (plusZeroRightNeutral right)\nplusCommutative (S k) right = rewrite plusCommutative k right in plusSuccRightSucc right k"),
        ("plusAssociative", "plusAssociative : (l, c, r : Nat) -> l + (c + r) = (l + c) + r", "plusAssociative Z c r = Refl\nplusAssociative (S k) c r = cong S (plusAssociative k c r)"),
        ("multZeroRightZero", "multZeroRightZero : (n : Nat) -> n * 0 = 0", "multZeroRightZero Z = Refl\nmultZeroRightZero (S k) = multZeroRightZero k"),
        ("multOneRightNeutral", "multOneRightNeutral : (n : Nat) -> n * 1 = n", "multOneRightNeutral Z = Refl\nmultOneRightNeutral (S k) = cong S (multOneRightNeutral k)"),
        ("multRightSuccPlus", "multRightSuccPlus : (left, right : Nat) -> left * S right = left + left * right", "multRightSuccPlus Z right = Refl\nmultRightSuccPlus (S k) right = rewrite multRightSuccPlus k right in rewrite sym (plusAssociative right k (k * right)) in rewrite plusCommutative right k in rewrite plusAssociative k right (k * right) in Refl"),
        ("multCommutative", "multCommutative : (left, right : Nat) -> left * right = right * left", "multCommutative Z right = sym (multZeroRightZero right)\nmultCommutative (S k) right = rewrite multCommutative k right in sym (multRightSuccPlus right k)"),
        ("multDistributesOverPlusLeft", "multDistributesOverPlusLeft : (l, c, r : Nat) -> (l + c) * r = l * r + c * r", "multDistributesOverPlusLeft Z c r = Refl\nmultDistributesOverPlusLeft (S k) c r = rewrite multDistributesOverPlusLeft k c r in sym (plusAssociative r (k * r) (c * r))"),
        ("multAssociative", "multAssociative : (l, c, r : Nat) -> l * (c * r) = (l * c) * r", "multAssociative Z c r = Refl\nmultAssociative (S k) c r = rewrite multAssociative k c r in rewrite multDistributesOverPlusLeft c (k * c) r in Refl"),
    ]

    decidable = [
        ("decEqNat", "decEqNat : (n1, n2 : Nat) -> Dec (n1 = n2)", "decEqNat Z Z = Yes Refl\ndecEqNat Z (S _) = No absurd\ndecEqNat (S _) Z = No absurd\ndecEqNat (S k) (S j) = case decEqNat k j of { Yes prf => Yes (cong S prf); No contra => No (\\h => contra (injective h)) }"),
        ("isLTE", "isLTE : (m, n : Nat) -> Dec (LTE m n)", "isLTE Z n = Yes LTEZero\nisLTE (S k) Z = No absurd\nisLTE (S k) (S j) = case isLTE k j of { Yes prf => Yes (LTESucc prf); No contra => No (\\(LTESucc p) => contra p) }"),
        ("decEqBool", "decEqBool : (b1, b2 : Bool) -> Dec (b1 = b2)", "decEqBool True True = Yes Refl\ndecEqBool False False = Yes Refl\ndecEqBool True False = No absurd\ndecEqBool False True = No absurd"),
        ("notNotTrue", "notNotTrue : Not (Not a) -> a -> Void -> Void", "notNotTrue f x = f (\\y => absurd (y x))"),
        ("decNot", "decNot : Dec a -> Dec (Not a)", "decNot (Yes prf) = No (\\f => f prf)\ndecNot (No contra) = Yes contra"),
    ]

    vector_proofs = [
        ("vectAppendNilRightNeutral", "vectAppendNilRightNeutral : (xs : Vect n a) -> xs ++ [] = xs", "vectAppendNilRightNeutral [] = Refl\nvectAppendNilRightNeutral (x :: xs) = cong (x ::) (vectAppendNilRightNeutral xs)"),
        ("vectMapId", "vectMapId : (xs : Vect n a) -> map id xs = xs", "vectMapId [] = Refl\nvectMapId (x :: xs) = cong (x ::) (vectMapId xs)"),
        ("vectMapCompose", "vectMapCompose : (f : b -> c) -> (g : a -> b) -> (xs : Vect n a) -> map f (map g xs) = map (f . g) xs", "vectMapCompose f g [] = Refl\nvectMapCompose f g (x :: xs) = cong (f (g x) ::) (vectMapCompose f g xs)"),
        ("vectLengthMap", "vectLengthMap : (f : a -> b) -> (xs : Vect n a) -> length (map f xs) = length xs", "vectLengthMap f [] = Refl\nvectLengthMap f (x :: xs) = cong S (vectLengthMap f xs)"),
        ("vectReverseReverse", "vectReverseReverse : (xs : Vect n a) -> reverse (reverse xs) = xs", ""),
        ("vectIndexMap", "vectIndexMap : (f : a -> b) -> (xs : Vect n a) -> (i : Fin n) -> index i (map f xs) = f (index i xs)", "vectIndexMap f (x :: xs) FZ = Refl\nvectIndexMap f (x :: xs) (FS k) = vectIndexMap f xs k"),
        ("vectZipWithComm", "vectZipWithComm : (f : a -> a -> b) -> ((x, y : a) -> f x y = f y x) -> (xs, ys : Vect n a) -> zipWith f xs ys = zipWith f ys xs", "vectZipWithComm f prf [] [] = Refl\nvectZipWithComm f prf (x :: xs) (y :: ys) = rewrite prf x y in cong (f y x ::) (vectZipWithComm f prf xs ys)"),
        ("vectAppendLength", "vectAppendLength : (xs : Vect m a) -> (ys : Vect n a) -> length (xs ++ ys) = m + n", "vectAppendLength [] ys = Refl\nvectAppendLength (x :: xs) ys = cong S (vectAppendLength xs ys)"),
    ]

    list_proofs = [
        ("appendNilRightNeutral", "appendNilRightNeutral : (l : List a) -> l ++ [] = l", "appendNilRightNeutral [] = Refl\nappendNilRightNeutral (x :: xs) = cong (x ::) (appendNilRightNeutral xs)"),
        ("appendAssociative", "appendAssociative : (l, c, r : List a) -> l ++ (c ++ r) = (l ++ c) ++ r", "appendAssociative [] c r = Refl\nappendAssociative (x :: xs) c r = cong (x ::) (appendAssociative xs c r)"),
        ("mapAppend", "mapAppend : (f : a -> b) -> (l1, l2 : List a) -> map f (l1 ++ l2) = map f l1 ++ map f l2", "mapAppend f [] l2 = Refl\nmapAppend f (x :: xs) l2 = cong (f x ::) (mapAppend f xs l2)"),
        ("lengthAppend", "lengthAppend : (l1, l2 : List a) -> length (l1 ++ l2) = length l1 + length l2", "lengthAppend [] l2 = Refl\nlengthAppend (x :: xs) l2 = cong S (lengthAppend xs l2)"),
        ("mapId", "mapId : (l : List a) -> map id l = l", "mapId [] = Refl\nmapId (x :: xs) = cong (x ::) (mapId xs)"),
        ("mapCompose", "mapCompose : (f : b -> c) -> (g : a -> b) -> (l : List a) -> map f (map g l) = map (f . g) l", "mapCompose f g [] = Refl\nmapCompose f g (x :: xs) = cong (f (g x) ::) (mapCompose f g xs)"),
        ("filterAppend", "filterAppend : (p : a -> Bool) -> (l1, l2 : List a) -> filter p (l1 ++ l2) = filter p l1 ++ filter p l2", "filterAppend p [] l2 = Refl\nfilterAppend p (x :: xs) l2 with (p x) | filterAppend p xs l2\n  _ | True  | rec = cong (x ::) rec\n  _ | False | rec = rec"),
        ("reverseAppend", "reverseAppend : (l1, l2 : List a) -> reverse (l1 ++ l2) = reverse l2 ++ reverse l1", ""),
    ]

    fin_proofs = [
        ("finToNatBound", "finToNatBound : (i : Fin n) -> LT (finToNat i) n", "finToNatBound FZ = LTESucc LTEZero\nfinToNatBound (FS k) = LTESucc (finToNatBound k)"),
        ("finToNatWeaken", "finToNatWeaken : (i : Fin n) -> finToNat (weaken i) = finToNat i", "finToNatWeaken FZ = Refl\nfinToNatWeaken (FS k) = cong S (finToNatWeaken k)"),
        ("finToNatLast", "finToNatLast : {n : Nat} -> finToNat (last {n}) = n", "finToNatLast {n = Z} = Refl\nfinToNatLast {n = S k} = cong S finToNatLast"),
        ("strengthenWeaken", "strengthenWeaken : (i : Fin n) -> strengthen (weaken i) = Just i", ""),
        ("lastIsLargest", "lastIsLargest : (i : Fin (S n)) -> LTE (finToNat i) n", ""),
    ]

    linear_types = [
        ("linearSwap", "linearSwap : (1 x : a) -> (1 y : b) -> (b, a)", "linearSwap x y = (y, x)"),
        ("linearDup", "linearDup : (1 x : a) -> {auto prf : Dup a} -> (a, a)", "linearDup x = dup x"),
        ("linearMap", "linearMap : (1 f : a -o b) -> (1 xs : LList a) -> LList b", "linearMap f [] = []\nlinearMap f (x :: xs) = f x :: linearMap f xs"),
        ("useOnce", "useOnce : (1 r : Resource) -> IO ()", "useOnce r = release r"),
        ("linearFold", "linearFold : (1 f : b -o a -o b) -> (1 init : b) -> (1 xs : LList a) -> b", "linearFold f init [] = init\nlinearFold f init (x :: xs) = linearFold f (f init x) xs"),
    ]

    dependent_pairs = [
        ("dpairFst", "dpairFst : DPair a p -> a", "dpairFst (x ** _) = x"),
        ("dpairSnd", "dpairSnd : (d : DPair a p) -> p (fst d)", "dpairSnd (_ ** prf) = prf"),
        ("filterDPair", "filterDPair : (p : a -> Bool) -> List a -> List (DPair a (\\x => So (p x)))", "filterDPair p [] = []\nfilterDPair p (x :: xs) with (p x) proof eq\n  _ | True = (x ** eqToSo eq) :: filterDPair p xs\n  _ | False = filterDPair p xs"),
        ("lookupDPair", "lookupDPair : DecEq k => (key : k) -> List (k, v) -> Maybe (DPair v (\\_ => Unit))", ""),
        ("existsNat", "existsNat : (n : Nat ** LTE 5 n)", "existsNat = (5 ** reflexive)"),
    ]

    interfaces = [
        ("functorId", "functorId : Functor f => (x : f a) -> map id x = x", ""),
        ("functorCompose", "functorCompose : Functor f => (g : b -> c) -> (h : a -> b) -> (x : f a) -> map g (map h x) = map (g . h) x", ""),
        ("monadLeftId", "monadLeftId : Monad m => (a : t) -> (f : t -> m u) -> (pure a >>= f) = f a", ""),
        ("monadRightId", "monadRightId : Monad m => (ma : m a) -> (ma >>= pure) = ma", ""),
        ("monadAssoc", "monadAssoc : Monad m => (ma : m a) -> (f : a -> m b) -> (g : b -> m c) -> ((ma >>= f) >>= g) = (ma >>= (\\x => f x >>= g))", ""),
    ]

    maybe_proofs = [
        ("maybeMap", "maybeMap : (f : a -> b) -> Maybe a -> Maybe b", "maybeMap f Nothing = Nothing\nmaybeMap f (Just x) = Just (f x)"),
        ("maybeMapCompose", "maybeMapCompose : (f : b -> c) -> (g : a -> b) -> (mx : Maybe a) -> maybeMap f (maybeMap g mx) = maybeMap (f . g) mx", "maybeMapCompose f g Nothing = Refl\nmaybeMapCompose f g (Just x) = Refl"),
        ("maybeBind", "maybeBind : Maybe a -> (a -> Maybe b) -> Maybe b", "maybeBind Nothing f = Nothing\nmaybeBind (Just x) f = f x"),
        ("maybeBindAssoc", "maybeBindAssoc : (mx : Maybe a) -> (f : a -> Maybe b) -> (g : b -> Maybe c) -> maybeBind (maybeBind mx f) g = maybeBind mx (\\x => maybeBind (f x) g)", "maybeBindAssoc Nothing f g = Refl\nmaybeBindAssoc (Just x) f g = Refl"),
        ("isJustFromJust", "isJustFromJust : (mx : Maybe a) -> isJust mx = True -> DPair a (\\x => mx = Just x)", "isJustFromJust (Just x) Refl = (x ** Refl)\nisJustFromJust Nothing Refl impossible"),
        ("nothingAbsurd", "nothingAbsurd : the (Maybe a) Nothing = Just x -> Void", "nothingAbsurd Refl impossible"),
        ("maybeToList", "maybeToList : Maybe a -> List a", "maybeToList Nothing = []\nmaybeToList (Just x) = [x]"),
        ("fromMaybeDefault", "fromMaybeDefault : (def : a) -> (mx : Maybe a) -> mx = Nothing -> fromMaybe def mx = def", "fromMaybeDefault def Nothing Refl = Refl\nfromMaybeDefault def (Just _) Refl impossible"),
    ]

    either_proofs = [
        ("eitherMap", "eitherMap : (f : a -> c) -> (g : b -> d) -> Either a b -> Either c d", "eitherMap f g (Left x) = Left (f x)\neitherMap f g (Right y) = Right (g y)"),
        ("eitherMapCompose", "eitherMapCompose : (f1 : c -> e) -> (f2 : a -> c) -> (g1 : d -> f) -> (g2 : b -> d) -> (e : Either a b) -> eitherMap f1 g1 (eitherMap f2 g2 e) = eitherMap (f1 . f2) (g1 . g2) e", "eitherMapCompose f1 f2 g1 g2 (Left x) = Refl\neitherMapCompose f1 f2 g1 g2 (Right y) = Refl"),
        ("eitherBimap", "eitherBimap : (f : a -> c) -> (g : b -> d) -> Either a b -> Either c d", "eitherBimap f g (Left x) = Left (f x)\neitherBimap f g (Right y) = Right (g y)"),
        ("eitherSwap", "eitherSwap : Either a b -> Either b a", "eitherSwap (Left x) = Right x\neitherSwap (Right y) = Left y"),
        ("eitherAssoc", "eitherAssoc : Either (Either a b) c -> Either a (Either b c)", "eitherAssoc (Left (Left x)) = Left x\neitherAssoc (Left (Right y)) = Right (Left y)\neitherAssoc (Right z) = Right (Right z)"),
        ("partitionEithers", "partitionEithers : List (Either a b) -> (List a, List b)", "partitionEithers [] = ([], [])\npartitionEithers (Left x :: xs) = let (ls, rs) = partitionEithers xs in (x :: ls, rs)\npartitionEithers (Right y :: xs) = let (ls, rs) = partitionEithers xs in (ls, y :: rs)"),
        ("leftsAppend", "leftsAppend : (xs, ys : List (Either a b)) -> fst (partitionEithers (xs ++ ys)) = fst (partitionEithers xs) ++ fst (partitionEithers ys)", ""),
        ("rightsAppend", "rightsAppend : (xs, ys : List (Either a b)) -> snd (partitionEithers (xs ++ ys)) = snd (partitionEithers xs) ++ snd (partitionEithers ys)", ""),
    ]

    nat_order = [
        ("lteRefl", "lteRefl : (n : Nat) -> LTE n n", "lteRefl Z = LTEZero\nlteRefl (S k) = LTESucc (lteRefl k)"),
        ("lteAntisym", "lteAntisym : LTE m n -> LTE n m -> m = n", "lteAntisym LTEZero LTEZero = Refl\nlteAntisym (LTESucc p) (LTESucc q) = cong S (lteAntisym p q)"),
        ("lteTrans", "lteTrans : LTE l c -> LTE c r -> LTE l r", "lteTrans LTEZero _ = LTEZero\nlteTrans (LTESucc p) (LTESucc q) = LTESucc (lteTrans p q)"),
        ("lteSuccRight", "lteSuccRight : LTE m n -> LTE m (S n)", "lteSuccRight LTEZero = LTEZero\nlteSuccRight (LTESucc p) = LTESucc (lteSuccRight p)"),
        ("lteAddRight", "lteAddRight : (m : Nat) -> (n : Nat) -> LTE m (m + n)", "lteAddRight Z n = LTEZero\nlteAddRight (S k) n = LTESucc (lteAddRight k n)"),
        ("notLteToGt", "notLteToGt : Not (LTE m n) -> LT n m", "notLteToGt {m = Z} contra = absurd (contra LTEZero)\nnotLteToGt {m = S k} {n = Z} _ = LTESucc LTEZero\nnotLteToGt {m = S k} {n = S j} contra = LTESucc (notLteToGt (\\p => contra (LTESucc p)))"),
        ("ltToLte", "ltToLte : LT m n -> LTE m n", "ltToLte (LTESucc p) = lteSuccRight p"),
        ("maxComm", "maxComm : (m, n : Nat) -> max m n = max n m", ""),
    ]

    stream_proofs = [
        ("takeLength", "takeLength : (n : Nat) -> (s : Stream a) -> length (take n s) = n", "takeLength Z s = Refl\ntakeLength (S k) (x :: xs) = cong S (takeLength k xs)"),
        ("iterateHead", "iterateHead : (f : a -> a) -> (x : a) -> head (iterate f x) = x", "iterateHead f x = Refl"),
        ("repeatHead", "repeatHead : (x : a) -> head (repeat x) = x", "repeatHead x = Refl"),
        ("cycleNonEmpty", "cycleNonEmpty : (xs : List a) -> NonEmpty xs -> Stream a", "cycleNonEmpty (x :: xs) IsNonEmpty = cycle (x :: xs)"),
        ("zipWithLength", "zipWithLength : (f : a -> b -> c) -> (n : Nat) -> (s1 : Stream a) -> (s2 : Stream b) -> length (take n (zipWith f s1 s2)) = n", "zipWithLength f Z s1 s2 = Refl\nzipWithLength f (S k) (x :: xs) (y :: ys) = cong S (zipWithLength f k xs ys)"),
        ("mapStream", "mapStream : (f : a -> b) -> (n : Nat) -> (s : Stream a) -> take n (map f s) = map f (take n s)", "mapStream f Z s = Refl\nmapStream f (S k) (x :: xs) = cong (f x ::) (mapStream f k xs)"),
    ]

    universe_proofs = [
        ("voidAbsurd", "voidAbsurd : Void -> a", "voidAbsurd v = absurd v"),
        ("unitUnique", "unitUnique : (x, y : ()) -> x = y", "unitUnique () () = Refl"),
        ("boolDec", "boolDec : (b : Bool) -> Dec (b = True)", "boolDec True = Yes Refl\nboolDec False = No absurd"),
        ("notNotBool", "notNotBool : (b : Bool) -> not (not b) = b", "notNotBool True = Refl\nnotNotBool False = Refl"),
        ("decElim", "decElim : (a -> b) -> (Not a -> b) -> Dec a -> b", "decElim f g (Yes prf) = f prf\ndecElim f g (No contra) = g contra"),
        ("eitherCommIso", "eitherCommIso : Either a b -> Either b a", "eitherCommIso (Left x) = Right x\neitherCommIso (Right y) = Left y"),
    ]

    type_level = [
        ("lengthReplicate", "lengthReplicate : (n : Nat) -> (x : a) -> length (replicate n x) = n", "lengthReplicate Z x = Refl\nlengthReplicate (S k) x = cong S (lengthReplicate k x)"),
        ("transposeInvolutive", "transposeInvolutive : (xss : Vect m (Vect n a)) -> transpose (transpose xss) = xss", ""),
        ("diagonalZip", "diagonalZip : (xs : Vect n a) -> map (\\i => index i xs) range = xs", ""),
        ("tabulateIndex", "tabulateIndex : (f : Fin n -> a) -> (i : Fin n) -> index i (tabulate f) = f i", "tabulateIndex f FZ = Refl\ntabulateIndex f (FS k) = tabulateIndex (f . FS) k"),
        ("generateLength", "generateLength : (n : Nat) -> (f : Fin n -> a) -> length (toList (tabulate f)) = n", ""),
        ("concatMapLength", "concatMapLength : (f : a -> Vect m b) -> (xs : Vect n a) -> length (concat (map f xs)) = n * m", "concatMapLength f [] = Refl\nconcatMapLength f (x :: xs) = rewrite concatMapLength f xs in vectAppendLength (f x) (concat (map f xs))"),
        ("intersperse", "intersperse : a -> Vect n a -> Vect (n + pred n) a", "intersperse sep [] = []\nintersperse sep [x] = [x]\nintersperse sep (x :: y :: ys) = x :: sep :: intersperse sep (y :: ys)"),
        ("chunksOfLength", "chunksOfLength : (k : Nat) -> {auto ok : NonZero k} -> (xs : Vect n a) -> length (chunksOf k xs) = divCeilNZ n k ok", ""),
    ]

    all_categories = [
        ("equality", equality_proofs),
        ("decidable", decidable),
        ("vectors", vector_proofs),
        ("lists", list_proofs),
        ("fin", fin_proofs),
        ("linear", linear_types),
        ("dpair", dependent_pairs),
        ("interfaces", interfaces),
        ("maybe", maybe_proofs),
        ("either", either_proofs),
        ("nat_order", nat_order),
        ("streams", stream_proofs),
        ("universe", universe_proofs),
        ("type_level", type_level),
    ]

    proofs = Dict{String,Any}[]
    for (category, entries) in all_categories
        for entry in entries
            name = entry[1]
            sig = entry[2]
            impl = length(entry) > 2 ? entry[3] : ""

            keywords = [m_.match for m_ in eachmatch(r"\b(Vect|Nat|Fin|Dec|LTE|GTE|DPair|Refl|Void|So|Equal|List|Bool|Maybe|IO)\b", sig)]
            push!(proofs, Dict{String,Any}(
                "theorem" => name,
                "goal" => sig,
                "tactic_proof" => impl,
                "tactics" => unique(keywords)[1:min(20, length(unique(keywords)))],
                "source" => "idris2_synthetic/$category",
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

    println("[Idris2] Phase 1: Attempting to download from GitHub ...")
    downloaded = download_idris2_files()
    println("  Downloaded/cached $downloaded files")

    for fname in readdir(EXTERNAL_DIR)
        if endswith(fname, ".idr")
            fpath = joinpath(EXTERNAL_DIR, fname)
            parsed = parse_idris2_file(fpath)
            append!(all_entries, parsed)
            if !isempty(parsed)
                println("  Parsed $(length(parsed)) from $fname")
            end
        end
    end
    extracted_count = length(all_entries)

    println("[Idris2] Phase 2: Generating synthetic proofs ...")
    synthetic = generate_synthetic_idris2()
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
            "prover" => "Idris2",
            "theorem" => entry["theorem"],
            "goal" => entry["goal"],
            "context" => get(entry, "tactics", String[]),
            "tactic_proof" => get(entry, "tactic_proof", ""),
            "source" => get(entry, "source", "idris2"),
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
        "prover" => "Idris2",
        "total_proofs" => length(output_records),
        "extracted_from_source" => extracted_count,
        "synthetic_added" => length(output_records) - extracted_count,
        "id_range" => [START_ID, current_id - 1],
    )
    open(STATS_FILE, "w") do fh
        write(fh, JSON3.write(stats))
    end

    println("\n[Idris2] COMPLETE: $(length(output_records)) proofs written to $OUTPUT_FILE")
    return extracted_count, length(output_records) - extracted_count
end

if abspath(PROGRAM_FILE) == @__FILE__
    run()
end
