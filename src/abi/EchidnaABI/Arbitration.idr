-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

||| ECHIDNA ABI — Arbitration fidelity levels (ECH-05)
|||
||| The Idris2 statement of the level an arbitrated verdict carries for
||| the source claim. Rust mirror: `FidelityEvidence`, `EpistemicLevel`
||| and `fidelity_level` in `src/rust/verification/result_arbiter.rs`.
|||
||| `Level fused` is a closed sum indexed by the evidence of the fused
||| attempts. Its `Sound` constructor takes, for every fused attempt, a
||| proof that the attempt is a kernel-checked translation whose term
||| hash equals the shared hash `h`. A `Sound` value therefore cannot be
||| built for a list holding two different term hashes (a synonym
||| collision), a declared correspondence, or no evidence — whatever
||| produced it. `level` is the classifier. The Rust `fidelity_level`
||| implements the same policy; that correspondence is by review, not
||| mechanically checked.
|||
||| The module is parametric in the hash type and needs only `DecEq` on
||| it. The runtime hash is the BLAKE3 hex digest from
||| `src/rust/exchange/mod.rs::term_hash`; the examples below use `Bool`
||| as a two-point hash space so that distinctness is constructive.
|||
||| Proves:
|||   1. kernelAtHash: a KernelAt witness yields the hash equality
|||   2. collisionNotSound: two fused kernel translations with different
|||      hashes make every `Level fused` non-Sound
|||   3. correspondenceNotSound / noEvidenceNotSound: such evidence in
|||      the fused list makes every `Level fused` non-Sound
|||   4. blockedIsBelief: review or retraction caps `level` at Belief
|||   5. noEvidenceIsBelief: an attempt without evidence caps `level` at
|||      Belief, fused or not
|||   6. failedCorrespondenceIsBelief / untestedCorrespondenceIsBelief
|||   7. emptyFusedIsBelief, blockingNeverRaises
|||   8. alignedPairIsSound / collisionPairIsBelief / mixedPairIsEpi
|||      (positive and negative controls, by evaluation)
|||
||| Correspondence, not import: the levels follow epistemic-types
||| `EpistemicTypes.Warrant` (`Warrant`, `Epi`, `SoundWarrant`,
||| `sound-epi`) and `no-receipt-reflection`
||| (`EpistemicTypes.Applications.RapidNJSkip`) at pin 6a68de3; retraction
||| follows residual-evidence-types `ResidualEvidence.Revision`
||| (`retract-case`, `dependent-holds`) at pin 97244f5. Nothing here is
||| proved about those Agda developments; they are cited, not consumed.
|||
||| NO believe-me, NO postulates, NO admits.

module EchidnaABI.Arbitration

import Data.List
import Data.Nat
import Data.List.Elem
import Data.List.Quantifiers
import Decidable.Equality

%default total

------------------------------------------------------------------------
-- Evidence
------------------------------------------------------------------------

||| Exchange-layer formats, one per bridge in `src/rust/exchange/`.
public export
data ExchangeFormat = OpenTheory | Dedukti | Lambdapi | Tptp | SmtLib | SmtCoq

||| Evidence that a backend's formal statement denotes the source claim.
public export
data Fidelity : (hash : Type) -> Type where
  ||| Translated through the exchange layer and checked by a kernel;
  ||| `termHash` names the exchange-layer term.
  KernelTranslation : (format : ExchangeFormat) -> (checkedBy : String) ->
                      (termHash : hash) -> Fidelity hash
  ||| A declared correspondence checked by consequence testing.
  DeclaredCorrespondence : (consequenceTests : Nat) -> (failures : Nat) ->
                           Fidelity hash
  ||| No evidence beyond the goal handed to the backend.
  NoEvidence : Fidelity hash

||| `KernelAt h e`: `e` is a kernel translation whose term hash is `h`.
||| The constructor carries the hash-equality proof.
public export
data KernelAt : hash -> Fidelity hash -> Type where
  MkKernelAt : (hashEq : h' = h) -> KernelAt h (KernelTranslation f c h')

||| Projection of the hash equality.
export
kernelAtHash : KernelAt h (KernelTranslation f c h') -> h' = h
kernelAtHash (MkKernelAt hashEq) = hashEq

export
noKernelAtCorrespondence : KernelAt h (DeclaredCorrespondence t k) -> Void
noKernelAtCorrespondence (MkKernelAt _) impossible

export
noKernelAtNoEvidence : KernelAt h NoEvidence -> Void
noKernelAtNoEvidence (MkKernelAt _) impossible

------------------------------------------------------------------------
-- The three-level verdict
------------------------------------------------------------------------

||| The level of an arbitrated verdict, indexed by the evidence of the
||| attempts that were fused into it.
public export
data Level : List (Fidelity hash) -> Type where
  ||| Agreement without a fidelity map to the source claim.
  Belief : Level fused
  ||| Every fused attempt has fidelity evidence, not all of it kernel.
  Epi    : Level fused
  ||| Every fused attempt is a kernel translation to the term `h`.
  Sound  : (h : hash) -> NonEmpty fused -> All (KernelAt h) fused ->
           Level fused

||| Belief < Epi < Sound.
public export
rank : Level fused -> Nat
rank Belief        = 0
rank Epi           = 1
rank (Sound _ _ _) = 2

public export
isSound : Level fused -> Bool
isSound (Sound _ _ _) = True
isSound _             = False

------------------------------------------------------------------------
-- Sound is closed under the type
------------------------------------------------------------------------

elemAll : Elem x xs -> All p xs -> p x
elemAll Here      (px :: _)   = px
elemAll (There e) (_  :: pxs) = elemAll e pxs

||| A synonym collision cannot be typed Sound: if two fused attempts are
||| kernel translations to different terms, no `Level fused` is Sound.
export
collisionNotSound : Elem (KernelTranslation f1 c1 h1) fused ->
                    Elem (KernelTranslation f2 c2 h2) fused ->
                    Not (h1 = h2) ->
                    (l : Level fused) -> isSound l = False
collisionNotSound _  _  _   Belief = Refl
collisionNotSound _  _  _   Epi    = Refl
collisionNotSound e1 e2 neq (Sound _ _ allK) =
  void (neq (trans (kernelAtHash (elemAll e1 allK))
                   (sym (kernelAtHash (elemAll e2 allK)))))

||| A fused declared correspondence rules out Sound.
export
correspondenceNotSound : Elem (DeclaredCorrespondence t k) fused ->
                         (l : Level fused) -> isSound l = False
correspondenceNotSound _ Belief = Refl
correspondenceNotSound _ Epi    = Refl
correspondenceNotSound e (Sound _ _ allK) =
  void (noKernelAtCorrespondence (elemAll e allK))

||| A fused attempt without evidence rules out Sound.
export
noEvidenceNotSound : Elem NoEvidence fused ->
                     (l : Level fused) -> isSound l = False
noEvidenceNotSound _ Belief = Refl
noEvidenceNotSound _ Epi    = Refl
noEvidenceNotSound e (Sound _ _ allK) =
  void (noKernelAtNoEvidence (elemAll e allK))

------------------------------------------------------------------------
-- The classifier
------------------------------------------------------------------------

||| True when no attempt lacks evidence.
public export
allEvidenced : List (Fidelity hash) -> Bool
allEvidenced []                                  = True
allEvidenced (NoEvidence :: _)                   = False
allEvidenced (KernelTranslation _ _ _ :: es)     = allEvidenced es
allEvidenced (DeclaredCorrespondence _ _ :: es)  = allEvidenced es

||| A correspondence counts with at least one test and no failures.
public export
correspondenceOk : (tests : Nat) -> (failures : Nat) -> Bool
correspondenceOk (S _) Z = True
correspondenceOk _     _ = False

||| True when every item is a kernel translation or an accepted
||| correspondence.
public export
allWarranted : List (Fidelity hash) -> Bool
allWarranted []                                 = True
allWarranted (NoEvidence :: _)                  = False
allWarranted (KernelTranslation _ _ _ :: es)    = allWarranted es
allWarranted (DeclaredCorrespondence t k :: es) =
  if correspondenceOk t k then allWarranted es else False

||| The term hashes of the kernel translations, in order.
public export
kernelHashes : List (Fidelity hash) -> List hash
kernelHashes []                                 = []
kernelHashes (KernelTranslation _ _ h :: es)    = h :: kernelHashes es
kernelHashes (DeclaredCorrespondence _ _ :: es) = kernelHashes es
kernelHashes (NoEvidence :: es)                 = kernelHashes es

public export
allEqualTo : DecEq a => a -> List a -> Bool
allEqualTo _ []        = True
allEqualTo x (y :: ys) = case decEq x y of
  Yes _ => allEqualTo x ys
  No _  => False

public export
allEqual : DecEq a => List a -> Bool
allEqual []        = True
allEqual (x :: xs) = allEqualTo x xs

allHead : All p (x :: xs) -> p x
allHead (px :: _) = px

allTail : All p (x :: xs) -> All p xs
allTail (_ :: pxs) = pxs

public export
decAll : ((x : a) -> Dec (p x)) -> (xs : List a) -> Dec (All p xs)
decAll _ []        = Yes []
decAll d (x :: xs) = case d x of
  No contra => No (contra . allHead)
  Yes px    => case decAll d xs of
    Yes pxs   => Yes (px :: pxs)
    No contra => No (contra . allTail)

notKernelAt : Not (h' = h) -> Not (KernelAt h (KernelTranslation f c h'))
notKernelAt contra (MkKernelAt hashEq) = contra hashEq

public export
decKernelAt : DecEq hash => (h : hash) -> (e : Fidelity hash) ->
              Dec (KernelAt h e)
decKernelAt h (KernelTranslation f c h') = case decEq h' h of
  Yes hashEq => Yes (MkKernelAt hashEq)
  No contra  => No (notKernelAt contra)
decKernelAt _ (DeclaredCorrespondence _ _) = No noKernelAtCorrespondence
decKernelAt _ NoEvidence                   = No noKernelAtNoEvidence

||| Sound when every item is a kernel translation to the first item's
||| term, Epi otherwise. Called only on warranted, hash-agreeing lists.
public export
soundOrEpi : DecEq hash => (fused : List (Fidelity hash)) -> Level fused
soundOrEpi [] = Belief
soundOrEpi fused@(KernelTranslation _ _ h :: _) =
  case decAll (decKernelAt h) fused of
    Yes allK => Sound h IsNonEmpty allK
    No _     => Epi
soundOrEpi (DeclaredCorrespondence _ _ :: _) = Epi
soundOrEpi (NoEvidence :: _)                 = Belief

||| Pass `l` through when the flag holds, Belief otherwise.
public export
gateOk : Bool -> Level fused -> Level fused
gateOk True  l = l
gateOk False _ = Belief

||| The level of the fused attempts alone.
public export
fusedLevel : DecEq hash => (fused : List (Fidelity hash)) -> Level fused
fusedLevel fused =
  gateOk (allWarranted fused)
    (gateOk (allEqual (kernelHashes fused)) (soundOrEpi fused))

||| The ECH-05 levelling policy. `attempts` is every attempt's evidence,
||| `fused` the evidence of the attempts fused into the verdict, and
||| `blocked` is set when the verdict needs review or rests on a
||| retracted backend. (The Rust side also rejects an empty hash string,
||| which the abstract hash type has no counterpart for.)
public export
level : DecEq hash => (attempts, fused : List (Fidelity hash)) ->
        (blocked : Bool) -> Level fused
level _        _     True  = Belief
level attempts fused False = gateOk (allEvidenced attempts) (fusedLevel fused)

------------------------------------------------------------------------
-- Classifier properties
------------------------------------------------------------------------

gateOkFalse : (b : Bool) -> b = False -> (l : Level fused) ->
              gateOk b l = Belief
gateOkFalse False Refl _ = Refl

gateOkBelief : (b : Bool) -> (l : Level fused) -> l = Belief ->
               gateOk b l = Belief
gateOkBelief True  _ prf = prf
gateOkBelief False _ _   = Refl

elemNoEvidence : (xs : List (Fidelity hash)) -> Elem NoEvidence xs ->
                 allEvidenced xs = False
elemNoEvidence (NoEvidence :: _) _ = Refl
elemNoEvidence (KernelTranslation _ _ _ :: es) (There e) =
  elemNoEvidence es e
elemNoEvidence (DeclaredCorrespondence _ _ :: es) (There e) =
  elemNoEvidence es e

||| A correspondence that is not accepted falsifies `allWarranted`.
elemBadCorrespondence : (xs : List (Fidelity hash)) ->
                        correspondenceOk t k = False ->
                        Elem (DeclaredCorrespondence t k) xs ->
                        allWarranted xs = False
elemBadCorrespondence (NoEvidence :: _) _ _ = Refl
elemBadCorrespondence (DeclaredCorrespondence _ _ :: _) bad Here =
  rewrite bad in Refl
elemBadCorrespondence (DeclaredCorrespondence t' k' :: es) bad (There e) with (correspondenceOk t' k')
  _ | True  = elemBadCorrespondence es bad e
  _ | False = Refl
elemBadCorrespondence (KernelTranslation _ _ _ :: es) bad (There e) =
  elemBadCorrespondence es bad e

||| A correspondence with a failed consequence test is never accepted.
failedNotOk : (t : Nat) -> correspondenceOk t (S k) = False
failedNotOk Z     = Refl
failedNotOk (S _) = Refl

||| (4) A verdict that needs review or rests on a retracted backend is
||| Belief.
export
blockedIsBelief : DecEq hash => (attempts, fused : List (Fidelity hash)) ->
                  level attempts fused True = Belief
blockedIsBelief _ _ = Refl

||| (5) One attempt without evidence anywhere in the input caps the level
||| at Belief.
export
noEvidenceIsBelief : DecEq hash => (attempts, fused : List (Fidelity hash)) ->
                     (blocked : Bool) -> Elem NoEvidence attempts ->
                     level attempts fused blocked = Belief
noEvidenceIsBelief _        _     True  _ = Refl
noEvidenceIsBelief attempts fused False e =
  gateOkFalse (allEvidenced attempts) (elemNoEvidence attempts e)
              (fusedLevel fused)

fusedBadCorrespondence : DecEq hash => (fused : List (Fidelity hash)) ->
                         correspondenceOk t k = False ->
                         Elem (DeclaredCorrespondence t k) fused ->
                         fusedLevel fused = Belief
fusedBadCorrespondence fused bad e =
  gateOkFalse (allWarranted fused) (elemBadCorrespondence fused bad e)
              (gateOk (allEqual (kernelHashes fused)) (soundOrEpi fused))

||| (6a) A fused correspondence with a failed consequence test is Belief.
export
failedCorrespondenceIsBelief :
  DecEq hash => {t : Nat} ->
  (attempts, fused : List (Fidelity hash)) -> (blocked : Bool) ->
  Elem (DeclaredCorrespondence t (S k)) fused ->
  level attempts fused blocked = Belief
failedCorrespondenceIsBelief _ _ True _ = Refl
failedCorrespondenceIsBelief {t} attempts fused False e =
  gateOkBelief (allEvidenced attempts) (fusedLevel fused)
               (fusedBadCorrespondence fused (failedNotOk t) e)

||| (6b) A fused correspondence with no consequence tests is Belief.
export
untestedCorrespondenceIsBelief :
  DecEq hash => (attempts, fused : List (Fidelity hash)) -> (blocked : Bool) ->
  Elem (DeclaredCorrespondence Z k) fused ->
  level attempts fused blocked = Belief
untestedCorrespondenceIsBelief _        _     True  _ = Refl
untestedCorrespondenceIsBelief attempts fused False e =
  gateOkBelief (allEvidenced attempts) (fusedLevel fused)
               (fusedBadCorrespondence fused Refl e)

||| (7a) Nothing fused, nothing warranted.
export
emptyFusedIsBelief : DecEq hash => (attempts : List (Fidelity hash)) ->
                     (blocked : Bool) ->
                     level attempts [] blocked = Belief
emptyFusedIsBelief _        True  = Refl
emptyFusedIsBelief attempts False =
  gateOkBelief (allEvidenced attempts) (fusedLevel []) Refl

||| (7b) Blocking (review, retraction) never raises the level.
export
blockingNeverRaises : DecEq hash => (attempts, fused : List (Fidelity hash)) ->
                      (blocked : Bool) ->
                      LTE (rank (level attempts fused True))
                          (rank (level attempts fused blocked))
blockingNeverRaises _ _ _ = LTEZero

------------------------------------------------------------------------
-- Controls, by evaluation (hash space Bool)
------------------------------------------------------------------------

||| Two kernel translations of one term (MiniF2F-style aligned pair).
public export
alignedPair : List (Fidelity Bool)
alignedPair = [ KernelTranslation Dedukti "lean4" True
              , KernelTranslation Dedukti "isabelle" True ]

||| Two kernel translations of different terms (synonym collision).
public export
collisionPair : List (Fidelity Bool)
collisionPair = [ KernelTranslation Dedukti "lean4" True
                , KernelTranslation Dedukti "metamath" False ]

||| A kernel translation and a tested, failure-free correspondence.
public export
mixedPair : List (Fidelity Bool)
mixedPair = [ KernelTranslation Dedukti "lean4" True
            , DeclaredCorrespondence 12 0 ]

export
alignedPairIsSound :
  isSound (level Arbitration.alignedPair Arbitration.alignedPair False) = True
alignedPairIsSound = Refl

export
collisionPairIsBelief :
  rank (level Arbitration.collisionPair Arbitration.collisionPair False) = 0
collisionPairIsBelief = Refl

export
mixedPairIsEpi :
  rank (level Arbitration.mixedPair Arbitration.mixedPair False) = 1
mixedPairIsEpi = Refl

trueNotFalse : Not (True = False)
trueNotFalse Refl impossible

||| The collision is ruled out by the type, not only by `level`.
export
collisionPairNeverSound :
  (l : Level Arbitration.collisionPair) -> isSound l = False
collisionPairNeverSound =
  collisionNotSound Here (There Here) trueNotFalse
