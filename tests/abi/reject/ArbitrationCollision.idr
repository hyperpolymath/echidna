-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

||| Reject fixture: a synonym collision (two kernel translations of
||| different terms) must not type-check as Sound. Identical to
||| ../accept/ArbitrationAligned.idr except for the second hash: no single
||| `h` satisfies both `MkKernelAt Refl` proofs, so `Sound` is refused.
module ArbitrationCollision

import EchidnaABI.Arbitration
import Data.List
import Data.List.Quantifiers

%default total

fusedPair : List (Fidelity Bool)
fusedPair = [ KernelTranslation Dedukti "lean4" True
            , KernelTranslation Dedukti "metamath" False ]

verdict : Level ArbitrationCollision.fusedPair
verdict = Sound True IsNonEmpty [MkKernelAt Refl, MkKernelAt Refl]
