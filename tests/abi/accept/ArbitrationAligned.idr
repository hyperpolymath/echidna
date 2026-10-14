-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

||| Accept fixture (positive control for ../reject/ArbitrationCollision.idr):
||| two kernel translations of one term can be typed Sound. The reject
||| fixture is this file with the second hash changed.
module ArbitrationAligned

import EchidnaABI.Arbitration
import Data.List
import Data.List.Quantifiers

%default total

fusedPair : List (Fidelity Bool)
fusedPair = [ KernelTranslation Dedukti "lean4" True
            , KernelTranslation Dedukti "metamath" True ]

verdict : Level ArbitrationAligned.fusedPair
verdict = Sound True IsNonEmpty [MkKernelAt Refl, MkKernelAt Refl]
