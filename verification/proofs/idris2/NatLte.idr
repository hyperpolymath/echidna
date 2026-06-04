-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- NatLte.idr — machine-checked `LTE` for literal Nats.
--
-- Order facts like `LTE 4 5` were previously written as hand-counted Peano
-- towers `LTESucc (LTESucc (... LTEZero))`.  That representation silently
-- mis-counts (off-by-one between the source and target index) and is
-- unreviewable for large bounds.  `lteLit m n` instead runs the `Data.Nat`
-- decision procedure, so the witness is computed: it type-checks iff
-- `m <= n` actually holds, and the count can never be wrong.

module NatLte

import Data.Nat

||| Inhabited exactly when a decision landed in the `Yes` branch.
public export
0 IsYes : Dec p -> Type
IsYes (Yes _) = ()
IsYes (No  _) = Void

||| Extract the witness from a `Yes` decision; the `No` branch is ruled out
||| by `IsYes` being `Void` there.
public export
fromYes : (d : Dec p) -> IsYes d -> p
fromYes (Yes pf) _ = pf
fromYes (No  _)  v = absurd v

||| Machine-checked `LTE` for literal Nats.  `lteLit m n` elaborates to the
||| witness computed by `isLTE m n`; it compiles iff `m <= n` is true.
public export
lteLit : (m : Nat) -> (n : Nat) -> {auto ok : IsYes (isLTE m n)} -> LTE m n
lteLit m n = fromYes (isLTE m n) ok
