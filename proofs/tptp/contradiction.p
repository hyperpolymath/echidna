%-----------------------------------------------------------------------------
% SPDX-License-Identifier: MPL-2.0
% File     : contradiction.p
% Status   : CounterSatisfiable
% Claim    : Deliberately unprovable: asserting P and ¬P.
%            ATPs should report CounterSatisfiable (or Unsatisfiable of the
%            axioms, depending on mode) — any answer other than "Theorem"
%            is correct.
%-----------------------------------------------------------------------------
fof(p,     axiom, p).
fof(not_p, axiom, ~ p).
fof(goal,  conjecture, q).
