%-----------------------------------------------------------------------------
% SPDX-License-Identifier: PMPL-1.0-or-later
% File     : symmetry_eq.p
% Status   : Theorem
% Claim    : Equality is symmetric: a=b → b=a (follows from equality axioms).
%-----------------------------------------------------------------------------
fof(h, axiom, a = b).
fof(goal, conjecture, b = a).
