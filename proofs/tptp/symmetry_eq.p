%-----------------------------------------------------------------------------
% SPDX-License-Identifier: MPL-2.0
% File     : symmetry_eq.p
% Status   : Theorem
% Claim    : Equality is symmetric: a=b → b=a (follows from equality axioms).
%-----------------------------------------------------------------------------
fof(h, axiom, a = b).
fof(goal, conjecture, b = a).
