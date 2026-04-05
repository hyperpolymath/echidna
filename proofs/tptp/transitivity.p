%-----------------------------------------------------------------------------
% SPDX-License-Identifier: PMPL-1.0-or-later
% File     : transitivity.p
% Status   : Theorem
% Claim    : Less-than is transitive: a<b ∧ b<c → a<c.
%-----------------------------------------------------------------------------
fof(trans, axiom,
    ! [X,Y,Z] : ((lt(X,Y) & lt(Y,Z)) => lt(X,Z)) ).
fof(h1, axiom, lt(a,b)).
fof(h2, axiom, lt(b,c)).
fof(goal, conjecture, lt(a,c)).
