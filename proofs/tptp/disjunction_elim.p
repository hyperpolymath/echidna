%-----------------------------------------------------------------------------
% SPDX-License-Identifier: MPL-2.0
% File     : disjunction_elim.p
% Status   : Theorem
% Claim    : Disjunction elimination — from P∨Q, P→R, Q→R, conclude R.
%-----------------------------------------------------------------------------
fof(p_or_q, axiom, p | q).
fof(p_imp,  axiom, p => r).
fof(q_imp,  axiom, q => r).
fof(goal,   conjecture, r).
