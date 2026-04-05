%-----------------------------------------------------------------------------
% SPDX-License-Identifier: PMPL-1.0-or-later
% File     : modus_ponens.p
% Syntax   : TPTP FOF (First-Order Form)
% Status   : Theorem
% Claim    : Modus ponens: from P and P→Q, conclude Q.
%-----------------------------------------------------------------------------
fof(p,        axiom,    p).
fof(p_imp_q,  axiom,    p => q).
fof(goal,     conjecture, q).
