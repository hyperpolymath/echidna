%-----------------------------------------------------------------------------
% SPDX-License-Identifier: AGPL-3.0-or-later
% File     : double_negation.p
% Status   : Theorem
% Claim    : ¬¬P → P (classical double-negation elimination).
%-----------------------------------------------------------------------------
fof(not_not_p, axiom, ~ ~ p).
fof(goal,      conjecture, p).
