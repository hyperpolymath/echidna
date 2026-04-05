%-----------------------------------------------------------------------------
% SPDX-License-Identifier: PMPL-1.0-or-later
% File     : group_left_identity.p
% Status   : Theorem
% Claim    : In a group, e is also a right identity (proved from left-identity
%            + left-inverse axioms — a classical group-theory exercise).
%-----------------------------------------------------------------------------
fof(left_id,      axiom, ! [X] : mult(e, X) = X).
fof(left_inv,     axiom, ! [X] : mult(inv(X), X) = e).
fof(assoc,        axiom,
    ! [X,Y,Z] : mult(X, mult(Y, Z)) = mult(mult(X, Y), Z) ).
fof(right_id_goal, conjecture, ! [X] : mult(X, e) = X).
