%--------------------------------------------------------------------
% File     : mini.p
% Problem  : MINI001+1
% Domain   : Mini-test for the ECHIDNA TPTP corpus adapter.
% English  : Commutativity of a constant pair.
% Status   : Theorem
%--------------------------------------------------------------------
include('Axioms/EQU001+0.ax').

%---- Axioms ----
fof(comm_axiom, axiom,
    ! [X, Y] : mult(X, Y) = mult(Y, X) ).

fof(assoc_hyp, hypothesis,
    ! [X, Y, Z] : mult(mult(X, Y), Z) = mult(X, mult(Y, Z)) ).

%---- Conjecture ----
fof(swap_goal, conjecture,
    mult(a, b) = mult(b, a) ).
%--------------------------------------------------------------------
