%-----------------------------------------------------------------------------
% SPDX-License-Identifier: PMPL-1.0-or-later
% File     : socrates.p
% Status   : Theorem
% Claim    : Classical syllogism: all humans are mortal; Socrates is human;
%            therefore Socrates is mortal.
%-----------------------------------------------------------------------------
fof(all_humans_mortal, axiom,
    ! [X] : (human(X) => mortal(X)) ).
fof(socrates_is_human, axiom, human(socrates)).
fof(goal, conjecture, mortal(socrates)).
