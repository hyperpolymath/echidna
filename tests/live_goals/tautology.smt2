(set-logic QF_LIA)
(declare-const x Int)
; Negation of a tautology (x = 0 ∨ x ≠ 0) — UNSAT means the tautology holds,
; which is what ECHIDNA's verify_proof reports as "verified".
(assert (not (or (= x 0) (not (= x 0)))))
(check-sat)
