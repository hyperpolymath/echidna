(set-logic QF_LIA)
(declare-const x Int)
; Satisfiable assertion — SAT, so verify_proof reports "not verified".
(assert (= x 1))
(check-sat)
