(set-logic QF_NRA)
(declare-const x Real)
(assert (< (* x x) 0.0))
(check-sat)
