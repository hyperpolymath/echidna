(set-logic QF_LIA)
(declare-const x Int) (declare-const y Int)
(assert (> x y)) (assert (> y x))
(check-sat)
