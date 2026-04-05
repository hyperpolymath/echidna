(set-logic QF_NIA)
(declare-const x Int) (declare-const y Int)
(assert (not (= (* x y) (* y x))))
(check-sat)
