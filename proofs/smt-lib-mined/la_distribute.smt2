(set-logic QF_NIA)
(declare-const a Int) (declare-const b Int) (declare-const c Int)
(assert (not (= (* a (+ b c)) (+ (* a b) (* a c)))))
(check-sat)
