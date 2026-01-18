; Simple SMT-LIB example for ECHIDNA CVC5 backend
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (> x 0))
(assert (> y 0))
(assert (= (+ x y) 10))
(assert (< x y))
(check-sat)
