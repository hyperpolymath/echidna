(set-logic LIA)
(assert (not (forall ((x Int)) (exists ((y Int)) (> y x)))))
(check-sat)
