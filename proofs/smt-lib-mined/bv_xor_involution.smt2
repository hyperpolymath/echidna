(set-logic QF_BV)
(declare-const x (_ BitVec 32)) (declare-const y (_ BitVec 32))
(assert (not (= (bvxor (bvxor x y) y) x)))
(check-sat)
