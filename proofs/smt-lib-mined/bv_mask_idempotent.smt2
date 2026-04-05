(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (not (= (bvand x x) x)))
(check-sat)
