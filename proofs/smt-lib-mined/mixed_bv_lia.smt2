(set-logic QF_BV)
(declare-const x (_ BitVec 16))
(assert (not (= (bvadd x (_ bv0 16)) x)))
(check-sat)
