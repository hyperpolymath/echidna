; ECHIDNA SMT-LIB corpus adapter mini fixture.
(set-logic QF_LIA)
(set-info :source "echidna-corpus-test")
(set-info :status sat)

(declare-const x Int)
(declare-const y Int)

(define-fun double ((n Int)) Int (+ n n))

(assert (> x 0))
(assert (! (= (double x) y) :named y_is_double_x))

(check-sat)
(get-model)
(exit)
