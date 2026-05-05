; EXPECT: unsat
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(assert (= x #x1))
(assert (= x #x2))
(check-sat)
