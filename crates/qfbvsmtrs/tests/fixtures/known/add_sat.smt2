; EXPECT: sat
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= (bvadd x #x01) #x2b))
(check-sat)
