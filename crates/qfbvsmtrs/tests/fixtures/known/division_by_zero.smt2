; EXPECT: sat
(set-logic QF_BV)
(declare-fun a () (_ BitVec 2))
(assert (= (bvudiv #x07 #x00) #xff))
(assert (= (bvurem #x07 #x00) #x07))
(assert (= (bvudiv #b00 a) #b11))
(assert (= (bvudiv a a) #b11))
(check-sat)
