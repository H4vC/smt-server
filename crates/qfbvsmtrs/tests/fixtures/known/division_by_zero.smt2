; EXPECT: sat
(set-logic QF_BV)
(assert (= (bvudiv #x07 #x00) #xff))
(assert (= (bvurem #x07 #x00) #x07))
(check-sat)
