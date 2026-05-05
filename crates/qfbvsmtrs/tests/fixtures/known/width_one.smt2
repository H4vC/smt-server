; EXPECT: sat
(set-logic QF_BV)
(assert (= (bvadd #b1 #b1) #b0))
(assert (= (bvudiv #b0 #b0) #b1))
(assert (= ((_ sign_extend 7) #b1) #xff))
(check-sat)
