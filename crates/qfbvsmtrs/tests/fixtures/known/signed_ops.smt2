; EXPECT: sat
(set-logic QF_BV)
(assert (= (bvsdiv #b1001 #b0011) #b1110))
(assert (= (bvsrem #b1001 #b0011) #b1111))
(assert (= (bvsmod #b1011 #b0010) #b0001))
(check-sat)
