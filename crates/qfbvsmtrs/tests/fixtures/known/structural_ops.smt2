; EXPECT: sat
(set-logic QF_BV)
(assert (= (concat ((_ extract 3 2) #b1101) ((_ zero_extend 1) #b01)) #b11001))
(assert (= ((_ sign_extend 3) #b101) #b111101))
(check-sat)
