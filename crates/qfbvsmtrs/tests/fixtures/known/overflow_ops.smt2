; EXPECT: sat
(set-logic QF_BV)
(assert (bvuaddo #b1111 #b0001))
(assert (bvsaddo #b0111 #b0001))
(assert (bvusubo #x00 #x01))
(assert (bvnego #b1000))
(assert (bvsdivo #b1000 #b1111))
(check-sat)
