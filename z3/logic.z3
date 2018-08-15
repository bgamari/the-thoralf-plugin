
(declare-const x Int)
(declare-const y Int)

(declare-const a Bool)

;(assert (or (= x y) false))

(assert (not (= (or a false) a) ) )


(check-sat)










