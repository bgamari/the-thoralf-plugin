;(define-fun either ((m (Maybe Int)) (n (Maybe Int))) (Maybe Int)
;  (ite ((_ is nothing) n) nothing  m)
;)



(declare-datatypes ((Maybe 1)) ((par (T) ((just (fromJust T)) (nothing)))))

(declare-fun either ((Maybe Int) (Maybe Int)) (Maybe Int))
(assert (forall ((y (Maybe Int))) (= (either nothing y) y)))
(assert (forall ((x (Maybe Int)) (y (Maybe Int))) (=> ((_ is just) x) (= (either x y) x))))


(declare-fun both ((Maybe Int) (Maybe Int)) (Maybe Int))
(assert (forall ((y (Maybe Int))) (= (both y nothing) nothing)))
(assert (forall ((y (Maybe Int))) (= (both nothing y) nothing)))
(assert (forall ((x (Maybe Int)) (y (Maybe Int)))
  (=> (and ((_ is just) x) ((_ is just) y) ) (= (both x y) x))
  )
)





(declare-const x (Array Int (Maybe Int)))
(declare-const y (Array Int (Maybe Int)))
(declare-const z (Array Int (Maybe Int)))


;(assert (not  (=
;   ( (_ map either)  ((_ map either) x y) z  )
;   ( (_ map either)  x     ( (_ map either) y z )         )
;)))


;(assert (not  (=
;   ( (_ map both)  ((_ map both) x y) z  )
;   ( (_ map both)  x     ( (_ map both) y z )         )
;)))

(assert  (= (both ))
)




(check-sat)

