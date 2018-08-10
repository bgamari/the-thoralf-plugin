;(define-fun both ((m (Maybe Int)) (n (Maybe Int))) (Maybe Int)
;  (ite ((_ is nothing) n) nothing  m)
;)



(declare-datatypes ((Maybe 1)) ((par (T) ((just (fromJust T)) (nothing)))))

(declare-fun combine ((Maybe Int) (Maybe Int)) (Maybe Int))
(assert (forall ((y (Maybe Int))) (= (combine nothing y) y)))
(assert (forall ((x (Maybe Int)) (y (Maybe Int))) (=> ((_ is just) x) (= (combine x y) x))))


(declare-const x (Array Int (Maybe Int)))
(declare-const y (Array Int (Maybe Int)))
(declare-const z (Array Int (Maybe Int)))

(declare-const q (Array Int (Maybe Int)))


;(assert (=
;   (_ map combine  (_ map  combine x y) z)
;  (_ map combine x (_ map combine y z))
;  q
;))


(assert (not  (=
   ( (_ map combine)  ((_ map combine) x y) z  )

   ( (_ map combine)  x     ( (_ map combine) y z )         )

)))



(check-sat)

