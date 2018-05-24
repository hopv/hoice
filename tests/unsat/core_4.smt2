
(set-option :produce-proofs true)
(set-option :produce-unsat-cores true)

(set-logic HORN)

(declare-fun blah (Int) Bool)

(assert
  (! (forall ((n Int))
    (=> (>= n 0) (blah n))
  ) :named a_1)
)

(assert
  (! (forall ((n Int))
    (=> (blah n) false)
  ) :named a_2)
)

(check-sat)

(get-unsat-core)
(get-proof)