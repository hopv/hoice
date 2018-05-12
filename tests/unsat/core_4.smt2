(set-option :produce-unsat-cores true)

(set-logic HORN)

(declare-fun blah (Int) Bool)

(assert
  (forall ((n Int))
    (=> (>= n 0) (blah n))
  )
)

(assert
  (forall ((n Int))
    (=> (blah n) false)
  )
)

(check-sat)

(get-unsat-core)
