(set-logic HORN)

(set-option :produce-proofs true)
(set-option :produce-unsat-cores true)

(declare-fun mc_91_out (Int Int) Bool)

(assert
  (! (forall ((n Int))
    (=>
      (> n 100)
      (mc_91_out n (- n 10))
    )
  ) :named a_1)
)
(assert
  (! (forall ( (n Int) (tmp Int) (res Int) )
    (=>
      (and (<= n 100) (mc_91_out (+ n 11) tmp) (mc_91_out tmp res))
      (mc_91_out n tmp)
    )
  ) :named a_2)
)
(assert
  (! (forall ( (n Int) )
    (=>
      (< n 0)
      (>= n 0)
    )
  ) :named dumb_unsat_clause)
)
(assert
  (! (forall ( (m Int) (res Int) )
    (=>
      (and (<= m 101) (mc_91_out m res))
      (<= res 100)
    )
  ) :named a_3)
)

(check-sat)

(get-unsat-core)
(get-proof)
