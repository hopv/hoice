(set-logic HORN)

(set-option :produce-proofs true)
(set-option :produce-unsat-cores true)

(declare-fun mc_91_in (Int) Bool)
(declare-fun mc_91_out (Int Int) Bool)

(assert
  (! (forall ((m Int))
    (=> true (mc_91_in m))
  ) :named a_1)
)

(assert
  (! (forall ((n Int))
    (=>
      (and (mc_91_in n) (<= n 100))
      (mc_91_in (+ n 11))
    )
  ) :named a_2)
)

(assert
  (! (forall ( (n Int) (tmp Int) (res Int) )
    (=>
      (and
        (mc_91_in n)
        (<= n 100)
        (mc_91_out (+ n 11) tmp)
      )
      (mc_91_in tmp)
    )
  ) :named a_3)
)

(assert
  (! (forall ((n Int))
    (=>
      (and (mc_91_in n) (> n 100))
      (mc_91_out n (- n 10))
    )
  ) :named a_4)
)

(assert
  (! (forall ( (n Int) (tmp Int) (res Int) )
    (=>
      (and
        (mc_91_in n)
        (<= n 100)
        (mc_91_out (+ n 11) tmp)
        (mc_91_out tmp res)
      )
      (mc_91_out n tmp)
    )
  ) :named a_5)
)

(assert
  (! (forall ( (m Int) (res Int) )
    (=>
      (and (<= m 101) (mc_91_in m) (mc_91_out m res))
      (<= res 100)
    )
  ) :named a_6)
)

(check-sat)

(get-unsat-core)
(get-proof)
