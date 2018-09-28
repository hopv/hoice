(set-option :produce-proofs true)

(set-logic HORN)

(declare-fun useless (Int Int) Bool)
(declare-fun mc_91_out (Int Int) Bool)

(assert
  (forall ((n Int) (m Int))
    (=>
      (and
        (> n 100)
      )
      (useless n m)
    )
  )
)

(assert
  (forall ((n Int) (m Int))
    (=>
      (useless n m)
      (mc_91_out n (- n 10))
    )
  )
)

(assert
  (forall ( (n Int) (tmp Int) (res Int) )
    (=>
      (and (<= n 100) (mc_91_out (+ n 11) tmp) (mc_91_out tmp res))
      (mc_91_out n tmp)
    )
  )
)
(assert
  (forall ( (m Int) (res Int) )
    (=>
      (and (<= m 101) (mc_91_out m res))
      (<= res 100)
    )
  )
)

(check-sat)
(get-proof)