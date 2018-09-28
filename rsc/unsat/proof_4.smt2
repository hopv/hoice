(set-option :produce-proofs true)

(set-logic HORN)

(declare-fun useless (Int Int) Bool)
(declare-fun useless_2 (Int Int) Bool)
(declare-fun useless_3 (Int Int) Bool)
(declare-fun mc_91_out (Int Int) Bool)

(assert
  (forall ((n Int) (m Int))
    (=>
      (and
        (> n 100)
        (> m 7)
        (<= m (+ n 2))
      )
      (useless n m)
    )
  )
)

(assert
  (forall ((n Int) (m Int))
    (=>
      (and
        (> m 9)
        (< m 100000)
        (useless n m)
      )
      (useless_2 n m)
    )
  )
)

(assert
  (forall ((n Int) (m Int))
    (=>
      (and
        (> m 2)
        (useless n m)
      )
      (useless_3 n m)
    )
  )
)

(assert
  (forall ((n Int) (m_1 Int) (m_2 Int))
    (=>
      (and
        (useless_3 n m_1)
        (useless_2 n m_2)
        (<= m_1 (+ n 2))
        (<= m_2 (+ n 2))
      )
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
