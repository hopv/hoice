(declare-fun p_1 (Int Int Int Int) Bool)
(declare-fun p_2 (Int) Bool)

(assert
  (forall
    ( (A Int) (B Int) (C Int) (D Int) )
    (=> (> A 3) (p_1 A B C D))
  )
)
(assert
  (forall
    ( (A Int) (B Int) (C Int) (D Int) )
    (=> (and (p_1 A B C D) (<= A 3)) (p_2 C))
  )
)
(assert
  (forall
    ( (C Int) )
    (=> (p_2 C) (= C 1))
  )
)

(check-sat)

(get-model)