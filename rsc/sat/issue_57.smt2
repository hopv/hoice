(set-logic HORN)

(declare-fun
  main@_6
  ( Int Int Int ) Bool
)
(declare-fun
  main@.preheader
  ( Int Int Int Int ) Bool
)
(declare-fun
  main@.lr.ph
  ( Int Int ) Bool
)

(assert 
  (forall
    ( (A Int) (C Int) (I Int) (J Int) )
    (=>
      (and
        (>= (+ C (* (- 1) J)) 0) (>= (+ I (* (- 1) A)) 1)
        (main@.preheader C A I J)
      )
      (main@.preheader (+ C (- 1)) (+ A 1) I J)
    )
  )
)

(assert 
  (forall
    ( (H Int) (I Int) )
    (=>
      (and
        true
        true
      )
      (main@_6 0 H I)
    )
  )
)

(assert 
  (forall
    ( (A Int) (B Int) (D Int) )
    (=>
      (and
        (not (= D 0))
        (main@.lr.ph A B)
      )
      (main@.lr.ph (+ A 1) (+ B 1))
    )
  )
)

(assert 
  (forall
    ( (B Int) (C Int) (L Int) (M Int) )
    (=>
      (and
        (not (= B 0))
        (main@_6 C L M)
      )
      (main@_6 (+ C 1) L M)
    )
  )
)

(assert 
  (forall
    ( (B Int) (C Int) (D Int) )
    (=>
      (and
        (or (>= (+ C (* (- 1) B)) 1) (>= (+ D (* (- 1) C)) 0))
        (main@_6 C B D)
      )
      (main@.preheader 0 0 (- 1) 1)
    )
  )
)

(assert 
  (forall
    ( (A Int) (B Int) (C Int) (H Int) )
    (=>
      (and
        (or (>= (+ B (* (- 1) A)) 1) (>= (+ C (* (- 1) B)) 0)) (not (= H 0))
        (main@_6 B A C)
      )
      (main@.lr.ph 0 0)
    )
  )
)
(assert 
  (forall
    ( (A Int) (C Int) (D Int) (G Int) )
    (=>
      (and
        (>= (+ G (* (- 1) A)) 2) (>= (+ D (* (- 1) C)) 1)
        (main@.preheader (+ A 1) C D G)
      )
      false
    )
  )
)
(assert 
  (forall
    ( (B Int) (I Int) )
    (=>
      (and
        true
        (main@.lr.ph I B)
      )
      (main@.preheader (+ B 1) 0 I 1)
    )
  )
)
(check-sat)
