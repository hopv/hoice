(declare-fun p (Real) Bool)

(assert
  (forall ( (x Real) )
    (=>
      (and
        (p x)
        (= (+ x (/ 2 0)) (/ 1 1))
      )
      false
    )
  )
)