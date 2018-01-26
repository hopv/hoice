(declare-fun p (Int Int) Bool)

(assert
  (forall ((a Int) (b Int))
    (=>
      (p a b)
      ( let ( (n 2) ) (> a n) )
    )
  )
)

(assert
  (let ( (n 7) (m (* (- 1) 7)) )
    (forall ((a Int) (b Int))
      (=>
        (and (> a 0) (< b n))
        (p a b)
      )
    )
  )
)

(assert
  (forall ((a Int) (b Int))
    (let ( (n (- 2)) )
      (=>
        (p a b)
        (< b n)
      )
    )
  )
)

(assert
  (not
    (let ((n 3))
      (exists ((a Int) (b Int))
        (and
          (p b a)
          (< a (+ b n))
        )
      )
    )
  )
)

(check-sat)

(exit)