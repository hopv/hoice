(declare-fun p (Int Int) Bool)

(assert
  (forall ((a Int) (b Int))
    (not
      (and
        (p a b)
        ( let ( (n 2) ) (> a n) )
      )
    )
  )
)

(assert
  (let ( (n 7) )
    (forall ((a Int) (b Int))
      (not
        (and
          (and (> a 0) (< b n))
          (not (p a b))
        )
      )
    )
  )
)

(assert
  (not (exists ((a Int) (b Int))
    (let ( (n (- 2)) )
        (or
          (p a b)
          (< b n)
        )
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