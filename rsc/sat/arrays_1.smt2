(declare-fun pred ( (Array Int Int) ) Bool)

(assert
  (forall ( (n Int) )
    (=>
      (>= n 0)
      (pred ((as const (Array Int Int)) n))
    )
  )
)

(assert
  (forall ( (idx Int) (array (Array Int Int)) )
    (=>
      (and (<= 0 idx) (<= idx 7) (pred array))
      (>= (select array idx) 0)
    )
  )
)

(check-sat)

(get-model)