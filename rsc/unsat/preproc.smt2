(set-logic HORN)

(assert
  (not (exists ( (|$knormal:1| Int) (|$knormal:2| Int) )
    ( and (= (not (= 0 |$knormal:2|)) (= |$knormal:1| 1)) (= (not (= 0 |$knormal:1|)) true) (not (not (= 0 |$knormal:2|))) )
    )
  )
)
(check-sat)

(exit)