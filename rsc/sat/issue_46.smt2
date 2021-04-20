(set-logic HORN)

(declare-fun main (Bool) Bool)
(declare-fun go (Int Int Bool) Bool)
(declare-fun go2 (Int Bool) Bool)

(assert (forall ((r Bool)) (=> (go 0 0 r) (main r))))
(assert (forall ((r Bool)) (=> (go 1 1 r) (main r))))
(assert (forall ((n Int)) (go n 0 true)))
(assert (forall ((n Int) (m Int) (r Bool))
  (=> (and (not (= m 0)) (go2 n r)) (go n m r))))
(assert (forall ((n Int)) (go2 1 true)))
(assert (forall ((n Int)) (=> (not (= n 1)) (go2 n false))))

(assert (forall ((r Bool)) (=> (main r) r)))
(check-sat)
