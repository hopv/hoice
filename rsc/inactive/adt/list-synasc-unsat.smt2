(set-logic HORN)

(declare-fun Concat ((List Int) (List Int) (List Int)) Bool)

(assert (forall ((y (List Int)))
           (Concat nil y y)))

(assert (forall ((x (List Int))(y (List Int))(r (List Int))(i Int))
           (=> (Concat x y r) (Concat (Cons i x) y (Cons i r)) )))

(assert (forall ((x (List Int))(y (List Int))(r (List Int))(i Int))
           (=> (Concat x y r) (Concat x y (Cons i r)) )))

(assert (forall ((x (List Int))(y (List Int))(r (List Int)))
           (=> (and (not (= r nil)) (Concat x y r)) (or (= (head r) (head x)) (= (head r) (head y)) ))))

(assert (forall ((x (List Int))(y (List Int))(r (List Int))(nx Int)(ny Int)(nr Int))
           (=> (and (Concat x y r) (= nx (_size x)) (= ny (_size y)) (= nr (_size r))) (= (+ nr 1) (+ nx ny)))))

(check-sat)
