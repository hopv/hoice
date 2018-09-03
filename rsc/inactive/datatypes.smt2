(declare-datatypes (T1 T2) (
  (Pair (mk-pair (first T1) (second T2)))
) )
(declare-datatypes (T1 T2) (
  (Pair2 (mk-pair-2 (first (Pair T1 T2)) (second T2)))
))

(declare-datatypes () (
  (S A B C)
))

(declare-datatypes (T) (
  (Lst
    nil
    (cons (hd T) (tl Lst))
  )
))

(declare-datatypes (T)
  (
    (Tree
      leaf
      (node (value T) (children TreeList))
    )
    (TreeList
      tnil
      (tcons (car Tree) (cdr TreeList))
    )
  )
)