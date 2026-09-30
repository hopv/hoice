; Issue #73: `Heap73` mentions `Nat73`, which it precedes alphabetically. The
; datatypes must still be declared to the backend solver `Nat73` first.
(set-logic HORN)
(declare-datatypes ((Nat73 0)) (((Z73) (S73 (p73 Nat73)))))
(declare-datatypes ((Heap73 0)) (((Leaf73) (Node73 (l73 Heap73) (v73 Nat73) (r73 Heap73)))))
(declare-fun P73 (Heap73) Bool)
(assert (forall ((h Heap73)) (=> (= h Leaf73) (P73 h))))
(assert (forall ((h Heap73) (n Nat73)) (=> (P73 h) (P73 (Node73 h n Leaf73)))))
(assert (forall ((h Heap73))
  (=> (and (P73 h) (= h (Node73 Leaf73 Z73 (Node73 Leaf73 Z73 Leaf73)))) false)))
(check-sat)
