; Mutually recursive datatypes must be declared to the backend solver in a
; single `declare-datatypes` command.
(set-logic HORN)
(declare-datatypes ((TreeMut 0) (ForestMut 0))
  (((NdMut (kidsMut ForestMut)))
   ((NilMut) (ConsMut (hdMut TreeMut) (tlMut ForestMut)))))
(declare-fun PMut (ForestMut) Bool)
(assert (forall ((f ForestMut)) (=> (= f NilMut) (PMut f))))
(assert (forall ((f ForestMut)) (=> (PMut f) (PMut (ConsMut (NdMut NilMut) f)))))
(assert (forall ((f ForestMut))
  (=> (and (PMut f) (= f (ConsMut (NdMut (ConsMut (NdMut NilMut) NilMut)) NilMut))) false)))
(check-sat)
