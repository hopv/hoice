(set-logic HORN)

(declare-fun a (Int) Bool)

(assert (a 7) )

(check-sat)