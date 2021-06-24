(set-logic HORN)

(declare-fun a (Int) Bool)

(assert (not (a 7)) )

(check-sat)