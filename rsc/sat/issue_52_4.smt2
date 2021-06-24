(set-logic HORN)

(declare-fun a () Bool)

(assert (not a) )

(check-sat)