(set-logic HORN)
(set-info :status sat)
(declare-fun predr16_5 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun predr8_1 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun predr10_11 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun predr24_2 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun predr12_8 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(assert (forall ((var0 Int)) (forall ((var1 Int)) (forall ((var2 Int)) (forall ((var3 Int)) (forall ((var4 Int)) (forall ((var5 Int)) (forall ((var6 Int)) (forall ((var7 Int)) (forall ((var8 Int)) (forall ((var9 Int)) (forall ((var10 Int)) (forall ((var11 Int)) (forall ((var12 Int)) (forall ((var13 Int)) (forall ((var14 Int)) (forall ((var15 Int)) (not (and (not (predr10_11 var15 var14 var13 var12 var11 var10 var9 var8 var7 var6 var5 var4 0 var3 var2 var1 var0 (* (- 1) 1 ) 0 0 ) ) (not (and (and (and (<= 0 (+ (+ (+ var3 var2 ) (* (- 1) var0 ) ) (* (- 1) 1 ) ) ) (<= 0 (+ var3 (* (- 1) 1 ) ) ) ) (<= 0 (+ var2 (* (- 1) 1 ) ) ) ) (<= 0 (+ var0 (* (- 1) 1 ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )

(check-sat)

(get-model)

(exit)