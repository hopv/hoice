(set-logic HORN)

(declare-fun |main@.lr.ph.i.preheader| ( (Array Int Int) Int ) Bool)
(declare-fun |main@linear_search.exit.split| ( ) Bool)
(declare-fun |main@.lr.ph.i| ( (Array Int Int) Int Int Int Int (Array Int Int) ) Bool)

(assert
  (forall ( (A (Array Int Int)) (B Int) ) 
    (=>
      (and
        true
      )
      (main@.lr.ph.i.preheader A B)
    )
  )
)
(assert
  (forall ( (A (Array Int Int)) (B Int) (C Int) (D Int) (E (Array Int Int)) (F Int) (G (Array Int Int)) (H Int) (I Bool) (J Bool) (K Int) (L (Array Int Int)) (M Int) (N Int) (O Int) (P Int) (Q (Array Int Int)) ) 
    (=>
      (and
        (main@.lr.ph.i.preheader A C)
        (and (= H (+ P (* 4 F)))
     (= O (+ 1 D))
     (= E (store A M 0))
     (= L (store E M O))
     (= Q (store G H 3))
     (not (<= P 0))
     (or (not J) (not I) (= K 0))
     (or (not J) (not I) (= N K))
     (or (<= P 0) (not (<= H 0)))
     (or (not I) (and J I))
     (= I true)
     (= B C))
      )
      (main@.lr.ph.i L M N O P Q)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Bool) (D Bool) (E Int) (F Bool) (G Int) (H Bool) (I Bool) (J Int) (K (Array Int Int)) (L Int) (M Int) (N Int) (O Int) (P (Array Int Int)) ) 
    (=>
      (and
        (main@.lr.ph.i K L E N O P)
        (let ((a!1 (ite (>= G 0)
                (or (not (<= N G)) (not (>= N 0)))
                (and (not (<= N G)) (not (<= 0 N))))))
  (and (= A (+ O (* 4 E)))
       (= B (select P A))
       (not (<= O 0))
       (or (not I) (not D) (not C))
       (or (not I) (not H) (= J G))
       (or (not I) (not H) (= M J))
       (or (not I) (not H) F)
       (or (<= O 0) (not (<= A 0)))
       (or (not H) (and I H))
       (or (not I) (= F a!1))
       (or (not I) (= G (+ 1 E)))
       (or (not I) (and I C))
       (= H true)
       (= D (= B 3))))
      )
      (main@.lr.ph.i K L M N O P)
    )
  )
)
(assert
  (forall ( (A Int) (B (Array Int Int)) (C Int) (D Int) (E Int) (F Bool) (G Int) (H Bool) (I Int) (J Bool) (K Bool) (L Int) (M Bool) (N Bool) (O Int) (P (Array Int Int)) (Q Int) (R Int) (S Int) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) ) 
    (=>
      (and
        (main@.lr.ph.i P Q I E A B)
        (let ((a!1 (ite (>= G 0)
                (or (not (<= E G)) (not (>= E 0)))
                (and (not (<= E G)) (not (<= 0 E)))))
      (a!2 (ite (>= R 0)
                (or (not (<= S R)) (not (>= S 0)))
                (and (not (<= S R)) (not (<= 0 S))))))
  (and (= C (+ A (* 4 I)))
       (= D (select B C))
       (not (<= A 0))
       (or (not M) (not J) (not H))
       (or (not W) (and N M) (and K J))
       (or (not K) (not J) (= L G))
       (or (not K) (not J) (= R L))
       (or (not K) (not J) (not F))
       (or (not N) (not M) (= O I))
       (or (not N) (not M) (= R O))
       (or (not N) (not M) H)
       (or (not (<= C 0)) (<= A 0))
       (or (not J) (= F a!1))
       (or (not J) (= G (+ 1 I)))
       (or (not J) (and M J))
       (or (not W) (= U a!2))
       (or (not W) (= V (not U)))
       (or (not W) (= S (select P Q)))
       (or (not W) (not T))
       (or (not W) V)
       (or (not X) (and X W))
       (or (not K) J)
       (or (not N) M)
       (= X true)
       (= H (= D 3))))
      )
      main@linear_search.exit.split
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        main@linear_search.exit.split
        true
      )
      false
    )
  )
)

(check-sat)

(exit)
