(set-logic HORN)

(declare-datatypes ( (Lst 1) ) (
  (par (T) (
    (nil)
    (cons (head T) (tail (Lst T)))
  ) )
) )

(define-funs-rec
  (
    (len ( (l (Lst Int)) ) Int)
  )
  (
    (ite
      (= l nil)
      0
      (+ 1 (len (tail l)))
    )
  )
)

(assert (forall
  ( (l (Lst Int)) )
  (>= (len l) 0)
))

(define-funs-rec
  (
    (all_equal ( (l (Lst Int)) ) Bool)
    (all_equal_aux ( (v Int) (l (Lst Int)) ) Bool)
  )
  (
    (ite
      (= l nil)
      true
      (all_equal_aux (head l) (tail l))
    )
    (ite
      (= l nil)
      true
      (ite
        (not (= (head l) v) )
        false
        (all_equal_aux v (tail l))
      )
    )
  )
)

(define-funs-rec
  (
    (rev ( (l (Lst Int)) ) (Lst Int))
    (rev_aux ( (acc (Lst Int)) (l (Lst Int)) ) (Lst Int))
  )
  (
    (rev_aux nil l)
    (ite
      (= l nil)
      acc
      (rev_aux (cons (head l) acc) (tail l))
    )
  )
)


; let rec sorted = function
; | nil | _ :: nil => true
; | h1 :: h2 :: t => (h1 < h2) and (sorted (h2 :: t))
; (* STRICTLY sorted~~~~~^ *)

; Post-condition.
(declare-fun
  srt_pst ( (Lst Int) Bool ) Bool
)

; Terminal cases.
(assert
  (forall ( (unused Bool) )
  (srt_pst nil true)
) )

(assert
  (forall ( (hd Int) )
  (srt_pst (cons hd nil) true)
) )

(assert
  (forall ( (lst (Lst Int)) )
  (=>
    (and
      (not (= lst nil))
      (not (= (tail lst) nil))
      (not (< (head lst) (head (tail lst))))
    )
    (srt_pst lst false)
  )
) )

(assert
  (forall ( (lst (Lst Int)) )
  (=>
    (and
      (not (= lst nil))
      (not (= (tail lst) nil))
      (not (< (head lst) (head (tail lst))))
      (srt_pst lst true)
    )
    false
  )
) )

; Recursive case.
(assert
  (forall ( (lst (Lst Int)) (res Bool) )
  (=>
    (and
      (not (= lst nil))
      (not (= (tail lst) nil))
      (< (head lst) (head (tail lst)))
      (srt_pst (tail lst) res)
    )
    (srt_pst lst res)
  )
) )


; let main lst =
;   if lst = (rev lst)
;   and (sorted lst)
;   and (sorted (rev lst))
;   then (assert (all_elements_the_same lst))
(assert
  (forall ( (lst1 (Lst Int)) (lst2 (Lst Int)) )
  (=>
    (and
      (= (rev lst1) lst2)
      (srt_pst lst1 true)
      (srt_pst lst2 true)
      (not (<= (len lst1) 1))
    )
    false
  )
) )


(check-sat)
