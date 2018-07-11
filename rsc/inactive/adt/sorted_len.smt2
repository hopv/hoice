(set-logic HORN)

(declare-datatypes () (
  (Lst nil (cons (head Int) (tail Lst)))
) )

(define-funs-rec
  (
    (len ( (l Lst) ) Int)
  )
  (
    (ite
      (= l nil)
      0
      (+ 1 (len (tail l)))
    )
  )
)

(define-funs-rec
  (
    (all_equal ( (l Lst) ) Bool)
    (all_equal_aux ( (v Int) (l Lst) ) Bool)
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

; let rev =
;   let rec loop acc = function
;   | [] -> acc
;   | h :: t -> loop (h :: acc) t
;   in
;   loop []

; Post-condition.
(declare-fun
  rev_pst ( Lst Lst Lst ) Bool
)
; Terminal case.
(assert
  (forall ( (acc Lst) )
    (rev_pst acc nil acc)
) )
; Recursive case.
(assert
  (forall ( (acc Lst) (lst Lst) (res Lst) )
  (=>
    (and
      (not (= lst nil))
      (rev_pst
        (cons (head lst) acc)
        (tail lst)
        res
      )
    )
    (rev_pst acc lst res)
  )
) )


; let rec sorted = function
; | nil | _ :: nil => true
; | h1 :: h2 :: t => (h1 < h2) and (sorted (h2 :: t))
; (* STRICTLY sorted~~~~~^ *)

; Post-condition.
(declare-fun
  srt_pst ( Lst Bool ) Bool
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
  (forall ( (lst Lst) )
  (=>
    (and
      (not (= lst nil))
      (not (= (tail lst) nil))
      (not (< (head lst) (head (tail lst))))
    )
    (srt_pst lst false)
  )
) )
; Recursive case.
(assert
  (forall ( (lst Lst) (res Bool) )
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
  (forall ( (lst1 Lst) (lst2 Lst) )
  (=>
    (and
      (rev_pst nil lst1 lst2)
      (srt_pst lst1 true)
      (srt_pst lst2 true)
      (not (all_equal lst1))
    )
    false
  )
) )


(check-sat)
(get-model)