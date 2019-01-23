(set-logic HORN)

(declare-datatypes ((Lst 1)) (
    (par (T) (
      nil (cons (head T) (tail (Lst T))))
    )
) )


; let rev =
;   let rec loop acc = function
;   | [] -> acc
;   | h :: t -> loop (h :: acc) t
;   in
;   loop []

; Post-condition.
(declare-fun
  rev_pst ( (Lst Int) (Lst Int) (Lst Int) ) Bool
)
; Terminal case.
(assert
  (forall ( (acc (Lst Int)) )
    (rev_pst acc nil acc)
) )
; Recursive case.
(assert
  (forall ( (acc (Lst Int)) (lst (Lst Int)) (res (Lst Int)) )
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
;   then match lst
;   | nil | _ :: nil => ()
;   | _ => assert false
(assert
  (forall ( (lst1 (Lst Int)) (lst2 (Lst Int)) )
  (=>
    (and
      (rev_pst nil lst1 lst2)
      (srt_pst lst1 true)
      (srt_pst lst2 true)
      (not (= lst1 nil))
      (not (= (tail lst1) nil))
    )
    false
  )
) )


(check-sat)
(get-model)