(set-info :origin "Verification conditions for the caml program
  (*
  USED: PLDI2011 as a-init
  *)
  
  let make_array n i = assert (0 <= i && i < n); 0
  let update i a x j :int= if j > i-1 && j <= i then x else a (j)
  let rec init i n a =
    if i >= n then a else init (i + 1) n (update i a 1)
  let main k n i =
    if k >= 0 && k <= 0 then
      let x = init k n (make_array n) in
        if 0 <= i && i < n then
          assert (x i >= 1)
")

(set-logic HORN)

(declare-fun |make_array$unknown:9|
  ( Int Int Int ) Bool
)

(declare-fun |make_array$unknown:8|
  ( Int Int ) Bool
)

(declare-fun |update$unknown:12|
  ( Int Int Int ) Bool
)

(declare-fun |update$unknown:11|
  ( Int Int ) Bool
)

(declare-fun |init$unknown:6|
  ( Int Int Int Int ) Bool
)

(declare-fun |init$unknown:5|
  ( Int Int Int ) Bool
)

(declare-fun |init$unknown:4|
  ( Int Int Int Int ) Bool
)

(declare-fun |update$unknown:15|
  ( Int Int Int Int ) Bool
)

(declare-fun |update$unknown:14|
  ( Int Int Int ) Bool
)

(declare-fun |init$unknown:3|
  ( Int Int Int ) Bool
)

(assert
  (forall ( (|$V-reftype:5| Int) (|$alpha-8:i| Int) (|$alpha-9:n| Int) (|$knormal:13| Int) (|$knormal:16| Int) (|$knormal:9| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:9|)) (>= |$alpha-8:i| |$alpha-9:n|)) (= |$knormal:16| (+ |$alpha-8:i| 1)) (= |$knormal:13| 1) (not (not (= 0 |$knormal:9|))) (|init$unknown:3| |$V-reftype:5| |$alpha-9:n| |$knormal:16|) true true )
      (|update$unknown:14| |$V-reftype:5| |$knormal:13| |$alpha-8:i|)
    )
  )
)
(assert
  (forall ( (|$V-reftype:34| Int) (|$alpha-8:i| Int) (|$alpha-9:n| Int) (|$knormal:13| Int) (|$knormal:15| Int) (|$knormal:16| Int) (|$knormal:9| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:9|)) (>= |$alpha-8:i| |$alpha-9:n|)) (= |$knormal:16| (+ |$alpha-8:i| 1)) (= |$knormal:13| 1) (not (not (= 0 |$knormal:9|))) (|update$unknown:15| |$V-reftype:34| |$knormal:15| |$knormal:13| |$alpha-8:i|) (|init$unknown:3| |$knormal:15| |$alpha-9:n| |$knormal:16|) true true )
      (|init$unknown:4| |$V-reftype:34| |$knormal:15| |$alpha-9:n| |$knormal:16|)
    )
  )
)
(assert
  (forall ( (|$V-reftype:6| Int) (|$V-reftype:7| Int) (|$alpha-8:i| Int) (|$alpha-9:n| Int) (|$knormal:9| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:9|)) (>= |$alpha-8:i| |$alpha-9:n|)) (not (= 0 |$knormal:9|)) (|init$unknown:5| |$V-reftype:6| |$alpha-9:n| |$alpha-8:i|) (|init$unknown:4| |$V-reftype:7| |$V-reftype:6| |$alpha-9:n| |$alpha-8:i|) true true )
      (|init$unknown:6| |$V-reftype:7| |$V-reftype:6| |$alpha-9:n| |$alpha-8:i|)
    )
  )
)
(assert
  (forall ( (|$V-reftype:7| Int) (|$alpha-10:a| Int) (|$alpha-8:i| Int) (|$alpha-9:n| Int) (|$knormal:13| Int) (|$knormal:9| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:9|)) (>= |$alpha-8:i| |$alpha-9:n|)) (= |$knormal:13| 1) (not (not (= 0 |$knormal:9|))) (|update$unknown:11| |$alpha-10:a| |$alpha-8:i|) (|init$unknown:4| |$V-reftype:7| |$alpha-10:a| |$alpha-9:n| |$alpha-8:i|) true true )
      (|update$unknown:12| |$V-reftype:7| |$alpha-10:a| |$alpha-8:i|)
    )
  )
)
(assert
  (forall ( (|$V-reftype:10| Int) (|$V-reftype:11| Int) (|$alpha-8:i| Int) (|$alpha-9:n| Int) (|$knormal:13| Int) (|$knormal:16| Int) (|$knormal:9| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:9|)) (>= |$alpha-8:i| |$alpha-9:n|)) (= |$knormal:16| (+ |$alpha-8:i| 1)) (= |$knormal:13| 1) (not (not (= 0 |$knormal:9|))) (|init$unknown:6| |$V-reftype:11| |$V-reftype:10| |$alpha-9:n| |$knormal:16|) (|init$unknown:5| |$V-reftype:10| |$alpha-9:n| |$alpha-8:i|) true true )
      (|init$unknown:6| |$V-reftype:11| |$V-reftype:10| |$alpha-9:n| |$alpha-8:i|)
    )
  )
)
(assert
  (forall ( (|$V-reftype:9| Int) (|$alpha-8:i| Int) (|$alpha-9:n| Int) (|$knormal:9| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:9|)) (>= |$alpha-8:i| |$alpha-9:n|)) (not (= 0 |$knormal:9|)) (|init$unknown:5| |$V-reftype:9| |$alpha-9:n| |$alpha-8:i|) true true )
      (|init$unknown:3| |$V-reftype:9| |$alpha-9:n| |$alpha-8:i|)
    )
  )
)
(assert
  (forall ( (|$V-reftype:9| Int) (|$alpha-8:i| Int) (|$alpha-9:n| Int) (|$knormal:13| Int) (|$knormal:16| Int) (|$knormal:9| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:9|)) (>= |$alpha-8:i| |$alpha-9:n|)) (= |$knormal:16| (+ |$alpha-8:i| 1)) (= |$knormal:13| 1) (not (not (= 0 |$knormal:9|))) (|init$unknown:5| |$V-reftype:9| |$alpha-9:n| |$alpha-8:i|) true true )
      (|init$unknown:5| |$V-reftype:9| |$alpha-9:n| |$knormal:16|)
    )
  )
)
(assert
  (forall ( (|$V-reftype:26| Int) (|$alpha-8:i| Int) (|$alpha-9:n| Int) (|$knormal:13| Int) (|$knormal:9| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:9|)) (>= |$alpha-8:i| |$alpha-9:n|)) (= |$knormal:13| 1) (not (not (= 0 |$knormal:9|))) (|update$unknown:11| |$V-reftype:26| |$alpha-8:i|) true true )
      (|init$unknown:3| |$V-reftype:26| |$alpha-9:n| |$alpha-8:i|)
    )
  )
)
(assert
  (forall ( (|$alpha-8:i| Int) (|$alpha-9:n| Int) (|$knormal:13| Int) (|$knormal:16| Int) (|$knormal:9| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:9|)) (>= |$alpha-8:i| |$alpha-9:n|)) (= |$knormal:16| (+ |$alpha-8:i| 1)) (= |$knormal:13| 1) (not (not (= 0 |$knormal:9|))) true true )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-8:i| Int) (|$alpha-9:n| Int) (|$knormal:13| Int) (|$knormal:16| Int) (|$knormal:9| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:9|)) (>= |$alpha-8:i| |$alpha-9:n|)) (= |$knormal:16| (+ |$alpha-8:i| 1)) (= |$knormal:13| 1) (not (not (= 0 |$knormal:9|))) true true )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-8:i| Int) (|$alpha-9:n| Int) (|$knormal:13| Int) (|$knormal:9| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:9|)) (>= |$alpha-8:i| |$alpha-9:n|)) (= |$knormal:13| 1) (not (not (= 0 |$knormal:9|))) true true )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-8:i| Int) (|$alpha-9:n| Int) (|$knormal:13| Int) (|$knormal:9| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:9|)) (>= |$alpha-8:i| |$alpha-9:n|)) (= |$knormal:13| 1) (not (not (= 0 |$knormal:9|))) true true )
      true
    )
  )
)
(assert
  (forall ( (|$V-reftype:5| Int) (|$alpha-11:k| Int) (|$alpha-12:n| Int) (|$knormal:23| Int) (|$knormal:24| Int) (|$knormal:25| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:25|)) (and (not (= 0 |$knormal:23|)) (not (= 0 |$knormal:24|)))) (= (not (= 0 |$knormal:24|)) (<= |$alpha-11:k| 0)) (= (not (= 0 |$knormal:23|)) (>= |$alpha-11:k| 0)) (not (= 0 |$knormal:25|)) (|init$unknown:3| |$V-reftype:5| |$alpha-12:n| |$alpha-11:k|) )
      (|make_array$unknown:8| |$V-reftype:5| |$alpha-12:n|)
    )
  )
)
(assert
  (forall ( (|$V-reftype:23| Int) (|$alpha-11:k| Int) (|$alpha-12:n| Int) (|$knormal:23| Int) (|$knormal:24| Int) (|$knormal:25| Int) (|$knormal:32| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:25|)) (and (not (= 0 |$knormal:23|)) (not (= 0 |$knormal:24|)))) (= (not (= 0 |$knormal:24|)) (<= |$alpha-11:k| 0)) (= (not (= 0 |$knormal:23|)) (>= |$alpha-11:k| 0)) (not (= 0 |$knormal:25|)) (|make_array$unknown:9| |$V-reftype:23| |$knormal:32| |$alpha-12:n|) (|init$unknown:3| |$knormal:32| |$alpha-12:n| |$alpha-11:k|) )
      (|init$unknown:4| |$V-reftype:23| |$knormal:32| |$alpha-12:n| |$alpha-11:k|)
    )
  )
)
(assert
  (not (exists ( (|$alpha-11:k| Int) (|$alpha-12:n| Int) (|$alpha-13:i| Int) (|$knormal:23| Int) (|$knormal:24| Int) (|$knormal:25| Int) (|$knormal:26| Int) (|$knormal:27| Int) (|$knormal:28| Int) (|$knormal:29| Int) (|$knormal:31| Int) )
    ( and (= (not (= 0 |$knormal:31|)) (>= |$knormal:29| 1)) (= (not (= 0 |$knormal:28|)) (and (not (= 0 |$knormal:26|)) (not (= 0 |$knormal:27|)))) (= (not (= 0 |$knormal:27|)) (< |$alpha-13:i| |$alpha-12:n|)) (= (not (= 0 |$knormal:26|)) (<= 0 |$alpha-13:i|)) (= (not (= 0 |$knormal:25|)) (and (not (= 0 |$knormal:23|)) (not (= 0 |$knormal:24|)))) (= (not (= 0 |$knormal:24|)) (<= |$alpha-11:k| 0)) (= (not (= 0 |$knormal:23|)) (>= |$alpha-11:k| 0)) (not (not (= 0 |$knormal:31|))) (not (= 0 |$knormal:28|)) (not (= 0 |$knormal:25|)) (|init$unknown:6| |$knormal:29| |$alpha-13:i| |$alpha-12:n| |$alpha-11:k|) )
    )
  )
)
(assert
  (forall ( (|$V-reftype:39| Int) (|$alpha-1:n| Int) (|$alpha-2:i| Int) (|$alpha-3:$$tmp::1| Int) (|$knormal:1| Int) (|$knormal:2| Int) (|$knormal:3| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:3|)) (and (not (= 0 |$knormal:1|)) (not (= 0 |$knormal:2|)))) (= (not (= 0 |$knormal:2|)) (< |$alpha-2:i| |$alpha-1:n|)) (= (not (= 0 |$knormal:1|)) (<= 0 |$alpha-2:i|)) (= |$alpha-3:$$tmp::1| 1) (= |$V-reftype:39| 0) (not (= 0 |$knormal:3|)) (|make_array$unknown:8| |$alpha-2:i| |$alpha-1:n|) true )
      (|make_array$unknown:9| |$V-reftype:39| |$alpha-2:i| |$alpha-1:n|)
    )
  )
)
(assert
  (not (exists ( (|$alpha-1:n| Int) (|$alpha-2:i| Int) (|$knormal:1| Int) (|$knormal:2| Int) (|$knormal:3| Int) )
    ( and (= (not (= 0 |$knormal:3|)) (and (not (= 0 |$knormal:1|)) (not (= 0 |$knormal:2|)))) (= (not (= 0 |$knormal:2|)) (< |$alpha-2:i| |$alpha-1:n|)) (= (not (= 0 |$knormal:1|)) (<= 0 |$alpha-2:i|)) (not (not (= 0 |$knormal:3|))) (|make_array$unknown:8| |$alpha-2:i| |$alpha-1:n|) true )
    )
  )
)
(assert
  (forall ( (|$V-reftype:45| Int) (|$alpha-4:i| Int) (|$alpha-6:x| Int) (|$alpha-7:j| Int) (|$knormal:4| Int) (|$knormal:5| Int) (|$knormal:6| Int) (|$knormal:7| Int) (|$knormal:8| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:7|)) (and (not (= 0 |$knormal:5|)) (not (= 0 |$knormal:6|)))) (= (not (= 0 |$knormal:6|)) (<= |$alpha-7:j| |$alpha-4:i|)) (= (not (= 0 |$knormal:5|)) (> |$alpha-7:j| |$knormal:4|)) (= |$knormal:4| (- |$alpha-4:i| 1)) (= |$V-reftype:45| |$knormal:8|) (not (not (= 0 |$knormal:7|))) (|update$unknown:14| |$alpha-7:j| |$alpha-6:x| |$alpha-4:i|) true (|update$unknown:12| |$knormal:8| |$alpha-7:j| |$alpha-4:i|) true )
      (|update$unknown:15| |$V-reftype:45| |$alpha-7:j| |$alpha-6:x| |$alpha-4:i|)
    )
  )
)
(assert
  (forall ( (|$V-reftype:44| Int) (|$alpha-4:i| Int) (|$alpha-6:x| Int) (|$alpha-7:j| Int) (|$knormal:4| Int) (|$knormal:5| Int) (|$knormal:6| Int) (|$knormal:7| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:7|)) (and (not (= 0 |$knormal:5|)) (not (= 0 |$knormal:6|)))) (= (not (= 0 |$knormal:6|)) (<= |$alpha-7:j| |$alpha-4:i|)) (= (not (= 0 |$knormal:5|)) (> |$alpha-7:j| |$knormal:4|)) (= |$knormal:4| (- |$alpha-4:i| 1)) (= |$V-reftype:44| |$alpha-6:x|) (not (= 0 |$knormal:7|)) (|update$unknown:14| |$alpha-7:j| |$alpha-6:x| |$alpha-4:i|) true true )
      (|update$unknown:15| |$V-reftype:44| |$alpha-7:j| |$alpha-6:x| |$alpha-4:i|)
    )
  )
)
(assert
  (forall ( (|$alpha-4:i| Int) (|$alpha-6:x| Int) (|$alpha-7:j| Int) (|$knormal:4| Int) (|$knormal:5| Int) (|$knormal:6| Int) (|$knormal:7| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:7|)) (and (not (= 0 |$knormal:5|)) (not (= 0 |$knormal:6|)))) (= (not (= 0 |$knormal:6|)) (<= |$alpha-7:j| |$alpha-4:i|)) (= (not (= 0 |$knormal:5|)) (> |$alpha-7:j| |$knormal:4|)) (= |$knormal:4| (- |$alpha-4:i| 1)) (not (not (= 0 |$knormal:7|))) (|update$unknown:14| |$alpha-7:j| |$alpha-6:x| |$alpha-4:i|) true true )
      (|update$unknown:11| |$alpha-7:j| |$alpha-4:i|)
    )
  )
)
(assert
  (forall ( (|$alpha-11:k| Int) (|$alpha-12:n| Int) (|$alpha-13:i| Int) (|$knormal:23| Int) (|$knormal:24| Int) (|$knormal:25| Int) (|$knormal:26| Int) (|$knormal:27| Int) (|$knormal:28| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:28|)) (and (not (= 0 |$knormal:26|)) (not (= 0 |$knormal:27|)))) (= (not (= 0 |$knormal:27|)) (< |$alpha-13:i| |$alpha-12:n|)) (= (not (= 0 |$knormal:26|)) (<= 0 |$alpha-13:i|)) (= (not (= 0 |$knormal:25|)) (and (not (= 0 |$knormal:23|)) (not (= 0 |$knormal:24|)))) (= (not (= 0 |$knormal:24|)) (<= |$alpha-11:k| 0)) (= (not (= 0 |$knormal:23|)) (>= |$alpha-11:k| 0)) (not (= 0 |$knormal:28|)) (not (= 0 |$knormal:25|)) )
      (|init$unknown:5| |$alpha-13:i| |$alpha-12:n| |$alpha-11:k|)
    )
  )
)
(assert
  (forall ( (|$alpha-11:k| Int) (|$knormal:23| Int) (|$knormal:24| Int) (|$knormal:25| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:25|)) (and (not (= 0 |$knormal:23|)) (not (= 0 |$knormal:24|)))) (= (not (= 0 |$knormal:24|)) (<= |$alpha-11:k| 0)) (= (not (= 0 |$knormal:23|)) (>= |$alpha-11:k| 0)) (not (= 0 |$knormal:25|)) )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-11:k| Int) (|$knormal:23| Int) (|$knormal:24| Int) (|$knormal:25| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:25|)) (and (not (= 0 |$knormal:23|)) (not (= 0 |$knormal:24|)))) (= (not (= 0 |$knormal:24|)) (<= |$alpha-11:k| 0)) (= (not (= 0 |$knormal:23|)) (>= |$alpha-11:k| 0)) (not (= 0 |$knormal:25|)) )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-11:k| Int) (|$knormal:23| Int) (|$knormal:24| Int) (|$knormal:25| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:25|)) (and (not (= 0 |$knormal:23|)) (not (= 0 |$knormal:24|)))) (= (not (= 0 |$knormal:24|)) (<= |$alpha-11:k| 0)) (= (not (= 0 |$knormal:23|)) (>= |$alpha-11:k| 0)) (not (= 0 |$knormal:25|)) )
      true
    )
  )
)
(check-sat)

(get-model)

(exit)

