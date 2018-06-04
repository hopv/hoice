(set-logic HORN)

(set-option :produce-unsat-cores true)

(declare-fun
  |f_1036$unknown:60|
  ( Int Int Int Int Int Int Int ) Bool
)
(declare-fun
  |f_1036$unknown:61|
  ( Int Int Int Int Int Int Int ) Bool
)
(declare-fun
  |app_without_checking_1157$unknown:49|
  ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool
)
(declare-fun
  |app_1032$unknown:15|
  ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool
)
(declare-fun
  |app_without_checking_1157$unknown:41|
  ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool
)


(assert (forall
  ( (|$alpha-26:x_DO_NOT_CARE_1165| Int) (|$alpha-27:x_DO_NOT_CARE_1166| Int) (|$alpha-28:x_DO_NOT_CARE_1167| Int) (|$alpha-37:v_1034| Int) (|$alpha-39:s_prev_app_h_EXPARAM_1132| Int) (|$alpha-40:s_prev_app_v_1134| Int) (|$alpha-41:u_1035| Int) ) 
  (=>
    (and
      (> (+ |$alpha-37:v_1034| 1) 0)
      (|f_1036$unknown:60| |$alpha-40:s_prev_app_v_1134| |$alpha-39:s_prev_app_h_EXPARAM_1132| 0 (+ |$alpha-37:v_1034| 1) |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
    )
    (|app_without_checking_1157$unknown:49| |$alpha-40:s_prev_app_v_1134| |$alpha-39:s_prev_app_h_EXPARAM_1132| 0 |$alpha-37:v_1034| |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165| |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165| 0 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
  )
))



(assert (forall
  ( (|$V-reftype:20| Int) (|$V-reftype:30| Int) (|$V-reftype:31| Int) (|$alpha-26:x_DO_NOT_CARE_1165| Int) (|$alpha-27:x_DO_NOT_CARE_1166| Int) (|$alpha-28:x_DO_NOT_CARE_1167| Int) (|$alpha-38:prev_set_flag_app_1136| Int) (|$alpha-39:s_prev_app_h_EXPARAM_1132| Int) (|$alpha-41:u_1035| Int) (|$knormal:52| Int) (|$knormal:57| Int) (|$knormal:59| Int) (|$knormal:65| Int) (|$knormal:66| Int) (hoice_fresh_var@43 Int) (hoice_fresh_var@44 Int) (hoice_fresh_var@45 Int) (hoice_fresh_var@46 Int) (hoice_fresh_var@47 Int) (hoice_fresh_var@48 Int) ) 
  (=>
    (and
      (> |$knormal:52| |$knormal:57|)
      (not (= 0 |$knormal:65|))
      (>= |$knormal:57| 0)
      (not (= 0 |$alpha-38:prev_set_flag_app_1136|))
      (not (= 0 |$knormal:66|))
      (not (= 0 |$knormal:59|))
      (> (+ |$knormal:57| 1) 0)
      (|f_1036$unknown:60| |$knormal:52| |$alpha-39:s_prev_app_h_EXPARAM_1132| |$alpha-38:prev_set_flag_app_1136| (+ |$knormal:57| 1) |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
      (|f_1036$unknown:61| |$V-reftype:20| 0 1 |$V-reftype:20| |$V-reftype:20| 0 1)
      (|app_without_checking_1157$unknown:49| hoice_fresh_var@43 hoice_fresh_var@44 hoice_fresh_var@45 |$V-reftype:20| hoice_fresh_var@46 hoice_fresh_var@47 hoice_fresh_var@48 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165| 0 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
      (|app_1032$unknown:15| |$V-reftype:20| 0 1 |$V-reftype:20| |$V-reftype:20| 0 1 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165| 0 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
    )
    (|app_without_checking_1157$unknown:41| |$V-reftype:20| 0 1 |$V-reftype:20| |$V-reftype:20| 0 1 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165| 0 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
  )
))



(assert (forall
  ( (|$V-reftype:20| Int) (|$V-reftype:30| Int) (|$V-reftype:31| Int) (|$alpha-26:x_DO_NOT_CARE_1165| Int) (|$alpha-27:x_DO_NOT_CARE_1166| Int) (|$alpha-28:x_DO_NOT_CARE_1167| Int) (|$alpha-37:v_1034| Int) (|$alpha-39:s_prev_app_h_EXPARAM_1132| Int) (|$alpha-40:s_prev_app_v_1134| Int) (|$alpha-41:u_1035| Int) (hoice_fresh_var@25 Int) (hoice_fresh_var@26 Int) (hoice_fresh_var@27 Int) (hoice_fresh_var@28 Int) (hoice_fresh_var@29 Int) (hoice_fresh_var@30 Int) ) 
  (=>
    (and
      (> (+ |$alpha-37:v_1034| 1) 0)
      (|f_1036$unknown:60| |$alpha-40:s_prev_app_v_1134| |$alpha-39:s_prev_app_h_EXPARAM_1132| 0 (+ |$alpha-37:v_1034| 1) |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
      (|f_1036$unknown:61| |$V-reftype:20| 0 1 |$V-reftype:20| |$V-reftype:20| 0 1)
      (|app_without_checking_1157$unknown:49| hoice_fresh_var@25 hoice_fresh_var@26 hoice_fresh_var@27 |$V-reftype:20| hoice_fresh_var@28 hoice_fresh_var@29 hoice_fresh_var@30 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165| 0 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
      (|app_1032$unknown:15| |$V-reftype:20| 0 1 |$V-reftype:20| |$V-reftype:20| 0 1 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165| 0 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
    )
    (|app_without_checking_1157$unknown:41| |$V-reftype:20| 0 1 |$V-reftype:20| |$V-reftype:20| 0 1 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165| 0 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
  )
))



(assert (forall
  ( (|$alpha-26:x_DO_NOT_CARE_1165| Int) (|$alpha-27:x_DO_NOT_CARE_1166| Int) (|$alpha-28:x_DO_NOT_CARE_1167| Int) (|$alpha-38:prev_set_flag_app_1136| Int) (|$alpha-39:s_prev_app_h_EXPARAM_1132| Int) (|$alpha-41:u_1035| Int) (|$knormal:52| Int) (|$knormal:57| Int) (|$knormal:65| Int) ) 
  (=>
    (and
      (not (= 0 |$alpha-38:prev_set_flag_app_1136|))
      (> (+ |$knormal:57| 1) 0)
      (not (> |$knormal:52| |$knormal:57|))
      (= (not (= 0 |$knormal:65|)) (>= |$knormal:57| 0))
      (|f_1036$unknown:60| |$knormal:52| |$alpha-39:s_prev_app_h_EXPARAM_1132| |$alpha-38:prev_set_flag_app_1136| (+ |$knormal:57| 1) |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
    )
    false
  )
))



(assert (forall
  ( (|$V-reftype:20| Int) (|$V-reftype:78| Int) (|$alpha-26:x_DO_NOT_CARE_1165| Int) (|$alpha-27:x_DO_NOT_CARE_1166| Int) (|$alpha-28:x_DO_NOT_CARE_1167| Int) (|$alpha-38:prev_set_flag_app_1136| Int) (|$alpha-39:s_prev_app_h_EXPARAM_1132| Int) (|$alpha-41:u_1035| Int) (|$knormal:52| Int) (|$knormal:57| Int) (|$knormal:59| Int) (|$knormal:65| Int) (|$knormal:66| Int) (hoice_fresh_var@42 Int) (hoice_fresh_var@43 Int) (hoice_fresh_var@44 Int) (hoice_fresh_var@45 Int) (hoice_fresh_var@46 Int) (hoice_fresh_var@47 Int) ) 
  (=>
    (and
      (> |$knormal:52| |$knormal:57|)
      (not (= 0 |$knormal:66|))
      (not (= 0 |$knormal:59|))
      (not (= 0 |$knormal:65|))
      (not (= 0 |$alpha-38:prev_set_flag_app_1136|))
      (>= |$knormal:57| 0)
      (> (+ |$knormal:57| 1) 0)
      (|f_1036$unknown:60| |$knormal:52| |$alpha-39:s_prev_app_h_EXPARAM_1132| |$alpha-38:prev_set_flag_app_1136| (+ |$knormal:57| 1) |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
      (|app_without_checking_1157$unknown:49| hoice_fresh_var@42 hoice_fresh_var@43 hoice_fresh_var@44 |$V-reftype:20| hoice_fresh_var@45 hoice_fresh_var@46 hoice_fresh_var@47 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165| 0 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
    )
    (|app_1032$unknown:15| |$V-reftype:20| 0 1 |$V-reftype:20| |$V-reftype:20| 0 1 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165| 0 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
  )
))



(assert (forall
  ( (|$V-reftype:20| Int) (|$V-reftype:78| Int) (|$alpha-26:x_DO_NOT_CARE_1165| Int) (|$alpha-27:x_DO_NOT_CARE_1166| Int) (|$alpha-28:x_DO_NOT_CARE_1167| Int) (|$alpha-37:v_1034| Int) (|$alpha-39:s_prev_app_h_EXPARAM_1132| Int) (|$alpha-40:s_prev_app_v_1134| Int) (|$alpha-41:u_1035| Int) (hoice_fresh_var@24 Int) (hoice_fresh_var@25 Int) (hoice_fresh_var@26 Int) (hoice_fresh_var@27 Int) (hoice_fresh_var@28 Int) (hoice_fresh_var@29 Int) ) 
  (=>
    (and
      (> (+ |$alpha-37:v_1034| 1) 0)
      (|f_1036$unknown:60| |$alpha-40:s_prev_app_v_1134| |$alpha-39:s_prev_app_h_EXPARAM_1132| 0 (+ |$alpha-37:v_1034| 1) |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
      (|app_without_checking_1157$unknown:49| hoice_fresh_var@24 hoice_fresh_var@25 hoice_fresh_var@26 |$V-reftype:20| hoice_fresh_var@27 hoice_fresh_var@28 hoice_fresh_var@29 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165| 0 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
    )
    (|app_1032$unknown:15| |$V-reftype:20| 0 1 |$V-reftype:20| |$V-reftype:20| 0 1 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165| 0 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
  )
))



(assert (forall
  ( (|$V-reftype:123| Int) (|$V-reftype:125| Int) (|$V-reftype:127| Int) (|$V-reftype:129| Int) (|$V-reftype:130| Int) (|$alpha-44:set_flag_app_1137| Int) (|$alpha-45:s_app_h_EXPARAM_1128| Int) (|$alpha-46:s_app_v_1130| Int) (|$alpha-47:x_1037| Int) ) 
  (=>
    (and
      (not (> |$alpha-47:x_1037| 0))
      (|f_1036$unknown:60| |$V-reftype:127| |$V-reftype:125| |$V-reftype:123| |$alpha-47:x_1037| |$alpha-46:s_app_v_1130| |$alpha-45:s_app_h_EXPARAM_1128| |$alpha-44:set_flag_app_1137|)
    )
    (|f_1036$unknown:61| |$V-reftype:127| |$V-reftype:125| |$V-reftype:123| |$alpha-47:x_1037| |$alpha-46:s_app_v_1130| |$alpha-45:s_app_h_EXPARAM_1128| |$alpha-44:set_flag_app_1137|)
  )
))



(assert (forall
  ( (|$V-reftype:159| Int) (|$alpha-26:x_DO_NOT_CARE_1165| Int) (|$alpha-27:x_DO_NOT_CARE_1166| Int) (|$alpha-28:x_DO_NOT_CARE_1167| Int) (|$alpha-38:prev_set_flag_app_1136| Int) (|$alpha-39:s_prev_app_h_EXPARAM_1132| Int) (|$alpha-41:u_1035| Int) (|$knormal:52| Int) (|$knormal:57| Int) (|$knormal:59| Int) (|$knormal:65| Int) (|$knormal:66| Int) ) 
  (=>
    (and
      (>= |$knormal:57| 0)
      (not (= 0 |$alpha-38:prev_set_flag_app_1136|))
      (not (= 0 |$knormal:59|))
      (> (+ |$knormal:57| 1) 0)
      (not (= 0 |$knormal:65|))
      (> |$knormal:52| |$knormal:57|)
      (not (= 0 |$knormal:66|))
      (|f_1036$unknown:60| |$knormal:52| |$alpha-39:s_prev_app_h_EXPARAM_1132| |$alpha-38:prev_set_flag_app_1136| (+ |$knormal:57| 1) |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
      (|app_without_checking_1157$unknown:49| |$knormal:52| |$alpha-39:s_prev_app_h_EXPARAM_1132| |$alpha-38:prev_set_flag_app_1136| |$knormal:57| |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165| |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165| 0 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
      (|app_without_checking_1157$unknown:41| |$knormal:57| 0 1 |$knormal:57| |$knormal:57| 0 1 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165| 0 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
    )
    (|f_1036$unknown:61| |$knormal:52| |$alpha-39:s_prev_app_h_EXPARAM_1132| |$alpha-38:prev_set_flag_app_1136| (+ |$knormal:57| 1) |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
  )
))



(assert (forall
  ( (|$V-reftype:164| Int) (|$alpha-26:x_DO_NOT_CARE_1165| Int) (|$alpha-27:x_DO_NOT_CARE_1166| Int) (|$alpha-28:x_DO_NOT_CARE_1167| Int) (|$alpha-37:v_1034| Int) (|$alpha-39:s_prev_app_h_EXPARAM_1132| Int) (|$alpha-40:s_prev_app_v_1134| Int) (|$alpha-41:u_1035| Int) ) 
  (=>
    (and
      (> (+ |$alpha-37:v_1034| 1) 0)
      (|f_1036$unknown:60| |$alpha-40:s_prev_app_v_1134| |$alpha-39:s_prev_app_h_EXPARAM_1132| 0 (+ |$alpha-37:v_1034| 1) |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
      (|app_without_checking_1157$unknown:49| |$alpha-40:s_prev_app_v_1134| |$alpha-39:s_prev_app_h_EXPARAM_1132| 0 |$alpha-37:v_1034| |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165| |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165| 0 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
      (|app_without_checking_1157$unknown:41| |$alpha-37:v_1034| 0 1 |$alpha-37:v_1034| |$alpha-37:v_1034| 0 1 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165| 0 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
    )
    (|f_1036$unknown:61| |$alpha-40:s_prev_app_v_1134| |$alpha-39:s_prev_app_h_EXPARAM_1132| 0 (+ |$alpha-37:v_1034| 1) |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
  )
))



(assert (forall
  ( (|$alpha-50:r| Int) ) 
  (|f_1036$unknown:60| 0 0 0 |$alpha-50:r| 0 0 0)
))



(assert (forall
  ( (|$alpha-26:x_DO_NOT_CARE_1165| Int) (|$alpha-27:x_DO_NOT_CARE_1166| Int) (|$alpha-28:x_DO_NOT_CARE_1167| Int) (|$alpha-38:prev_set_flag_app_1136| Int) (|$alpha-39:s_prev_app_h_EXPARAM_1132| Int) (|$alpha-41:u_1035| Int) (|$knormal:52| Int) (|$knormal:57| Int) (|$knormal:59| Int) (|$knormal:65| Int) (|$knormal:66| Int) ) 
  (=>
    (and
      (> |$knormal:52| |$knormal:57|)
      (not (= 0 |$alpha-38:prev_set_flag_app_1136|))
      (>= |$knormal:57| 0)
      (> (+ |$knormal:57| 1) 0)
      (not (= 0 |$knormal:65|))
      (not (= 0 |$knormal:66|))
      (not (= 0 |$knormal:59|))
      (|f_1036$unknown:60| |$knormal:52| |$alpha-39:s_prev_app_h_EXPARAM_1132| |$alpha-38:prev_set_flag_app_1136| (+ |$knormal:57| 1) |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
    )
    (|app_without_checking_1157$unknown:49| |$knormal:52| |$alpha-39:s_prev_app_h_EXPARAM_1132| |$alpha-38:prev_set_flag_app_1136| |$knormal:57| |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165| |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165| 0 |$alpha-28:x_DO_NOT_CARE_1167| |$alpha-27:x_DO_NOT_CARE_1166| |$alpha-26:x_DO_NOT_CARE_1165|)
  )
))



(assert (forall
  ( (|$V-reftype:105| Int) (|$V-reftype:107| Int) (|$V-reftype:109| Int) (|$V-reftype:111| Int) (|$V-reftype:113| Int) (|$V-reftype:115| Int) (|$V-reftype:29| Int) (|$alpha-44:set_flag_app_1137| Int) (|$alpha-45:s_app_h_EXPARAM_1128| Int) (|$alpha-46:s_app_v_1130| Int) (|$alpha-47:x_1037| Int) (|$knormal:71| Int) (f_1036 Int) ) 
  (=>
    (and
      (not (= 0 |$knormal:71|))
      (> |$alpha-47:x_1037| 0)
      (|app_1032$unknown:15| |$V-reftype:115| |$V-reftype:113| |$V-reftype:111| |$V-reftype:109| |$V-reftype:107| |$V-reftype:105| f_1036 |$alpha-46:s_app_v_1130| |$alpha-45:s_app_h_EXPARAM_1128| |$alpha-44:set_flag_app_1137| 0 |$alpha-46:s_app_v_1130| |$alpha-45:s_app_h_EXPARAM_1128| |$alpha-44:set_flag_app_1137|)
    )
    (|f_1036$unknown:60| |$V-reftype:115| |$V-reftype:113| |$V-reftype:111| |$V-reftype:109| |$V-reftype:107| |$V-reftype:105| f_1036)
  )
))


(check-sat)

(get-model)