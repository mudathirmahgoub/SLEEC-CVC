(set-logic HO_ALL)
(set-option :produce-models true)
(set-option :finite-model-find true)
(set-option :check-models true)
(set-option :sets-exp true)
(set-option :dag-thresh 0)
(set-option :uf-lazy-ll true)
(set-option :fmf-bound true)
(set-option :tlimit-per 20000)
(declare-const time (Set (Tuple Int)))
(declare-const A (Set (Tuple Int)))
(declare-const not_A (Set (Tuple Int Int)))
(declare-const B (Set (Tuple Int)))
(declare-const not_B (Set (Tuple Int Int)))
(declare-const C (Set (Tuple Int)))
(declare-const not_C (Set (Tuple Int Int)))
(declare-const Measure (Set (Tuple Int Int)))
(assert (set.exists ((tuple_8 (Tuple Int Int Int))) (rel.product A Measure) (= ((_ tuple.select 0) tuple_8) ((_ tuple.select 1) tuple_8))))
(assert (set.forall ((tuple_2 (Tuple Int))) A (set.exists ((tuple_3 (Tuple Int Int))) Measure (and (set.exists ((tuple_4 (Tuple Int))) B (and (>= ((_ tuple.select 0) tuple_4) (+ ((_ tuple.select 0) tuple_2) 0)) (<= ((_ tuple.select 0) tuple_4) (+ ((_ tuple.select 0) tuple_2) 7)))) (= ((_ tuple.select 0) tuple_2) ((_ tuple.select 0) tuple_3))))))
(assert (set.forall ((tuple_12 (Tuple Int))) B (set.exists ((tuple_13 (Tuple Int Int))) Measure (and (set.exists ((tuple_14 (Tuple Int))) C (and (>= ((_ tuple.select 0) tuple_14) (+ ((_ tuple.select 0) tuple_12) 0)) (<= ((_ tuple.select 0) tuple_14) (+ ((_ tuple.select 0) tuple_12) 7)))) (= ((_ tuple.select 0) tuple_12) ((_ tuple.select 0) tuple_13))))))
(assert (set.forall ((tuple_22 (Tuple Int))) A (set.exists ((tuple_23 (Tuple Int Int))) Measure (and (or (set.exists ((tuple_24 (Tuple Int))) C (and (>= ((_ tuple.select 0) tuple_24) (+ ((_ tuple.select 0) tuple_22) 0)) (<= ((_ tuple.select 0) tuple_24) (+ ((_ tuple.select 0) tuple_22) 15)))) (not (< ((_ tuple.select 1) tuple_23) 20))) (= ((_ tuple.select 0) tuple_22) ((_ tuple.select 0) tuple_23))))))
(assert (set.forall ((tuple_35 (Tuple Int))) A (set.exists ((tuple_36 (Tuple Int Int))) Measure (and (set.exists ((tuple_38 (Tuple Int Int))) not_C (and (= ((_ tuple.select 1) tuple_38) (+ ((_ tuple.select 0) tuple_35) 11)) (= ((_ tuple.select 0) tuple_38) (+ ((_ tuple.select 0) tuple_35) 0)))) (= ((_ tuple.select 0) tuple_35) ((_ tuple.select 0) tuple_36))))))
(assert (and (and (forall ((C_time_Int_6 Int) (not_C_start_time_Int_7 Int) (not_C_end_time_Int_8 Int)) (=> (and (set.member (tuple not_C_start_time_Int_7 not_C_end_time_Int_8) not_C) (set.member (tuple C_time_Int_6) C)) (not (and (<= C_time_Int_6 not_C_end_time_Int_8) (<= not_C_start_time_Int_7 C_time_Int_6))))) (and (forall ((B_time_Int_3 Int) (not_B_start_time_Int_4 Int) (not_B_end_time_Int_5 Int)) (=> (and (set.member (tuple not_B_start_time_Int_4 not_B_end_time_Int_5) not_B) (set.member (tuple B_time_Int_3) B)) (not (and (<= B_time_Int_3 not_B_end_time_Int_5) (<= not_B_start_time_Int_4 B_time_Int_3))))) (forall ((A_time_Int_0 Int) (not_A_start_time_Int_1 Int) (not_A_end_time_Int_2 Int)) (=> (and (set.member (tuple not_A_start_time_Int_1 not_A_end_time_Int_2) not_A) (set.member (tuple A_time_Int_0) A)) (not (and (<= A_time_Int_0 not_A_end_time_Int_2) (<= not_A_start_time_Int_1 A_time_Int_0))))))) (set.forall ((tuple_62 (Tuple Int Int Int Int))) (rel.product Measure Measure) (=> (= ((_ tuple.select 0) tuple_62) ((_ tuple.select 2) tuple_62)) (and (= ((_ tuple.select 1) tuple_62) ((_ tuple.select 3) tuple_62)) (= ((_ tuple.select 0) tuple_62) ((_ tuple.select 2) tuple_62)))))))
(assert (=> (set.exists ((tuple_47 (Tuple Int))) A true) (and (set.exists ((tuple_50 (Tuple Int))) A (set.forall ((tuple_51 (Tuple Int))) A (<= ((_ tuple.select 0) tuple_51) ((_ tuple.select 0) tuple_50)))) (set.exists ((tuple_48 (Tuple Int))) A (set.forall ((tuple_49 (Tuple Int))) A (>= ((_ tuple.select 0) tuple_49) ((_ tuple.select 0) tuple_48)))))))
(assert (=> (set.exists ((tuple_52 (Tuple Int))) B true) (and (set.exists ((tuple_55 (Tuple Int))) B (set.forall ((tuple_56 (Tuple Int))) B (<= ((_ tuple.select 0) tuple_56) ((_ tuple.select 0) tuple_55)))) (set.exists ((tuple_53 (Tuple Int))) B (set.forall ((tuple_54 (Tuple Int))) B (>= ((_ tuple.select 0) tuple_54) ((_ tuple.select 0) tuple_53)))))))
(assert (=> (set.exists ((tuple_57 (Tuple Int))) C true) (and (set.exists ((tuple_60 (Tuple Int))) C (set.forall ((tuple_61 (Tuple Int))) C (<= ((_ tuple.select 0) tuple_61) ((_ tuple.select 0) tuple_60)))) (set.exists ((tuple_58 (Tuple Int))) C (set.forall ((tuple_59 (Tuple Int))) C (>= ((_ tuple.select 0) tuple_59) ((_ tuple.select 0) tuple_58)))))))
(assert (set.forall ((tuple_1 (Tuple Int))) time (>= ((_ tuple.select 0) tuple_1) 0)))
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert (set.forall ((tuple_63 (Tuple Int Int))) Measure (set.exists ((tuple_64 (Tuple Int))) time (= ((_ tuple.select 0) tuple_64) ((_ tuple.select 0) tuple_63)))))
(check-sat)
(get-model)
