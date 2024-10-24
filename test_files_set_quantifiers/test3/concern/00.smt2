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
(declare-const D (Set (Tuple Int)))
(declare-const not_D (Set (Tuple Int Int)))
(declare-const Measure (Set (Tuple Int Int)))
(assert (set.exists ((tuple_40 (Tuple Int))) C (set.exists ((tuple_41 (Tuple Int Int))) Measure (and (set.exists ((tuple_43 (Tuple Int Int))) not_D (and (= ((_ tuple.select 1) tuple_43) (+ ((_ tuple.select 0) tuple_40) 15)) (= ((_ tuple.select 0) tuple_43) (+ ((_ tuple.select 0) tuple_40) 1)))) (= ((_ tuple.select 0) tuple_40) ((_ tuple.select 0) tuple_41))))))
(assert (set.forall ((tuple_2 (Tuple Int))) A (set.exists ((tuple_3 (Tuple Int Int))) Measure (and (=> true (or (set.exists ((tuple_5 (Tuple Int Int))) Measure (and (set.exists ((tuple_6 (Tuple Int))) D (and (>= ((_ tuple.select 0) tuple_6) (+ ((_ tuple.select 0) tuple_5) 0)) (<= ((_ tuple.select 0) tuple_6) (+ ((_ tuple.select 0) tuple_5) 5)))) (= (+ ((_ tuple.select 0) tuple_3) 10) ((_ tuple.select 0) tuple_5)))) (set.exists ((tuple_4 (Tuple Int))) B (and (>= ((_ tuple.select 0) tuple_4) (+ ((_ tuple.select 0) tuple_2) 0)) (<= ((_ tuple.select 0) tuple_4) (+ ((_ tuple.select 0) tuple_2) 10)))))) (= ((_ tuple.select 0) tuple_2) ((_ tuple.select 0) tuple_3))))))
(assert (set.forall ((tuple_16 (Tuple Int))) C (set.exists ((tuple_17 (Tuple Int Int))) Measure (and (=> true (or (set.exists ((tuple_19 (Tuple Int Int))) Measure (and (set.exists ((tuple_20 (Tuple Int))) B (and (>= ((_ tuple.select 0) tuple_20) (+ ((_ tuple.select 0) tuple_19) 0)) (<= ((_ tuple.select 0) tuple_20) (+ ((_ tuple.select 0) tuple_19) 5)))) (= (+ ((_ tuple.select 0) tuple_17) 10) ((_ tuple.select 0) tuple_19)))) (set.exists ((tuple_18 (Tuple Int))) A (and (>= ((_ tuple.select 0) tuple_18) (+ ((_ tuple.select 0) tuple_16) 1)) (<= ((_ tuple.select 0) tuple_18) (+ ((_ tuple.select 0) tuple_16) 10)))))) (= ((_ tuple.select 0) tuple_16) ((_ tuple.select 0) tuple_17))))))
(assert (set.forall ((tuple_30 (Tuple Int))) B (set.exists ((tuple_31 (Tuple Int Int))) Measure (and (set.exists ((tuple_32 (Tuple Int))) D (and (>= ((_ tuple.select 0) tuple_32) (+ ((_ tuple.select 0) tuple_30) 0)) (<= ((_ tuple.select 0) tuple_32) (+ ((_ tuple.select 0) tuple_30) 1)))) (= ((_ tuple.select 0) tuple_30) ((_ tuple.select 0) tuple_31))))))
(assert (and (and (forall ((D_time_Int_9 Int) (not_D_start_time_Int_10 Int) (not_D_end_time_Int_11 Int)) (=> (and (set.member (tuple not_D_start_time_Int_10 not_D_end_time_Int_11) not_D) (set.member (tuple D_time_Int_9) D)) (not (and (<= D_time_Int_9 not_D_end_time_Int_11) (<= not_D_start_time_Int_10 D_time_Int_9))))) (and (forall ((C_time_Int_6 Int) (not_C_start_time_Int_7 Int) (not_C_end_time_Int_8 Int)) (=> (and (set.member (tuple not_C_start_time_Int_7 not_C_end_time_Int_8) not_C) (set.member (tuple C_time_Int_6) C)) (not (and (<= C_time_Int_6 not_C_end_time_Int_8) (<= not_C_start_time_Int_7 C_time_Int_6))))) (and (forall ((B_time_Int_3 Int) (not_B_start_time_Int_4 Int) (not_B_end_time_Int_5 Int)) (=> (and (set.member (tuple not_B_start_time_Int_4 not_B_end_time_Int_5) not_B) (set.member (tuple B_time_Int_3) B)) (not (and (<= B_time_Int_3 not_B_end_time_Int_5) (<= not_B_start_time_Int_4 B_time_Int_3))))) (forall ((A_time_Int_0 Int) (not_A_start_time_Int_1 Int) (not_A_end_time_Int_2 Int)) (=> (and (set.member (tuple not_A_start_time_Int_1 not_A_end_time_Int_2) not_A) (set.member (tuple A_time_Int_0) A)) (not (and (<= A_time_Int_0 not_A_end_time_Int_2) (<= not_A_start_time_Int_1 A_time_Int_0)))))))) (set.forall ((tuple_64 (Tuple Int Int Int Int))) (rel.product Measure Measure) (=> (= ((_ tuple.select 0) tuple_64) ((_ tuple.select 2) tuple_64)) (and (= ((_ tuple.select 1) tuple_64) ((_ tuple.select 3) tuple_64)) (= ((_ tuple.select 0) tuple_64) ((_ tuple.select 2) tuple_64)))))))
(assert (=> (set.exists ((tuple_44 (Tuple Int))) A true) (and (set.exists ((tuple_47 (Tuple Int))) A (set.forall ((tuple_48 (Tuple Int))) A (<= ((_ tuple.select 0) tuple_48) ((_ tuple.select 0) tuple_47)))) (set.exists ((tuple_45 (Tuple Int))) A (set.forall ((tuple_46 (Tuple Int))) A (>= ((_ tuple.select 0) tuple_46) ((_ tuple.select 0) tuple_45)))))))
(assert (=> (set.exists ((tuple_49 (Tuple Int))) B true) (and (set.exists ((tuple_52 (Tuple Int))) B (set.forall ((tuple_53 (Tuple Int))) B (<= ((_ tuple.select 0) tuple_53) ((_ tuple.select 0) tuple_52)))) (set.exists ((tuple_50 (Tuple Int))) B (set.forall ((tuple_51 (Tuple Int))) B (>= ((_ tuple.select 0) tuple_51) ((_ tuple.select 0) tuple_50)))))))
(assert (=> (set.exists ((tuple_54 (Tuple Int))) C true) (and (set.exists ((tuple_57 (Tuple Int))) C (set.forall ((tuple_58 (Tuple Int))) C (<= ((_ tuple.select 0) tuple_58) ((_ tuple.select 0) tuple_57)))) (set.exists ((tuple_55 (Tuple Int))) C (set.forall ((tuple_56 (Tuple Int))) C (>= ((_ tuple.select 0) tuple_56) ((_ tuple.select 0) tuple_55)))))))
(assert (=> (set.exists ((tuple_59 (Tuple Int))) D true) (and (set.exists ((tuple_62 (Tuple Int))) D (set.forall ((tuple_63 (Tuple Int))) D (<= ((_ tuple.select 0) tuple_63) ((_ tuple.select 0) tuple_62)))) (set.exists ((tuple_60 (Tuple Int))) D (set.forall ((tuple_61 (Tuple Int))) D (>= ((_ tuple.select 0) tuple_61) ((_ tuple.select 0) tuple_60)))))))
(assert (set.forall ((tuple_1 (Tuple Int))) time (>= ((_ tuple.select 0) tuple_1) 0)))
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert (set.forall ((tuple_65 (Tuple Int Int))) Measure (set.exists ((tuple_66 (Tuple Int))) time (= ((_ tuple.select 0) tuple_66) ((_ tuple.select 0) tuple_65)))))
(check-sat)
