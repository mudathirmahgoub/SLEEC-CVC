(set-logic HO_ALL)
(set-option :produce-models true)
(set-option :finite-model-find true)
(set-option :check-models true)
(set-option :sets-ext true)
(set-option :dag-thresh 0)
(set-option :uf-lazy-ll true)
(set-option :fmf-bound true)
(set-option :tlimit-per 10000)
(set-option :produce-models true)
(set-option :finite-model-find true)
(set-option :check-models true)
(set-option :sets-ext true)
(set-option :dag-thresh 0)
(set-option :uf-lazy-ll true)
(set-option :fmf-bound true)
(set-option :tlimit-per 10000)
(declare-const time (Set (Tuple Int)))
(declare-const A (Set (Tuple Int)))
(declare-const not_A (Set (Tuple Int Int)))
(declare-const B (Set (Tuple Int)))
(declare-const not_B (Set (Tuple Int Int)))
(declare-const C (Set (Tuple Int)))
(declare-const not_C (Set (Tuple Int Int)))
(declare-const Measure (Set (Tuple Int Int)))
(assert (exists ((C_time_Int_28 Int)) (and (exists ((Measure_time_Int_29 Int) (Measure_m1_Int_30 Int)) (and (and (not (=> true (or (forall ((Measure_time_Int_32 Int) (Measure_m1_Int_33 Int)) (=> (set.member (tuple Measure_time_Int_32 Measure_m1_Int_33) Measure) (=> (= (+ Measure_time_Int_29 10) Measure_time_Int_32) (exists ((B_time_Int_34 Int)) (and (and (>= B_time_Int_34 (+ Measure_time_Int_32 0)) (<= B_time_Int_34 (+ Measure_time_Int_32 5))) (set.member (tuple B_time_Int_34) B)))))) (exists ((A_time_Int_31 Int)) (and (and (>= A_time_Int_31 (+ C_time_Int_28 0)) (<= A_time_Int_31 (+ C_time_Int_28 10))) (set.member (tuple A_time_Int_31) A)))))) (= C_time_Int_28 Measure_time_Int_29)) (set.member (tuple Measure_time_Int_29 Measure_m1_Int_30) Measure))) (set.member (tuple C_time_Int_28) C))))
(assert (forall ((A_time_Int_1 Int)) (=> (set.member (tuple A_time_Int_1) A) (exists ((Measure_time_Int_2 Int) (Measure_m1_Int_3 Int)) (and (and (=> true (or (exists ((Measure_time_Int_5 Int) (Measure_m1_Int_6 Int)) (and (and (exists ((C_time_Int_7 Int)) (and (and (>= C_time_Int_7 (+ Measure_time_Int_5 0)) (<= C_time_Int_7 (+ Measure_time_Int_5 5))) (set.member (tuple C_time_Int_7) C))) (= (+ Measure_time_Int_2 10) Measure_time_Int_5)) (set.member (tuple Measure_time_Int_5 Measure_m1_Int_6) Measure))) (exists ((B_time_Int_4 Int)) (and (and (>= B_time_Int_4 (+ A_time_Int_1 0)) (<= B_time_Int_4 (+ A_time_Int_1 10))) (set.member (tuple B_time_Int_4) B))))) (= A_time_Int_1 Measure_time_Int_2)) (set.member (tuple Measure_time_Int_2 Measure_m1_Int_3) Measure))))))
(assert (forall ((A_time_Int_41 Int)) (=> (set.member (tuple A_time_Int_41) A) (exists ((Measure_time_Int_42 Int) (Measure_m1_Int_43 Int)) (and (and (exists ((not_B_start_time_Int_45 Int) (not_B_end_time_Int_46 Int)) (and (and (= not_B_end_time_Int_46 (+ A_time_Int_41 30)) (= not_B_start_time_Int_45 (+ A_time_Int_41 0))) (set.member (tuple not_B_start_time_Int_45 not_B_end_time_Int_46) not_B))) (= A_time_Int_41 Measure_time_Int_42)) (set.member (tuple Measure_time_Int_42 Measure_m1_Int_43) Measure))))))
(assert (and (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_3 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_3) ((_ tuple.select 2) tuple_3)) (<= ((_ tuple.select 1) tuple_3) ((_ tuple.select 0) tuple_3)))))) (rel.product C not_C))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_2 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_2) ((_ tuple.select 2) tuple_2)) (<= ((_ tuple.select 1) tuple_2) ((_ tuple.select 0) tuple_2)))))) (rel.product B not_B))) (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_1 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_1) ((_ tuple.select 2) tuple_1)) (<= ((_ tuple.select 1) tuple_1) ((_ tuple.select 0) tuple_1)))))) (rel.product A not_A))))) (forall ((Measure_time_Int_59 Int) (Measure_m1_Int_60 Int) (Measure_time_Int_61 Int) (Measure_m1_Int_62 Int)) (=> (and (set.member (tuple Measure_time_Int_61 Measure_m1_Int_62) Measure) (set.member (tuple Measure_time_Int_59 Measure_m1_Int_60) Measure)) (=> (= Measure_time_Int_59 Measure_time_Int_61) (and (= Measure_m1_Int_60 Measure_m1_Int_62) (= Measure_time_Int_59 Measure_time_Int_61)))))))
(assert (forall ((A_time_Int_63 Int)) (=> (set.member (tuple A_time_Int_63) A) (or (exists ((A_time_Int_65 Int)) (and (and (forall ((A_time_Int_66 Int)) (=> (set.member (tuple A_time_Int_66) A) (<= A_time_Int_66 A_time_Int_63))) (> A_time_Int_65 A_time_Int_63)) (set.member (tuple A_time_Int_65) A))) (forall ((A_time_Int_64 Int)) (=> (set.member (tuple A_time_Int_64) A) (<= A_time_Int_64 A_time_Int_63)))))))
(assert (forall ((B_time_Int_67 Int)) (=> (set.member (tuple B_time_Int_67) B) (or (exists ((B_time_Int_69 Int)) (and (and (forall ((B_time_Int_70 Int)) (=> (set.member (tuple B_time_Int_70) B) (<= B_time_Int_70 B_time_Int_67))) (> B_time_Int_69 B_time_Int_67)) (set.member (tuple B_time_Int_69) B))) (forall ((B_time_Int_68 Int)) (=> (set.member (tuple B_time_Int_68) B) (<= B_time_Int_68 B_time_Int_67)))))))
(assert (forall ((C_time_Int_71 Int)) (=> (set.member (tuple C_time_Int_71) C) (or (exists ((C_time_Int_73 Int)) (and (and (forall ((C_time_Int_74 Int)) (=> (set.member (tuple C_time_Int_74) C) (<= C_time_Int_74 C_time_Int_71))) (> C_time_Int_73 C_time_Int_71)) (set.member (tuple C_time_Int_73) C))) (forall ((C_time_Int_72 Int)) (=> (set.member (tuple C_time_Int_72) C) (<= C_time_Int_72 C_time_Int_71)))))))
(assert (forall ((time_val_Int_0 Int)) (=> (set.member (tuple time_val_Int_0) time) (>= time_val_Int_0 0))))
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert (forall ((Measure_time_Int_75 Int) (Measure_m1_Int_76 Int)) (=> (set.member (tuple Measure_time_Int_75 Measure_m1_Int_76) Measure) (exists ((time_val_Int_77 Int)) (and (= time_val_Int_77 Measure_time_Int_75) (set.member (tuple time_val_Int_77) time))))))
(check-sat)
(get-model)
