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
(declare-const D (Set (Tuple Int)))
(declare-const not_D (Set (Tuple Int Int)))
(declare-const Measure (Set (Tuple Int Int)))
(assert (exists ((C_time_Int_28 Int)) (and (exists ((Measure_time_Int_29 Int) (Measure_m1_Int_30 Int)) (and (and (not (=> true (or (forall ((Measure_time_Int_32 Int) (Measure_m1_Int_33 Int)) (=> (set.member (tuple Measure_time_Int_32 Measure_m1_Int_33) Measure) (=> (= (+ Measure_time_Int_29 10) Measure_time_Int_32) (exists ((B_time_Int_34 Int)) (and (and (>= B_time_Int_34 (+ Measure_time_Int_32 0)) (<= B_time_Int_34 (+ Measure_time_Int_32 5))) (set.member (tuple B_time_Int_34) B)))))) (exists ((A_time_Int_31 Int)) (and (and (>= A_time_Int_31 (+ C_time_Int_28 1)) (<= A_time_Int_31 (+ C_time_Int_28 10))) (set.member (tuple A_time_Int_31) A)))))) (= C_time_Int_28 Measure_time_Int_29)) (set.member (tuple Measure_time_Int_29 Measure_m1_Int_30) Measure))) (set.member (tuple C_time_Int_28) C))))
(assert (forall ((A_time_Int_1 Int)) (=> (set.member (tuple A_time_Int_1) A) (exists ((Measure_time_Int_2 Int) (Measure_m1_Int_3 Int)) (and (and (=> true (or (exists ((Measure_time_Int_5 Int) (Measure_m1_Int_6 Int)) (and (and (exists ((D_time_Int_7 Int)) (and (and (>= D_time_Int_7 (+ Measure_time_Int_5 0)) (<= D_time_Int_7 (+ Measure_time_Int_5 5))) (set.member (tuple D_time_Int_7) D))) (= (+ Measure_time_Int_2 10) Measure_time_Int_5)) (set.member (tuple Measure_time_Int_5 Measure_m1_Int_6) Measure))) (exists ((B_time_Int_4 Int)) (and (and (>= B_time_Int_4 (+ A_time_Int_1 0)) (<= B_time_Int_4 (+ A_time_Int_1 10))) (set.member (tuple B_time_Int_4) B))))) (= A_time_Int_1 Measure_time_Int_2)) (set.member (tuple Measure_time_Int_2 Measure_m1_Int_3) Measure))))))
(assert (forall ((B_time_Int_41 Int)) (=> (set.member (tuple B_time_Int_41) B) (exists ((Measure_time_Int_42 Int) (Measure_m1_Int_43 Int)) (and (and (exists ((D_time_Int_44 Int)) (and (and (>= D_time_Int_44 (+ B_time_Int_41 0)) (<= D_time_Int_44 (+ B_time_Int_41 1))) (set.member (tuple D_time_Int_44) D))) (= B_time_Int_41 Measure_time_Int_42)) (set.member (tuple Measure_time_Int_42 Measure_m1_Int_43) Measure))))))
(assert (and (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_4 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_4) ((_ tuple.select 2) tuple_4)) (<= ((_ tuple.select 1) tuple_4) ((_ tuple.select 0) tuple_4)))))) (rel.product D not_D))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_3 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_3) ((_ tuple.select 2) tuple_3)) (<= ((_ tuple.select 1) tuple_3) ((_ tuple.select 0) tuple_3)))))) (rel.product C not_C))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_2 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_2) ((_ tuple.select 2) tuple_2)) (<= ((_ tuple.select 1) tuple_2) ((_ tuple.select 0) tuple_2)))))) (rel.product B not_B))) (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_1 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_1) ((_ tuple.select 2) tuple_1)) (<= ((_ tuple.select 1) tuple_1) ((_ tuple.select 0) tuple_1)))))) (rel.product A not_A)))))) (forall ((Measure_time_Int_61 Int) (Measure_m1_Int_62 Int) (Measure_time_Int_63 Int) (Measure_m1_Int_64 Int)) (=> (and (set.member (tuple Measure_time_Int_63 Measure_m1_Int_64) Measure) (set.member (tuple Measure_time_Int_61 Measure_m1_Int_62) Measure)) (=> (= Measure_time_Int_61 Measure_time_Int_63) (and (= Measure_m1_Int_62 Measure_m1_Int_64) (= Measure_time_Int_61 Measure_time_Int_63)))))))
(assert (forall ((A_time_Int_65 Int)) (=> (set.member (tuple A_time_Int_65) A) (or (exists ((A_time_Int_67 Int)) (and (and (forall ((A_time_Int_68 Int)) (=> (set.member (tuple A_time_Int_68) A) (<= A_time_Int_68 A_time_Int_65))) (> A_time_Int_67 A_time_Int_65)) (set.member (tuple A_time_Int_67) A))) (forall ((A_time_Int_66 Int)) (=> (set.member (tuple A_time_Int_66) A) (<= A_time_Int_66 A_time_Int_65)))))))
(assert (forall ((B_time_Int_69 Int)) (=> (set.member (tuple B_time_Int_69) B) (or (exists ((B_time_Int_71 Int)) (and (and (forall ((B_time_Int_72 Int)) (=> (set.member (tuple B_time_Int_72) B) (<= B_time_Int_72 B_time_Int_69))) (> B_time_Int_71 B_time_Int_69)) (set.member (tuple B_time_Int_71) B))) (forall ((B_time_Int_70 Int)) (=> (set.member (tuple B_time_Int_70) B) (<= B_time_Int_70 B_time_Int_69)))))))
(assert (forall ((C_time_Int_73 Int)) (=> (set.member (tuple C_time_Int_73) C) (or (exists ((C_time_Int_75 Int)) (and (and (forall ((C_time_Int_76 Int)) (=> (set.member (tuple C_time_Int_76) C) (<= C_time_Int_76 C_time_Int_73))) (> C_time_Int_75 C_time_Int_73)) (set.member (tuple C_time_Int_75) C))) (forall ((C_time_Int_74 Int)) (=> (set.member (tuple C_time_Int_74) C) (<= C_time_Int_74 C_time_Int_73)))))))
(assert (forall ((D_time_Int_77 Int)) (=> (set.member (tuple D_time_Int_77) D) (or (exists ((D_time_Int_79 Int)) (and (and (forall ((D_time_Int_80 Int)) (=> (set.member (tuple D_time_Int_80) D) (<= D_time_Int_80 D_time_Int_77))) (> D_time_Int_79 D_time_Int_77)) (set.member (tuple D_time_Int_79) D))) (forall ((D_time_Int_78 Int)) (=> (set.member (tuple D_time_Int_78) D) (<= D_time_Int_78 D_time_Int_77)))))))
(assert (forall ((time_val_Int_0 Int)) (=> (set.member (tuple time_val_Int_0) time) (>= time_val_Int_0 0))))
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert (forall ((Measure_time_Int_81 Int) (Measure_m1_Int_82 Int)) (=> (set.member (tuple Measure_time_Int_81 Measure_m1_Int_82) Measure) (exists ((time_val_Int_83 Int)) (and (= time_val_Int_83 Measure_time_Int_81) (set.member (tuple time_val_Int_83) time))))))
(check-sat)
(get-model)