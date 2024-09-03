(set-logic HO_ALL)
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
(assert (exists ((A_time_Int_9 Int) (Measure_time_Int_10 Int) (Measure_m1_Int_11 Int)) (and (= A_time_Int_9 Measure_time_Int_10) (and (set.member (tuple Measure_time_Int_10 Measure_m1_Int_11) Measure) (set.member (tuple A_time_Int_9) A)))))
(assert (forall ((A_time_Int_1 Int)) (=> (set.member (tuple A_time_Int_1) A) (exists ((Measure_time_Int_2 Int) (Measure_m1_Int_3 Int)) (and (and (exists ((B_time_Int_4 Int)) (and (and (>= B_time_Int_4 (+ A_time_Int_1 0)) (<= B_time_Int_4 (+ A_time_Int_1 7))) (set.member (tuple B_time_Int_4) B))) (= A_time_Int_1 Measure_time_Int_2)) (set.member (tuple Measure_time_Int_2 Measure_m1_Int_3) Measure))))))
(assert (forall ((B_time_Int_15 Int)) (=> (set.member (tuple B_time_Int_15) B) (exists ((Measure_time_Int_16 Int) (Measure_m1_Int_17 Int)) (and (and (exists ((C_time_Int_18 Int)) (and (and (>= C_time_Int_18 (+ B_time_Int_15 0)) (<= C_time_Int_18 (+ B_time_Int_15 7))) (set.member (tuple C_time_Int_18) C))) (= B_time_Int_15 Measure_time_Int_16)) (set.member (tuple Measure_time_Int_16 Measure_m1_Int_17) Measure))))))
(assert (forall ((A_time_Int_29 Int)) (=> (set.member (tuple A_time_Int_29) A) (exists ((Measure_time_Int_30 Int) (Measure_m1_Int_31 Int)) (and (and (or (exists ((C_time_Int_32 Int)) (and (and (>= C_time_Int_32 (+ A_time_Int_29 0)) (<= C_time_Int_32 (+ A_time_Int_29 15))) (set.member (tuple C_time_Int_32) C))) (not (< Measure_m1_Int_31 20))) (= A_time_Int_29 Measure_time_Int_30)) (set.member (tuple Measure_time_Int_30 Measure_m1_Int_31) Measure))))))
(assert (forall ((A_time_Int_49 Int)) (=> (set.member (tuple A_time_Int_49) A) (exists ((Measure_time_Int_50 Int) (Measure_m1_Int_51 Int)) (and (and (exists ((not_C_start_time_Int_53 Int) (not_C_end_time_Int_54 Int)) (and (and (= not_C_end_time_Int_54 (+ A_time_Int_49 11)) (= not_C_start_time_Int_53 (+ A_time_Int_49 0))) (set.member (tuple not_C_start_time_Int_53 not_C_end_time_Int_54) not_C))) (= A_time_Int_49 Measure_time_Int_50)) (set.member (tuple Measure_time_Int_50 Measure_m1_Int_51) Measure))))))
(assert (forall ((Measure_time_Int_79 Int) (Measure_m1_Int_80 Int) (Measure_time_Int_81 Int) (Measure_m1_Int_82 Int)) (=> (and (set.member (tuple Measure_time_Int_81 Measure_m1_Int_82) Measure) (set.member (tuple Measure_time_Int_79 Measure_m1_Int_80) Measure)) (=> (= Measure_time_Int_79 Measure_time_Int_81) (and (= Measure_m1_Int_80 Measure_m1_Int_82) (= Measure_time_Int_79 Measure_time_Int_81))))))
(assert (forall ((A_time_Int_67 Int)) (=> (set.member (tuple A_time_Int_67) A) (or (exists ((A_time_Int_69 Int)) (and (and (forall ((A_time_Int_70 Int)) (=> (set.member (tuple A_time_Int_70) A) (<= A_time_Int_70 A_time_Int_67))) (> A_time_Int_69 A_time_Int_67)) (set.member (tuple A_time_Int_69) A))) (forall ((A_time_Int_68 Int)) (=> (set.member (tuple A_time_Int_68) A) (<= A_time_Int_68 A_time_Int_67)))))))
(assert (forall ((B_time_Int_71 Int)) (=> (set.member (tuple B_time_Int_71) B) (or (exists ((B_time_Int_73 Int)) (and (and (forall ((B_time_Int_74 Int)) (=> (set.member (tuple B_time_Int_74) B) (<= B_time_Int_74 B_time_Int_71))) (> B_time_Int_73 B_time_Int_71)) (set.member (tuple B_time_Int_73) B))) (forall ((B_time_Int_72 Int)) (=> (set.member (tuple B_time_Int_72) B) (<= B_time_Int_72 B_time_Int_71)))))))
(assert (forall ((C_time_Int_75 Int)) (=> (set.member (tuple C_time_Int_75) C) (or (exists ((C_time_Int_77 Int)) (and (and (forall ((C_time_Int_78 Int)) (=> (set.member (tuple C_time_Int_78) C) (<= C_time_Int_78 C_time_Int_75))) (> C_time_Int_77 C_time_Int_75)) (set.member (tuple C_time_Int_77) C))) (forall ((C_time_Int_76 Int)) (=> (set.member (tuple C_time_Int_76) C) (<= C_time_Int_76 C_time_Int_75)))))))
(assert (forall ((time_val_Int_0 Int)) (=> (set.member (tuple time_val_Int_0) time) (>= time_val_Int_0 0))))
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert (forall ((Measure_time_Int_83 Int) (Measure_m1_Int_84 Int)) (=> (set.member (tuple Measure_time_Int_83 Measure_m1_Int_84) Measure) (exists ((time_val_Int_85 Int)) (and (= time_val_Int_85 Measure_time_Int_83) (set.member (tuple time_val_Int_85) time))))))
(check-sat)
(get-model)
