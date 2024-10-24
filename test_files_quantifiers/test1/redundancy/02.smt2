(set-logic HO_ALL)
(set-option :produce-models true)
(set-option :finite-model-find true)
(set-option :check-models true)
(set-option :sets-exp true)
(set-option :dag-thresh 0)
(set-option :uf-lazy-ll true)
(set-option :fmf-bound true)
(set-option :tlimit-per 20000)
(set-option :produce-models true)
(set-option :finite-model-find true)
(set-option :check-models true)
(set-option :sets-exp true)
(set-option :dag-thresh 0)
(set-option :uf-lazy-ll true)
(set-option :fmf-bound true)
(set-option :tlimit-per 20000)
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
(assert (exists ((A_time_Int_33 Int)) (and (exists ((Measure_time_Int_34 Int) (Measure_m1_Int_35 Int)) (and (and (and (not (exists ((C_time_Int_36 Int)) (and (and (>= C_time_Int_36 (+ A_time_Int_33 0)) (<= C_time_Int_36 (+ A_time_Int_33 15))) (set.member (tuple C_time_Int_36) C)))) (< Measure_m1_Int_35 20)) (= A_time_Int_33 Measure_time_Int_34)) (set.member (tuple Measure_time_Int_34 Measure_m1_Int_35) Measure))) (set.member (tuple A_time_Int_33) A))))
(assert (forall ((A_time_Int_1 Int)) (=> (set.member (tuple A_time_Int_1) A) (exists ((Measure_time_Int_2 Int) (Measure_m1_Int_3 Int)) (and (and (exists ((B_time_Int_4 Int)) (and (and (>= B_time_Int_4 (+ A_time_Int_1 0)) (<= B_time_Int_4 (+ A_time_Int_1 7))) (set.member (tuple B_time_Int_4) B))) (= A_time_Int_1 Measure_time_Int_2)) (set.member (tuple Measure_time_Int_2 Measure_m1_Int_3) Measure))))))
(assert (forall ((B_time_Int_15 Int)) (=> (set.member (tuple B_time_Int_15) B) (exists ((Measure_time_Int_16 Int) (Measure_m1_Int_17 Int)) (and (and (exists ((C_time_Int_18 Int)) (and (and (>= C_time_Int_18 (+ B_time_Int_15 0)) (<= C_time_Int_18 (+ B_time_Int_15 7))) (set.member (tuple C_time_Int_18) C))) (= B_time_Int_15 Measure_time_Int_16)) (set.member (tuple Measure_time_Int_16 Measure_m1_Int_17) Measure))))))
(assert (forall ((A_time_Int_49 Int)) (=> (set.member (tuple A_time_Int_49) A) (exists ((Measure_time_Int_50 Int) (Measure_m1_Int_51 Int)) (and (and (exists ((not_C_start_time_Int_53 Int) (not_C_end_time_Int_54 Int)) (and (and (= not_C_end_time_Int_54 (+ A_time_Int_49 11)) (= not_C_start_time_Int_53 (+ A_time_Int_49 0))) (set.member (tuple not_C_start_time_Int_53 not_C_end_time_Int_54) not_C))) (= A_time_Int_49 Measure_time_Int_50)) (set.member (tuple Measure_time_Int_50 Measure_m1_Int_51) Measure))))))
(assert (and (and (forall ((C_time_Int_77 Int) (not_C_start_time_Int_78 Int) (not_C_end_time_Int_79 Int)) (=> (and (set.member (tuple not_C_start_time_Int_78 not_C_end_time_Int_79) not_C) (set.member (tuple C_time_Int_77) C)) (not (and (<= C_time_Int_77 not_C_end_time_Int_79) (<= not_C_start_time_Int_78 C_time_Int_77))))) (and (forall ((B_time_Int_74 Int) (not_B_start_time_Int_75 Int) (not_B_end_time_Int_76 Int)) (=> (and (set.member (tuple not_B_start_time_Int_75 not_B_end_time_Int_76) not_B) (set.member (tuple B_time_Int_74) B)) (not (and (<= B_time_Int_74 not_B_end_time_Int_76) (<= not_B_start_time_Int_75 B_time_Int_74))))) (forall ((A_time_Int_71 Int) (not_A_start_time_Int_72 Int) (not_A_end_time_Int_73 Int)) (=> (and (set.member (tuple not_A_start_time_Int_72 not_A_end_time_Int_73) not_A) (set.member (tuple A_time_Int_71) A)) (not (and (<= A_time_Int_71 not_A_end_time_Int_73) (<= not_A_start_time_Int_72 A_time_Int_71))))))) (forall ((Measure_time_Int_67 Int) (Measure_m1_Int_68 Int) (Measure_time_Int_69 Int) (Measure_m1_Int_70 Int)) (=> (and (set.member (tuple Measure_time_Int_69 Measure_m1_Int_70) Measure) (set.member (tuple Measure_time_Int_67 Measure_m1_Int_68) Measure)) (=> (= Measure_time_Int_67 Measure_time_Int_69) (and (= Measure_m1_Int_68 Measure_m1_Int_70) (= Measure_time_Int_67 Measure_time_Int_69)))))))
(assert (=> (exists ((A_time_Int_80 Int)) (and true (set.member (tuple A_time_Int_80) A))) (and (exists ((A_time_Int_83 Int)) (and (forall ((A_time_Int_84 Int)) (=> (set.member (tuple A_time_Int_84) A) (<= A_time_Int_84 A_time_Int_83))) (set.member (tuple A_time_Int_83) A))) (exists ((A_time_Int_81 Int)) (and (forall ((A_time_Int_82 Int)) (=> (set.member (tuple A_time_Int_82) A) (>= A_time_Int_82 A_time_Int_81))) (set.member (tuple A_time_Int_81) A))))))
(assert (=> (exists ((B_time_Int_85 Int)) (and true (set.member (tuple B_time_Int_85) B))) (and (exists ((B_time_Int_88 Int)) (and (forall ((B_time_Int_89 Int)) (=> (set.member (tuple B_time_Int_89) B) (<= B_time_Int_89 B_time_Int_88))) (set.member (tuple B_time_Int_88) B))) (exists ((B_time_Int_86 Int)) (and (forall ((B_time_Int_87 Int)) (=> (set.member (tuple B_time_Int_87) B) (>= B_time_Int_87 B_time_Int_86))) (set.member (tuple B_time_Int_86) B))))))
(assert (=> (exists ((C_time_Int_90 Int)) (and true (set.member (tuple C_time_Int_90) C))) (and (exists ((C_time_Int_93 Int)) (and (forall ((C_time_Int_94 Int)) (=> (set.member (tuple C_time_Int_94) C) (<= C_time_Int_94 C_time_Int_93))) (set.member (tuple C_time_Int_93) C))) (exists ((C_time_Int_91 Int)) (and (forall ((C_time_Int_92 Int)) (=> (set.member (tuple C_time_Int_92) C) (>= C_time_Int_92 C_time_Int_91))) (set.member (tuple C_time_Int_91) C))))))
(assert (forall ((time_val_Int_0 Int)) (=> (set.member (tuple time_val_Int_0) time) (>= time_val_Int_0 0))))
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert (forall ((Measure_time_Int_95 Int) (Measure_m1_Int_96 Int)) (=> (set.member (tuple Measure_time_Int_95 Measure_m1_Int_96) Measure) (exists ((time_val_Int_97 Int)) (and (= time_val_Int_97 Measure_time_Int_95) (set.member (tuple time_val_Int_97) time))))))
(check-sat)
