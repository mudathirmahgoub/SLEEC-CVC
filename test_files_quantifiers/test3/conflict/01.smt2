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
(assert (exists ((C_time_Int_35 Int) (Measure_time_Int_36 Int) (Measure_m1_Int_37 Int)) (and (= C_time_Int_35 Measure_time_Int_36) (and (set.member (tuple Measure_time_Int_36 Measure_m1_Int_37) Measure) (set.member (tuple C_time_Int_35) C)))))
(assert (forall ((A_time_Int_1 Int)) (=> (set.member (tuple A_time_Int_1) A) (exists ((Measure_time_Int_2 Int) (Measure_m1_Int_3 Int)) (and (and (=> true (or (exists ((Measure_time_Int_5 Int) (Measure_m1_Int_6 Int)) (and (and (exists ((D_time_Int_7 Int)) (and (and (>= D_time_Int_7 (+ Measure_time_Int_5 0)) (<= D_time_Int_7 (+ Measure_time_Int_5 5))) (set.member (tuple D_time_Int_7) D))) (= (+ Measure_time_Int_2 10) Measure_time_Int_5)) (set.member (tuple Measure_time_Int_5 Measure_m1_Int_6) Measure))) (exists ((B_time_Int_4 Int)) (and (and (>= B_time_Int_4 (+ A_time_Int_1 0)) (<= B_time_Int_4 (+ A_time_Int_1 10))) (set.member (tuple B_time_Int_4) B))))) (= A_time_Int_1 Measure_time_Int_2)) (set.member (tuple Measure_time_Int_2 Measure_m1_Int_3) Measure))))))
(assert (forall ((C_time_Int_21 Int)) (=> (set.member (tuple C_time_Int_21) C) (exists ((Measure_time_Int_22 Int) (Measure_m1_Int_23 Int)) (and (and (=> true (or (exists ((Measure_time_Int_25 Int) (Measure_m1_Int_26 Int)) (and (and (exists ((B_time_Int_27 Int)) (and (and (>= B_time_Int_27 (+ Measure_time_Int_25 0)) (<= B_time_Int_27 (+ Measure_time_Int_25 5))) (set.member (tuple B_time_Int_27) B))) (= (+ Measure_time_Int_22 10) Measure_time_Int_25)) (set.member (tuple Measure_time_Int_25 Measure_m1_Int_26) Measure))) (exists ((A_time_Int_24 Int)) (and (and (>= A_time_Int_24 (+ C_time_Int_21 1)) (<= A_time_Int_24 (+ C_time_Int_21 10))) (set.member (tuple A_time_Int_24) A))))) (= C_time_Int_21 Measure_time_Int_22)) (set.member (tuple Measure_time_Int_22 Measure_m1_Int_23) Measure))))))
(assert (forall ((B_time_Int_41 Int)) (=> (set.member (tuple B_time_Int_41) B) (exists ((Measure_time_Int_42 Int) (Measure_m1_Int_43 Int)) (and (and (exists ((D_time_Int_44 Int)) (and (and (>= D_time_Int_44 (+ B_time_Int_41 0)) (<= D_time_Int_44 (+ B_time_Int_41 1))) (set.member (tuple D_time_Int_44) D))) (= B_time_Int_41 Measure_time_Int_42)) (set.member (tuple Measure_time_Int_42 Measure_m1_Int_43) Measure))))))
(assert (and (and (forall ((D_time_Int_94 Int) (not_D_start_time_Int_95 Int) (not_D_end_time_Int_96 Int)) (=> (and (set.member (tuple not_D_start_time_Int_95 not_D_end_time_Int_96) not_D) (set.member (tuple D_time_Int_94) D)) (not (and (<= D_time_Int_94 not_D_end_time_Int_96) (<= not_D_start_time_Int_95 D_time_Int_94))))) (and (forall ((C_time_Int_91 Int) (not_C_start_time_Int_92 Int) (not_C_end_time_Int_93 Int)) (=> (and (set.member (tuple not_C_start_time_Int_92 not_C_end_time_Int_93) not_C) (set.member (tuple C_time_Int_91) C)) (not (and (<= C_time_Int_91 not_C_end_time_Int_93) (<= not_C_start_time_Int_92 C_time_Int_91))))) (and (forall ((B_time_Int_88 Int) (not_B_start_time_Int_89 Int) (not_B_end_time_Int_90 Int)) (=> (and (set.member (tuple not_B_start_time_Int_89 not_B_end_time_Int_90) not_B) (set.member (tuple B_time_Int_88) B)) (not (and (<= B_time_Int_88 not_B_end_time_Int_90) (<= not_B_start_time_Int_89 B_time_Int_88))))) (forall ((A_time_Int_85 Int) (not_A_start_time_Int_86 Int) (not_A_end_time_Int_87 Int)) (=> (and (set.member (tuple not_A_start_time_Int_86 not_A_end_time_Int_87) not_A) (set.member (tuple A_time_Int_85) A)) (not (and (<= A_time_Int_85 not_A_end_time_Int_87) (<= not_A_start_time_Int_86 A_time_Int_85)))))))) (forall ((Measure_time_Int_81 Int) (Measure_m1_Int_82 Int) (Measure_time_Int_83 Int) (Measure_m1_Int_84 Int)) (=> (and (set.member (tuple Measure_time_Int_83 Measure_m1_Int_84) Measure) (set.member (tuple Measure_time_Int_81 Measure_m1_Int_82) Measure)) (=> (= Measure_time_Int_81 Measure_time_Int_83) (and (= Measure_m1_Int_82 Measure_m1_Int_84) (= Measure_time_Int_81 Measure_time_Int_83)))))))
(assert (=> (exists ((A_time_Int_61 Int)) (and true (set.member (tuple A_time_Int_61) A))) (and (exists ((A_time_Int_64 Int)) (and (forall ((A_time_Int_65 Int)) (=> (set.member (tuple A_time_Int_65) A) (<= A_time_Int_65 A_time_Int_64))) (set.member (tuple A_time_Int_64) A))) (exists ((A_time_Int_62 Int)) (and (forall ((A_time_Int_63 Int)) (=> (set.member (tuple A_time_Int_63) A) (>= A_time_Int_63 A_time_Int_62))) (set.member (tuple A_time_Int_62) A))))))
(assert (=> (exists ((B_time_Int_66 Int)) (and true (set.member (tuple B_time_Int_66) B))) (and (exists ((B_time_Int_69 Int)) (and (forall ((B_time_Int_70 Int)) (=> (set.member (tuple B_time_Int_70) B) (<= B_time_Int_70 B_time_Int_69))) (set.member (tuple B_time_Int_69) B))) (exists ((B_time_Int_67 Int)) (and (forall ((B_time_Int_68 Int)) (=> (set.member (tuple B_time_Int_68) B) (>= B_time_Int_68 B_time_Int_67))) (set.member (tuple B_time_Int_67) B))))))
(assert (=> (exists ((C_time_Int_71 Int)) (and true (set.member (tuple C_time_Int_71) C))) (and (exists ((C_time_Int_74 Int)) (and (forall ((C_time_Int_75 Int)) (=> (set.member (tuple C_time_Int_75) C) (<= C_time_Int_75 C_time_Int_74))) (set.member (tuple C_time_Int_74) C))) (exists ((C_time_Int_72 Int)) (and (forall ((C_time_Int_73 Int)) (=> (set.member (tuple C_time_Int_73) C) (>= C_time_Int_73 C_time_Int_72))) (set.member (tuple C_time_Int_72) C))))))
(assert (=> (exists ((D_time_Int_76 Int)) (and true (set.member (tuple D_time_Int_76) D))) (and (exists ((D_time_Int_79 Int)) (and (forall ((D_time_Int_80 Int)) (=> (set.member (tuple D_time_Int_80) D) (<= D_time_Int_80 D_time_Int_79))) (set.member (tuple D_time_Int_79) D))) (exists ((D_time_Int_77 Int)) (and (forall ((D_time_Int_78 Int)) (=> (set.member (tuple D_time_Int_78) D) (>= D_time_Int_78 D_time_Int_77))) (set.member (tuple D_time_Int_77) D))))))
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
(assert (forall ((Measure_time_Int_97 Int) (Measure_m1_Int_98 Int)) (=> (set.member (tuple Measure_time_Int_97 Measure_m1_Int_98) Measure) (exists ((time_val_Int_99 Int)) (and (= time_val_Int_99 Measure_time_Int_97) (set.member (tuple time_val_Int_99) time))))))
(check-sat)
(get-model)
