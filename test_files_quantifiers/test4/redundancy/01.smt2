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
(assert (exists ((C_time_Int_28 Int)) (and (exists ((Measure_time_Int_29 Int) (Measure_m1_Int_30 Int)) (and (and (not (=> true (or (forall ((Measure_time_Int_32 Int) (Measure_m1_Int_33 Int)) (=> (set.member (tuple Measure_time_Int_32 Measure_m1_Int_33) Measure) (=> (= (+ Measure_time_Int_29 10) Measure_time_Int_32) (exists ((B_time_Int_34 Int)) (and (and (>= B_time_Int_34 (+ Measure_time_Int_32 0)) (<= B_time_Int_34 (+ Measure_time_Int_32 5))) (set.member (tuple B_time_Int_34) B)))))) (exists ((A_time_Int_31 Int)) (and (and (>= A_time_Int_31 (+ C_time_Int_28 1)) (<= A_time_Int_31 (+ C_time_Int_28 10))) (set.member (tuple A_time_Int_31) A)))))) (= C_time_Int_28 Measure_time_Int_29)) (set.member (tuple Measure_time_Int_29 Measure_m1_Int_30) Measure))) (set.member (tuple C_time_Int_28) C))))
(assert (forall ((A_time_Int_1 Int)) (=> (set.member (tuple A_time_Int_1) A) (exists ((Measure_time_Int_2 Int) (Measure_m1_Int_3 Int)) (and (and (=> true (or (exists ((Measure_time_Int_5 Int) (Measure_m1_Int_6 Int)) (and (and (exists ((D_time_Int_7 Int)) (and (and (>= D_time_Int_7 (+ Measure_time_Int_5 0)) (<= D_time_Int_7 (+ Measure_time_Int_5 5))) (set.member (tuple D_time_Int_7) D))) (= (+ Measure_time_Int_2 10) Measure_time_Int_5)) (set.member (tuple Measure_time_Int_5 Measure_m1_Int_6) Measure))) (exists ((B_time_Int_4 Int)) (and (and (>= B_time_Int_4 (+ A_time_Int_1 0)) (<= B_time_Int_4 (+ A_time_Int_1 10))) (set.member (tuple B_time_Int_4) B))))) (= A_time_Int_1 Measure_time_Int_2)) (set.member (tuple Measure_time_Int_2 Measure_m1_Int_3) Measure))))))
(assert (forall ((B_time_Int_41 Int)) (=> (set.member (tuple B_time_Int_41) B) (exists ((Measure_time_Int_42 Int) (Measure_m1_Int_43 Int)) (and (and (exists ((D_time_Int_44 Int)) (and (and (>= D_time_Int_44 (+ B_time_Int_41 0)) (<= D_time_Int_44 (+ B_time_Int_41 1))) (set.member (tuple D_time_Int_44) D))) (= B_time_Int_41 Measure_time_Int_42)) (set.member (tuple Measure_time_Int_42 Measure_m1_Int_43) Measure))))))
(assert (and (and (forall ((D_time_Int_74 Int) (not_D_start_time_Int_75 Int) (not_D_end_time_Int_76 Int)) (=> (and (set.member (tuple not_D_start_time_Int_75 not_D_end_time_Int_76) not_D) (set.member (tuple D_time_Int_74) D)) (not (and (<= D_time_Int_74 not_D_end_time_Int_76) (<= not_D_start_time_Int_75 D_time_Int_74))))) (and (forall ((C_time_Int_71 Int) (not_C_start_time_Int_72 Int) (not_C_end_time_Int_73 Int)) (=> (and (set.member (tuple not_C_start_time_Int_72 not_C_end_time_Int_73) not_C) (set.member (tuple C_time_Int_71) C)) (not (and (<= C_time_Int_71 not_C_end_time_Int_73) (<= not_C_start_time_Int_72 C_time_Int_71))))) (and (forall ((B_time_Int_68 Int) (not_B_start_time_Int_69 Int) (not_B_end_time_Int_70 Int)) (=> (and (set.member (tuple not_B_start_time_Int_69 not_B_end_time_Int_70) not_B) (set.member (tuple B_time_Int_68) B)) (not (and (<= B_time_Int_68 not_B_end_time_Int_70) (<= not_B_start_time_Int_69 B_time_Int_68))))) (forall ((A_time_Int_65 Int) (not_A_start_time_Int_66 Int) (not_A_end_time_Int_67 Int)) (=> (and (set.member (tuple not_A_start_time_Int_66 not_A_end_time_Int_67) not_A) (set.member (tuple A_time_Int_65) A)) (not (and (<= A_time_Int_65 not_A_end_time_Int_67) (<= not_A_start_time_Int_66 A_time_Int_65)))))))) (forall ((Measure_time_Int_61 Int) (Measure_m1_Int_62 Int) (Measure_time_Int_63 Int) (Measure_m1_Int_64 Int)) (=> (and (set.member (tuple Measure_time_Int_63 Measure_m1_Int_64) Measure) (set.member (tuple Measure_time_Int_61 Measure_m1_Int_62) Measure)) (=> (= Measure_time_Int_61 Measure_time_Int_63) (and (= Measure_m1_Int_62 Measure_m1_Int_64) (= Measure_time_Int_61 Measure_time_Int_63)))))))
(assert (=> (exists ((A_time_Int_77 Int)) (and true (set.member (tuple A_time_Int_77) A))) (and (exists ((A_time_Int_80 Int)) (and (forall ((A_time_Int_81 Int)) (=> (set.member (tuple A_time_Int_81) A) (<= A_time_Int_81 A_time_Int_80))) (set.member (tuple A_time_Int_80) A))) (exists ((A_time_Int_78 Int)) (and (forall ((A_time_Int_79 Int)) (=> (set.member (tuple A_time_Int_79) A) (>= A_time_Int_79 A_time_Int_78))) (set.member (tuple A_time_Int_78) A))))))
(assert (=> (exists ((B_time_Int_82 Int)) (and true (set.member (tuple B_time_Int_82) B))) (and (exists ((B_time_Int_85 Int)) (and (forall ((B_time_Int_86 Int)) (=> (set.member (tuple B_time_Int_86) B) (<= B_time_Int_86 B_time_Int_85))) (set.member (tuple B_time_Int_85) B))) (exists ((B_time_Int_83 Int)) (and (forall ((B_time_Int_84 Int)) (=> (set.member (tuple B_time_Int_84) B) (>= B_time_Int_84 B_time_Int_83))) (set.member (tuple B_time_Int_83) B))))))
(assert (=> (exists ((C_time_Int_87 Int)) (and true (set.member (tuple C_time_Int_87) C))) (and (exists ((C_time_Int_90 Int)) (and (forall ((C_time_Int_91 Int)) (=> (set.member (tuple C_time_Int_91) C) (<= C_time_Int_91 C_time_Int_90))) (set.member (tuple C_time_Int_90) C))) (exists ((C_time_Int_88 Int)) (and (forall ((C_time_Int_89 Int)) (=> (set.member (tuple C_time_Int_89) C) (>= C_time_Int_89 C_time_Int_88))) (set.member (tuple C_time_Int_88) C))))))
(assert (=> (exists ((D_time_Int_92 Int)) (and true (set.member (tuple D_time_Int_92) D))) (and (exists ((D_time_Int_95 Int)) (and (forall ((D_time_Int_96 Int)) (=> (set.member (tuple D_time_Int_96) D) (<= D_time_Int_96 D_time_Int_95))) (set.member (tuple D_time_Int_95) D))) (exists ((D_time_Int_93 Int)) (and (forall ((D_time_Int_94 Int)) (=> (set.member (tuple D_time_Int_94) D) (>= D_time_Int_94 D_time_Int_93))) (set.member (tuple D_time_Int_93) D))))))
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
