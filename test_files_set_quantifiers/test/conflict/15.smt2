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
(declare-const E (Set (Tuple Int)))
(declare-const not_E (Set (Tuple Int Int)))
(declare-const F (Set (Tuple Int)))
(declare-const not_F (Set (Tuple Int Int)))
(declare-const G (Set (Tuple Int)))
(declare-const not_G (Set (Tuple Int Int)))
(declare-const H (Set (Tuple Int)))
(declare-const not_H (Set (Tuple Int Int)))
(declare-const Measure (Set (Tuple Int Bool Int Bool)))
(assert (set.exists ((tuple_217 (Tuple Int Int Bool Int Bool))) (rel.product E Measure) (and ((_ tuple.select 2) tuple_217) (= ((_ tuple.select 0) tuple_217) ((_ tuple.select 1) tuple_217)))))
(assert (set.forall ((tuple_2 (Tuple Int))) A (set.exists ((tuple_3 (Tuple Int Bool Int Bool))) Measure (and (set.exists ((tuple_4 (Tuple Int))) B (and (>= ((_ tuple.select 0) tuple_4) (+ ((_ tuple.select 0) tuple_2) 0)) (<= ((_ tuple.select 0) tuple_4) (+ ((_ tuple.select 0) tuple_2) 0)))) (= ((_ tuple.select 0) tuple_2) ((_ tuple.select 0) tuple_3))))))
(assert (set.forall ((tuple_12 (Tuple Int))) A (set.exists ((tuple_13 (Tuple Int Bool Int Bool))) Measure (and (or (set.exists ((tuple_14 (Tuple Int))) B (and (>= ((_ tuple.select 0) tuple_14) (+ ((_ tuple.select 0) tuple_12) 0)) (<= ((_ tuple.select 0) tuple_14) (+ ((_ tuple.select 0) tuple_12) 0)))) (not ((_ tuple.select 1) tuple_13))) (= ((_ tuple.select 0) tuple_12) ((_ tuple.select 0) tuple_13))))))
(assert (set.forall ((tuple_25 (Tuple Int))) A (set.exists ((tuple_26 (Tuple Int Bool Int Bool))) Measure (and (and (=> (and true (and (not ((_ tuple.select 1) tuple_26)) true)) (set.exists ((tuple_27 (Tuple Int))) B (and (>= ((_ tuple.select 0) tuple_27) (+ ((_ tuple.select 0) tuple_25) 0)) (<= ((_ tuple.select 0) tuple_27) (+ ((_ tuple.select 0) tuple_25) 0))))) (=> (and ((_ tuple.select 1) tuple_26) true) true)) (= ((_ tuple.select 0) tuple_25) ((_ tuple.select 0) tuple_26))))))
(assert (set.forall ((tuple_35 (Tuple Int))) B (set.exists ((tuple_36 (Tuple Int Bool Int Bool))) Measure (and (or (set.exists ((tuple_37 (Tuple Int))) C (and (>= ((_ tuple.select 0) tuple_37) (+ ((_ tuple.select 0) tuple_35) 0)) (<= ((_ tuple.select 0) tuple_37) (+ ((_ tuple.select 0) tuple_35) 0)))) (not (> ((_ tuple.select 2) tuple_36) 50))) (= ((_ tuple.select 0) tuple_35) ((_ tuple.select 0) tuple_36))))))
(assert (set.forall ((tuple_48 (Tuple Int))) B (set.exists ((tuple_49 (Tuple Int Bool Int Bool))) Measure (and (or (set.exists ((tuple_50 (Tuple Int))) C (and (>= ((_ tuple.select 0) tuple_50) (+ ((_ tuple.select 0) tuple_48) 0)) (<= ((_ tuple.select 0) tuple_50) (+ ((_ tuple.select 0) tuple_48) 0)))) (not (> ((_ tuple.select 2) tuple_49) 100))) (= ((_ tuple.select 0) tuple_48) ((_ tuple.select 0) tuple_49))))))
(assert (set.forall ((tuple_61 (Tuple Int))) A (set.exists ((tuple_62 (Tuple Int Bool Int Bool))) Measure (and (or (set.exists ((tuple_63 (Tuple Int))) C (and (>= ((_ tuple.select 0) tuple_63) (+ ((_ tuple.select 0) tuple_61) 0)) (<= ((_ tuple.select 0) tuple_63) (+ ((_ tuple.select 0) tuple_61) 0)))) (not (> ((_ tuple.select 2) tuple_62) 50))) (= ((_ tuple.select 0) tuple_61) ((_ tuple.select 0) tuple_62))))))
(assert (set.forall ((tuple_74 (Tuple Int))) C (set.exists ((tuple_75 (Tuple Int Bool Int Bool))) Measure (and (set.exists ((tuple_76 (Tuple Int))) D (and (>= ((_ tuple.select 0) tuple_76) (+ ((_ tuple.select 0) tuple_74) 0)) (<= ((_ tuple.select 0) tuple_76) (+ ((_ tuple.select 0) tuple_74) 300)))) (= ((_ tuple.select 0) tuple_74) ((_ tuple.select 0) tuple_75))))))
(assert (set.forall ((tuple_84 (Tuple Int))) C (set.exists ((tuple_85 (Tuple Int Bool Int Bool))) Measure (and (set.exists ((tuple_86 (Tuple Int))) D (and (>= ((_ tuple.select 0) tuple_86) (+ ((_ tuple.select 0) tuple_84) 0)) (<= ((_ tuple.select 0) tuple_86) (+ ((_ tuple.select 0) tuple_84) 301)))) (= ((_ tuple.select 0) tuple_84) ((_ tuple.select 0) tuple_85))))))
(assert (set.forall ((tuple_94 (Tuple Int))) C (set.exists ((tuple_95 (Tuple Int Bool Int Bool))) Measure (and (=> true (or (set.exists ((tuple_97 (Tuple Int Bool Int Bool))) Measure (and (set.exists ((tuple_98 (Tuple Int))) D (and (>= ((_ tuple.select 0) tuple_98) (+ ((_ tuple.select 0) tuple_97) 0)) (<= ((_ tuple.select 0) tuple_98) (+ ((_ tuple.select 0) tuple_97) 51)))) (= (+ ((_ tuple.select 0) tuple_95) 250) ((_ tuple.select 0) tuple_97)))) (set.exists ((tuple_96 (Tuple Int))) D (and (>= ((_ tuple.select 0) tuple_96) (+ ((_ tuple.select 0) tuple_94) 0)) (<= ((_ tuple.select 0) tuple_96) (+ ((_ tuple.select 0) tuple_94) 250)))))) (= ((_ tuple.select 0) tuple_94) ((_ tuple.select 0) tuple_95))))))
(assert (set.forall ((tuple_108 (Tuple Int))) C (set.exists ((tuple_109 (Tuple Int Bool Int Bool))) Measure (and (=> true (or (set.exists ((tuple_111 (Tuple Int Bool Int Bool))) Measure (and (=> true (or (set.exists ((tuple_113 (Tuple Int Bool Int Bool))) Measure (and (set.exists ((tuple_114 (Tuple Int))) D (and (>= ((_ tuple.select 0) tuple_114) (+ ((_ tuple.select 0) tuple_113) 0)) (<= ((_ tuple.select 0) tuple_114) (+ ((_ tuple.select 0) tuple_113) 10)))) (= (+ ((_ tuple.select 0) tuple_111) 40) ((_ tuple.select 0) tuple_113)))) (set.exists ((tuple_112 (Tuple Int))) D (and (>= ((_ tuple.select 0) tuple_112) (+ ((_ tuple.select 0) tuple_111) 0)) (<= ((_ tuple.select 0) tuple_112) (+ ((_ tuple.select 0) tuple_111) 40)))))) (= (+ ((_ tuple.select 0) tuple_109) 250) ((_ tuple.select 0) tuple_111)))) (set.exists ((tuple_110 (Tuple Int))) D (and (>= ((_ tuple.select 0) tuple_110) (+ ((_ tuple.select 0) tuple_108) 0)) (<= ((_ tuple.select 0) tuple_110) (+ ((_ tuple.select 0) tuple_108) 250)))))) (= ((_ tuple.select 0) tuple_108) ((_ tuple.select 0) tuple_109))))))
(assert (set.forall ((tuple_126 (Tuple Int))) C (set.exists ((tuple_127 (Tuple Int Bool Int Bool))) Measure (and (=> true (or (set.exists ((tuple_129 (Tuple Int Bool Int Bool))) Measure (and (=> true (or (set.exists ((tuple_131 (Tuple Int Bool Int Bool))) Measure (and (and (=> (and true (and (not ((_ tuple.select 1) tuple_131)) true)) (set.exists ((tuple_132 (Tuple Int))) D (and (>= ((_ tuple.select 0) tuple_132) (+ ((_ tuple.select 0) tuple_131) 0)) (<= ((_ tuple.select 0) tuple_132) (+ ((_ tuple.select 0) tuple_131) 10))))) (=> (and ((_ tuple.select 1) tuple_131) true) true)) (= (+ ((_ tuple.select 0) tuple_129) 40) ((_ tuple.select 0) tuple_131)))) (set.exists ((tuple_130 (Tuple Int))) D (and (>= ((_ tuple.select 0) tuple_130) (+ ((_ tuple.select 0) tuple_129) 0)) (<= ((_ tuple.select 0) tuple_130) (+ ((_ tuple.select 0) tuple_129) 40)))))) (= (+ ((_ tuple.select 0) tuple_127) 250) ((_ tuple.select 0) tuple_129)))) (set.exists ((tuple_128 (Tuple Int))) D (and (>= ((_ tuple.select 0) tuple_128) (+ ((_ tuple.select 0) tuple_126) 0)) (<= ((_ tuple.select 0) tuple_128) (+ ((_ tuple.select 0) tuple_126) 250)))))) (= ((_ tuple.select 0) tuple_126) ((_ tuple.select 0) tuple_127))))))
(assert (set.forall ((tuple_144 (Tuple Int))) C (set.exists ((tuple_145 (Tuple Int Bool Int Bool))) Measure (and (set.exists ((tuple_146 (Tuple Int))) E (and (>= ((_ tuple.select 0) tuple_146) (+ ((_ tuple.select 0) tuple_144) 0)) (<= ((_ tuple.select 0) tuple_146) (+ ((_ tuple.select 0) tuple_144) 250)))) (= ((_ tuple.select 0) tuple_144) ((_ tuple.select 0) tuple_145))))))
(assert (set.forall ((tuple_154 (Tuple Int))) C (set.exists ((tuple_155 (Tuple Int Bool Int Bool))) Measure (and (=> true (or (set.exists ((tuple_157 (Tuple Int Bool Int Bool))) Measure (and (=> true (or (set.exists ((tuple_159 (Tuple Int Bool Int Bool))) Measure (and (=> true (or (set.exists ((tuple_161 (Tuple Int))) D (and (>= ((_ tuple.select 0) tuple_161) (+ ((_ tuple.select 0) tuple_159) 0)) (<= ((_ tuple.select 0) tuple_161) (+ ((_ tuple.select 0) tuple_159) 10)))) (set.exists ((tuple_160 (Tuple Int))) E (and (>= ((_ tuple.select 0) tuple_160) (+ ((_ tuple.select 0) tuple_159) 0)) (<= ((_ tuple.select 0) tuple_160) (+ ((_ tuple.select 0) tuple_159) 0)))))) (= (+ ((_ tuple.select 0) tuple_157) 40) ((_ tuple.select 0) tuple_159)))) (set.exists ((tuple_158 (Tuple Int))) D (and (>= ((_ tuple.select 0) tuple_158) (+ ((_ tuple.select 0) tuple_157) 0)) (<= ((_ tuple.select 0) tuple_158) (+ ((_ tuple.select 0) tuple_157) 40)))))) (= (+ ((_ tuple.select 0) tuple_155) 250) ((_ tuple.select 0) tuple_157)))) (set.exists ((tuple_156 (Tuple Int))) D (and (>= ((_ tuple.select 0) tuple_156) (+ ((_ tuple.select 0) tuple_154) 0)) (<= ((_ tuple.select 0) tuple_156) (+ ((_ tuple.select 0) tuple_154) 250)))))) (= ((_ tuple.select 0) tuple_154) ((_ tuple.select 0) tuple_155))))))
(assert (set.forall ((tuple_174 (Tuple Int))) E (set.exists ((tuple_175 (Tuple Int Bool Int Bool))) Measure (and (and (=> (and true (and (not ((_ tuple.select 1) tuple_175)) (and (not (> ((_ tuple.select 2) tuple_175) 2)) true))) (set.exists ((tuple_176 (Tuple Int))) F (and (>= ((_ tuple.select 0) tuple_176) (+ ((_ tuple.select 0) tuple_174) 0)) (<= ((_ tuple.select 0) tuple_176) (+ ((_ tuple.select 0) tuple_174) 5))))) (and (=> (and ((_ tuple.select 1) tuple_175) (and (not (> ((_ tuple.select 2) tuple_175) 2)) true)) (set.exists ((tuple_177 (Tuple Int))) G (and (>= ((_ tuple.select 0) tuple_177) (+ ((_ tuple.select 0) tuple_174) 0)) (<= ((_ tuple.select 0) tuple_177) (+ ((_ tuple.select 0) tuple_174) 10))))) (=> (and (> ((_ tuple.select 2) tuple_175) 2) true) (set.exists ((tuple_179 (Tuple Int Int))) not_G (and (= ((_ tuple.select 1) tuple_179) (+ ((_ tuple.select 0) tuple_174) 20)) (= ((_ tuple.select 0) tuple_179) (+ ((_ tuple.select 0) tuple_174) 0))))))) (= ((_ tuple.select 0) tuple_174) ((_ tuple.select 0) tuple_175))))))
(assert (set.forall ((tuple_190 (Tuple Int))) E (set.exists ((tuple_191 (Tuple Int Bool Int Bool))) Measure (and (or (and (=> (and true (and (not (> ((_ tuple.select 2) tuple_191) 2)) true)) (set.exists ((tuple_192 (Tuple Int))) G (and (>= ((_ tuple.select 0) tuple_192) (+ ((_ tuple.select 0) tuple_190) 0)) (<= ((_ tuple.select 0) tuple_192) (+ ((_ tuple.select 0) tuple_190) 10))))) (=> (and (> ((_ tuple.select 2) tuple_191) 2) true) (set.exists ((tuple_194 (Tuple Int Int))) not_G (and (= ((_ tuple.select 1) tuple_194) (+ ((_ tuple.select 0) tuple_190) 10)) (= ((_ tuple.select 0) tuple_194) (+ ((_ tuple.select 0) tuple_190) 0)))))) (not ((_ tuple.select 1) tuple_191))) (= ((_ tuple.select 0) tuple_190) ((_ tuple.select 0) tuple_191))))))
(assert (set.forall ((tuple_207 (Tuple Int))) E (set.exists ((tuple_208 (Tuple Int Bool Int Bool))) Measure (and (or (and (=> (and true (and (not (> ((_ tuple.select 2) tuple_208) 3)) true)) (set.exists ((tuple_209 (Tuple Int))) G (and (>= ((_ tuple.select 0) tuple_209) (+ ((_ tuple.select 0) tuple_207) 0)) (<= ((_ tuple.select 0) tuple_209) (+ ((_ tuple.select 0) tuple_207) 10))))) (=> (and (> ((_ tuple.select 2) tuple_208) 3) true) (set.exists ((tuple_211 (Tuple Int Int))) not_G (and (= ((_ tuple.select 1) tuple_211) (+ ((_ tuple.select 0) tuple_207) 10)) (= ((_ tuple.select 0) tuple_211) (+ ((_ tuple.select 0) tuple_207) 0)))))) (not ((_ tuple.select 1) tuple_208))) (= ((_ tuple.select 0) tuple_207) ((_ tuple.select 0) tuple_208))))))
(assert (set.forall ((tuple_224 (Tuple Int))) E (set.exists ((tuple_225 (Tuple Int Bool Int Bool))) Measure (and (or (and (=> (and true (and (not (> ((_ tuple.select 2) tuple_225) 1)) true)) (set.exists ((tuple_226 (Tuple Int))) G (and (>= ((_ tuple.select 0) tuple_226) (+ ((_ tuple.select 0) tuple_224) 0)) (<= ((_ tuple.select 0) tuple_226) (+ ((_ tuple.select 0) tuple_224) 10))))) (=> (and (> ((_ tuple.select 2) tuple_225) 1) true) (set.exists ((tuple_228 (Tuple Int Int))) not_G (and (= ((_ tuple.select 1) tuple_228) (+ ((_ tuple.select 0) tuple_224) 10)) (= ((_ tuple.select 0) tuple_228) (+ ((_ tuple.select 0) tuple_224) 0)))))) (not ((_ tuple.select 1) tuple_225))) (= ((_ tuple.select 0) tuple_224) ((_ tuple.select 0) tuple_225))))))
(assert (set.forall ((tuple_241 (Tuple Int))) F (set.exists ((tuple_242 (Tuple Int Bool Int Bool))) Measure (and (and (=> (and true (and (not ((_ tuple.select 3) tuple_242)) true)) (set.exists ((tuple_243 (Tuple Int))) G (and (>= ((_ tuple.select 0) tuple_243) (+ ((_ tuple.select 0) tuple_241) 0)) (<= ((_ tuple.select 0) tuple_243) (+ ((_ tuple.select 0) tuple_241) 5))))) (=> (and ((_ tuple.select 3) tuple_242) true) (set.exists ((tuple_244 (Tuple Int))) H (and (>= ((_ tuple.select 0) tuple_244) (+ ((_ tuple.select 0) tuple_241) 0)) (<= ((_ tuple.select 0) tuple_244) (+ ((_ tuple.select 0) tuple_241) 10)))))) (= ((_ tuple.select 0) tuple_241) ((_ tuple.select 0) tuple_242))))))
(assert (set.forall ((tuple_253 (Tuple Int))) H (set.exists ((tuple_254 (Tuple Int Bool Int Bool))) Measure (and (set.exists ((tuple_255 (Tuple Int))) F (and (>= ((_ tuple.select 0) tuple_255) (+ ((_ tuple.select 0) tuple_253) 0)) (<= ((_ tuple.select 0) tuple_255) (+ ((_ tuple.select 0) tuple_253) 10)))) (= ((_ tuple.select 0) tuple_253) ((_ tuple.select 0) tuple_254))))))
(assert (set.forall ((tuple_263 (Tuple Int))) H (set.exists ((tuple_264 (Tuple Int Bool Int Bool))) Measure (and (set.exists ((tuple_266 (Tuple Int Int))) not_F (and (= ((_ tuple.select 1) tuple_266) (+ ((_ tuple.select 0) tuple_263) 0)) (= ((_ tuple.select 0) tuple_266) (+ ((_ tuple.select 0) tuple_263) 0)))) (= ((_ tuple.select 0) tuple_263) ((_ tuple.select 0) tuple_264))))))
(assert (set.forall ((tuple_275 (Tuple Int))) F (set.exists ((tuple_276 (Tuple Int Bool Int Bool))) Measure (and (set.exists ((tuple_277 (Tuple Int))) G (>= ((_ tuple.select 0) tuple_277) ((_ tuple.select 0) tuple_275))) (= ((_ tuple.select 0) tuple_275) ((_ tuple.select 0) tuple_276))))))
(assert (and (and (forall ((H_time_Int_21 Int) (not_H_start_time_Int_22 Int) (not_H_end_time_Int_23 Int)) (=> (and (set.member (tuple not_H_start_time_Int_22 not_H_end_time_Int_23) not_H) (set.member (tuple H_time_Int_21) H)) (not (and (<= H_time_Int_21 not_H_end_time_Int_23) (<= not_H_start_time_Int_22 H_time_Int_21))))) (and (forall ((G_time_Int_18 Int) (not_G_start_time_Int_19 Int) (not_G_end_time_Int_20 Int)) (=> (and (set.member (tuple not_G_start_time_Int_19 not_G_end_time_Int_20) not_G) (set.member (tuple G_time_Int_18) G)) (not (and (<= G_time_Int_18 not_G_end_time_Int_20) (<= not_G_start_time_Int_19 G_time_Int_18))))) (and (forall ((F_time_Int_15 Int) (not_F_start_time_Int_16 Int) (not_F_end_time_Int_17 Int)) (=> (and (set.member (tuple not_F_start_time_Int_16 not_F_end_time_Int_17) not_F) (set.member (tuple F_time_Int_15) F)) (not (and (<= F_time_Int_15 not_F_end_time_Int_17) (<= not_F_start_time_Int_16 F_time_Int_15))))) (and (forall ((E_time_Int_12 Int) (not_E_start_time_Int_13 Int) (not_E_end_time_Int_14 Int)) (=> (and (set.member (tuple not_E_start_time_Int_13 not_E_end_time_Int_14) not_E) (set.member (tuple E_time_Int_12) E)) (not (and (<= E_time_Int_12 not_E_end_time_Int_14) (<= not_E_start_time_Int_13 E_time_Int_12))))) (and (forall ((D_time_Int_9 Int) (not_D_start_time_Int_10 Int) (not_D_end_time_Int_11 Int)) (=> (and (set.member (tuple not_D_start_time_Int_10 not_D_end_time_Int_11) not_D) (set.member (tuple D_time_Int_9) D)) (not (and (<= D_time_Int_9 not_D_end_time_Int_11) (<= not_D_start_time_Int_10 D_time_Int_9))))) (and (forall ((C_time_Int_6 Int) (not_C_start_time_Int_7 Int) (not_C_end_time_Int_8 Int)) (=> (and (set.member (tuple not_C_start_time_Int_7 not_C_end_time_Int_8) not_C) (set.member (tuple C_time_Int_6) C)) (not (and (<= C_time_Int_6 not_C_end_time_Int_8) (<= not_C_start_time_Int_7 C_time_Int_6))))) (and (forall ((B_time_Int_3 Int) (not_B_start_time_Int_4 Int) (not_B_end_time_Int_5 Int)) (=> (and (set.member (tuple not_B_start_time_Int_4 not_B_end_time_Int_5) not_B) (set.member (tuple B_time_Int_3) B)) (not (and (<= B_time_Int_3 not_B_end_time_Int_5) (<= not_B_start_time_Int_4 B_time_Int_3))))) (forall ((A_time_Int_0 Int) (not_A_start_time_Int_1 Int) (not_A_end_time_Int_2 Int)) (=> (and (set.member (tuple not_A_start_time_Int_1 not_A_end_time_Int_2) not_A) (set.member (tuple A_time_Int_0) A)) (not (and (<= A_time_Int_0 not_A_end_time_Int_2) (<= not_A_start_time_Int_1 A_time_Int_0)))))))))))) (set.forall ((tuple_325 (Tuple Int Bool Int Bool Int Bool Int Bool))) (rel.product Measure Measure) (=> (= ((_ tuple.select 0) tuple_325) ((_ tuple.select 4) tuple_325)) (and (= ((_ tuple.select 3) tuple_325) ((_ tuple.select 7) tuple_325)) (and (= ((_ tuple.select 2) tuple_325) ((_ tuple.select 6) tuple_325)) (and (= ((_ tuple.select 1) tuple_325) ((_ tuple.select 5) tuple_325)) (= ((_ tuple.select 0) tuple_325) ((_ tuple.select 4) tuple_325)))))))))
(assert (=> (set.exists ((tuple_285 (Tuple Int))) A true) (and (set.exists ((tuple_288 (Tuple Int))) A (set.forall ((tuple_289 (Tuple Int))) A (<= ((_ tuple.select 0) tuple_289) ((_ tuple.select 0) tuple_288)))) (set.exists ((tuple_286 (Tuple Int))) A (set.forall ((tuple_287 (Tuple Int))) A (>= ((_ tuple.select 0) tuple_287) ((_ tuple.select 0) tuple_286)))))))
(assert (=> (set.exists ((tuple_290 (Tuple Int))) B true) (and (set.exists ((tuple_293 (Tuple Int))) B (set.forall ((tuple_294 (Tuple Int))) B (<= ((_ tuple.select 0) tuple_294) ((_ tuple.select 0) tuple_293)))) (set.exists ((tuple_291 (Tuple Int))) B (set.forall ((tuple_292 (Tuple Int))) B (>= ((_ tuple.select 0) tuple_292) ((_ tuple.select 0) tuple_291)))))))
(assert (=> (set.exists ((tuple_295 (Tuple Int))) C true) (and (set.exists ((tuple_298 (Tuple Int))) C (set.forall ((tuple_299 (Tuple Int))) C (<= ((_ tuple.select 0) tuple_299) ((_ tuple.select 0) tuple_298)))) (set.exists ((tuple_296 (Tuple Int))) C (set.forall ((tuple_297 (Tuple Int))) C (>= ((_ tuple.select 0) tuple_297) ((_ tuple.select 0) tuple_296)))))))
(assert (=> (set.exists ((tuple_300 (Tuple Int))) D true) (and (set.exists ((tuple_303 (Tuple Int))) D (set.forall ((tuple_304 (Tuple Int))) D (<= ((_ tuple.select 0) tuple_304) ((_ tuple.select 0) tuple_303)))) (set.exists ((tuple_301 (Tuple Int))) D (set.forall ((tuple_302 (Tuple Int))) D (>= ((_ tuple.select 0) tuple_302) ((_ tuple.select 0) tuple_301)))))))
(assert (=> (set.exists ((tuple_305 (Tuple Int))) E true) (and (set.exists ((tuple_308 (Tuple Int))) E (set.forall ((tuple_309 (Tuple Int))) E (<= ((_ tuple.select 0) tuple_309) ((_ tuple.select 0) tuple_308)))) (set.exists ((tuple_306 (Tuple Int))) E (set.forall ((tuple_307 (Tuple Int))) E (>= ((_ tuple.select 0) tuple_307) ((_ tuple.select 0) tuple_306)))))))
(assert (=> (set.exists ((tuple_310 (Tuple Int))) F true) (and (set.exists ((tuple_313 (Tuple Int))) F (set.forall ((tuple_314 (Tuple Int))) F (<= ((_ tuple.select 0) tuple_314) ((_ tuple.select 0) tuple_313)))) (set.exists ((tuple_311 (Tuple Int))) F (set.forall ((tuple_312 (Tuple Int))) F (>= ((_ tuple.select 0) tuple_312) ((_ tuple.select 0) tuple_311)))))))
(assert (=> (set.exists ((tuple_315 (Tuple Int))) G true) (and (set.exists ((tuple_318 (Tuple Int))) G (set.forall ((tuple_319 (Tuple Int))) G (<= ((_ tuple.select 0) tuple_319) ((_ tuple.select 0) tuple_318)))) (set.exists ((tuple_316 (Tuple Int))) G (set.forall ((tuple_317 (Tuple Int))) G (>= ((_ tuple.select 0) tuple_317) ((_ tuple.select 0) tuple_316)))))))
(assert (=> (set.exists ((tuple_320 (Tuple Int))) H true) (and (set.exists ((tuple_323 (Tuple Int))) H (set.forall ((tuple_324 (Tuple Int))) H (<= ((_ tuple.select 0) tuple_324) ((_ tuple.select 0) tuple_323)))) (set.exists ((tuple_321 (Tuple Int))) H (set.forall ((tuple_322 (Tuple Int))) H (>= ((_ tuple.select 0) tuple_322) ((_ tuple.select 0) tuple_321)))))))
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
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert (set.forall ((tuple_326 (Tuple Int Bool Int Bool))) Measure (set.exists ((tuple_327 (Tuple Int))) time (= ((_ tuple.select 0) tuple_327) ((_ tuple.select 0) tuple_326)))))
(check-sat)
(get-model)
