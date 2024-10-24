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
(assert (set.some (lambda ((tuple_38 (Tuple Int))) (set.some (lambda ((tuple_39 (Tuple Int Bool Int Bool))) (and (and (not (set.some (lambda ((tuple_40 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_40) (+ ((_ tuple.select 0) tuple_38) 0)) (<= ((_ tuple.select 0) tuple_40) (+ ((_ tuple.select 0) tuple_38) 0)))) C)) (> ((_ tuple.select 2) tuple_39) 50)) (= ((_ tuple.select 0) tuple_38) ((_ tuple.select 0) tuple_39)))) Measure)) B))
(assert (set.all (lambda ((tuple_2 (Tuple Int))) (set.some (lambda ((tuple_3 (Tuple Int Bool Int Bool))) (and (set.some (lambda ((tuple_4 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_4) (+ ((_ tuple.select 0) tuple_2) 0)) (<= ((_ tuple.select 0) tuple_4) (+ ((_ tuple.select 0) tuple_2) 0)))) B) (= ((_ tuple.select 0) tuple_2) ((_ tuple.select 0) tuple_3)))) Measure)) A))
(assert (set.all (lambda ((tuple_12 (Tuple Int))) (set.some (lambda ((tuple_13 (Tuple Int Bool Int Bool))) (and (or (set.some (lambda ((tuple_14 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_14) (+ ((_ tuple.select 0) tuple_12) 0)) (<= ((_ tuple.select 0) tuple_14) (+ ((_ tuple.select 0) tuple_12) 0)))) B) (not ((_ tuple.select 1) tuple_13))) (= ((_ tuple.select 0) tuple_12) ((_ tuple.select 0) tuple_13)))) Measure)) A))
(assert (set.all (lambda ((tuple_25 (Tuple Int))) (set.some (lambda ((tuple_26 (Tuple Int Bool Int Bool))) (and (and (=> (and true (and (not ((_ tuple.select 1) tuple_26)) true)) (set.some (lambda ((tuple_27 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_27) (+ ((_ tuple.select 0) tuple_25) 0)) (<= ((_ tuple.select 0) tuple_27) (+ ((_ tuple.select 0) tuple_25) 0)))) B)) (=> (and ((_ tuple.select 1) tuple_26) true) true)) (= ((_ tuple.select 0) tuple_25) ((_ tuple.select 0) tuple_26)))) Measure)) A))
(assert (set.all (lambda ((tuple_48 (Tuple Int))) (set.some (lambda ((tuple_49 (Tuple Int Bool Int Bool))) (and (or (set.some (lambda ((tuple_50 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_50) (+ ((_ tuple.select 0) tuple_48) 0)) (<= ((_ tuple.select 0) tuple_50) (+ ((_ tuple.select 0) tuple_48) 0)))) C) (not (> ((_ tuple.select 2) tuple_49) 100))) (= ((_ tuple.select 0) tuple_48) ((_ tuple.select 0) tuple_49)))) Measure)) B))
(assert (set.all (lambda ((tuple_61 (Tuple Int))) (set.some (lambda ((tuple_62 (Tuple Int Bool Int Bool))) (and (or (set.some (lambda ((tuple_63 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_63) (+ ((_ tuple.select 0) tuple_61) 0)) (<= ((_ tuple.select 0) tuple_63) (+ ((_ tuple.select 0) tuple_61) 0)))) C) (not (> ((_ tuple.select 2) tuple_62) 50))) (= ((_ tuple.select 0) tuple_61) ((_ tuple.select 0) tuple_62)))) Measure)) A))
(assert (set.all (lambda ((tuple_74 (Tuple Int))) (set.some (lambda ((tuple_75 (Tuple Int Bool Int Bool))) (and (set.some (lambda ((tuple_76 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_76) (+ ((_ tuple.select 0) tuple_74) 0)) (<= ((_ tuple.select 0) tuple_76) (+ ((_ tuple.select 0) tuple_74) 300)))) D) (= ((_ tuple.select 0) tuple_74) ((_ tuple.select 0) tuple_75)))) Measure)) C))
(assert (set.all (lambda ((tuple_84 (Tuple Int))) (set.some (lambda ((tuple_85 (Tuple Int Bool Int Bool))) (and (set.some (lambda ((tuple_86 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_86) (+ ((_ tuple.select 0) tuple_84) 0)) (<= ((_ tuple.select 0) tuple_86) (+ ((_ tuple.select 0) tuple_84) 301)))) D) (= ((_ tuple.select 0) tuple_84) ((_ tuple.select 0) tuple_85)))) Measure)) C))
(assert (set.all (lambda ((tuple_94 (Tuple Int))) (set.some (lambda ((tuple_95 (Tuple Int Bool Int Bool))) (and (=> true (or (set.some (lambda ((tuple_97 (Tuple Int Bool Int Bool))) (and (set.some (lambda ((tuple_98 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_98) (+ ((_ tuple.select 0) tuple_97) 0)) (<= ((_ tuple.select 0) tuple_98) (+ ((_ tuple.select 0) tuple_97) 51)))) D) (= (+ ((_ tuple.select 0) tuple_95) 250) ((_ tuple.select 0) tuple_97)))) Measure) (set.some (lambda ((tuple_96 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_96) (+ ((_ tuple.select 0) tuple_94) 0)) (<= ((_ tuple.select 0) tuple_96) (+ ((_ tuple.select 0) tuple_94) 250)))) D))) (= ((_ tuple.select 0) tuple_94) ((_ tuple.select 0) tuple_95)))) Measure)) C))
(assert (set.all (lambda ((tuple_108 (Tuple Int))) (set.some (lambda ((tuple_109 (Tuple Int Bool Int Bool))) (and (=> true (or (set.some (lambda ((tuple_111 (Tuple Int Bool Int Bool))) (and (=> true (or (set.some (lambda ((tuple_113 (Tuple Int Bool Int Bool))) (and (set.some (lambda ((tuple_114 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_114) (+ ((_ tuple.select 0) tuple_113) 0)) (<= ((_ tuple.select 0) tuple_114) (+ ((_ tuple.select 0) tuple_113) 10)))) D) (= (+ ((_ tuple.select 0) tuple_111) 40) ((_ tuple.select 0) tuple_113)))) Measure) (set.some (lambda ((tuple_112 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_112) (+ ((_ tuple.select 0) tuple_111) 0)) (<= ((_ tuple.select 0) tuple_112) (+ ((_ tuple.select 0) tuple_111) 40)))) D))) (= (+ ((_ tuple.select 0) tuple_109) 250) ((_ tuple.select 0) tuple_111)))) Measure) (set.some (lambda ((tuple_110 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_110) (+ ((_ tuple.select 0) tuple_108) 0)) (<= ((_ tuple.select 0) tuple_110) (+ ((_ tuple.select 0) tuple_108) 250)))) D))) (= ((_ tuple.select 0) tuple_108) ((_ tuple.select 0) tuple_109)))) Measure)) C))
(assert (set.all (lambda ((tuple_126 (Tuple Int))) (set.some (lambda ((tuple_127 (Tuple Int Bool Int Bool))) (and (=> true (or (set.some (lambda ((tuple_129 (Tuple Int Bool Int Bool))) (and (=> true (or (set.some (lambda ((tuple_131 (Tuple Int Bool Int Bool))) (and (and (=> (and true (and (not ((_ tuple.select 1) tuple_131)) true)) (set.some (lambda ((tuple_132 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_132) (+ ((_ tuple.select 0) tuple_131) 0)) (<= ((_ tuple.select 0) tuple_132) (+ ((_ tuple.select 0) tuple_131) 10)))) D)) (=> (and ((_ tuple.select 1) tuple_131) true) true)) (= (+ ((_ tuple.select 0) tuple_129) 40) ((_ tuple.select 0) tuple_131)))) Measure) (set.some (lambda ((tuple_130 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_130) (+ ((_ tuple.select 0) tuple_129) 0)) (<= ((_ tuple.select 0) tuple_130) (+ ((_ tuple.select 0) tuple_129) 40)))) D))) (= (+ ((_ tuple.select 0) tuple_127) 250) ((_ tuple.select 0) tuple_129)))) Measure) (set.some (lambda ((tuple_128 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_128) (+ ((_ tuple.select 0) tuple_126) 0)) (<= ((_ tuple.select 0) tuple_128) (+ ((_ tuple.select 0) tuple_126) 250)))) D))) (= ((_ tuple.select 0) tuple_126) ((_ tuple.select 0) tuple_127)))) Measure)) C))
(assert (set.all (lambda ((tuple_144 (Tuple Int))) (set.some (lambda ((tuple_145 (Tuple Int Bool Int Bool))) (and (set.some (lambda ((tuple_146 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_146) (+ ((_ tuple.select 0) tuple_144) 0)) (<= ((_ tuple.select 0) tuple_146) (+ ((_ tuple.select 0) tuple_144) 250)))) E) (= ((_ tuple.select 0) tuple_144) ((_ tuple.select 0) tuple_145)))) Measure)) C))
(assert (set.all (lambda ((tuple_154 (Tuple Int))) (set.some (lambda ((tuple_155 (Tuple Int Bool Int Bool))) (and (=> true (or (set.some (lambda ((tuple_157 (Tuple Int Bool Int Bool))) (and (=> true (or (set.some (lambda ((tuple_159 (Tuple Int Bool Int Bool))) (and (=> true (or (set.some (lambda ((tuple_161 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_161) (+ ((_ tuple.select 0) tuple_159) 0)) (<= ((_ tuple.select 0) tuple_161) (+ ((_ tuple.select 0) tuple_159) 10)))) D) (set.some (lambda ((tuple_160 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_160) (+ ((_ tuple.select 0) tuple_159) 0)) (<= ((_ tuple.select 0) tuple_160) (+ ((_ tuple.select 0) tuple_159) 0)))) E))) (= (+ ((_ tuple.select 0) tuple_157) 40) ((_ tuple.select 0) tuple_159)))) Measure) (set.some (lambda ((tuple_158 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_158) (+ ((_ tuple.select 0) tuple_157) 0)) (<= ((_ tuple.select 0) tuple_158) (+ ((_ tuple.select 0) tuple_157) 40)))) D))) (= (+ ((_ tuple.select 0) tuple_155) 250) ((_ tuple.select 0) tuple_157)))) Measure) (set.some (lambda ((tuple_156 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_156) (+ ((_ tuple.select 0) tuple_154) 0)) (<= ((_ tuple.select 0) tuple_156) (+ ((_ tuple.select 0) tuple_154) 250)))) D))) (= ((_ tuple.select 0) tuple_154) ((_ tuple.select 0) tuple_155)))) Measure)) C))
(assert (set.all (lambda ((tuple_174 (Tuple Int))) (set.some (lambda ((tuple_175 (Tuple Int Bool Int Bool))) (and (and (=> (and true (and (not ((_ tuple.select 1) tuple_175)) (and (not (> ((_ tuple.select 2) tuple_175) 2)) true))) (set.some (lambda ((tuple_176 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_176) (+ ((_ tuple.select 0) tuple_174) 0)) (<= ((_ tuple.select 0) tuple_176) (+ ((_ tuple.select 0) tuple_174) 5)))) F)) (and (=> (and ((_ tuple.select 1) tuple_175) (and (not (> ((_ tuple.select 2) tuple_175) 2)) true)) (set.some (lambda ((tuple_177 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_177) (+ ((_ tuple.select 0) tuple_174) 0)) (<= ((_ tuple.select 0) tuple_177) (+ ((_ tuple.select 0) tuple_174) 10)))) G)) (=> (and (> ((_ tuple.select 2) tuple_175) 2) true) (set.some (lambda ((tuple_179 (Tuple Int Int))) (and (= ((_ tuple.select 1) tuple_179) (+ ((_ tuple.select 0) tuple_174) 20)) (= ((_ tuple.select 0) tuple_179) (+ ((_ tuple.select 0) tuple_174) 0)))) not_G)))) (= ((_ tuple.select 0) tuple_174) ((_ tuple.select 0) tuple_175)))) Measure)) E))
(assert (set.all (lambda ((tuple_190 (Tuple Int))) (set.some (lambda ((tuple_191 (Tuple Int Bool Int Bool))) (and (or (and (=> (and true (and (not (> ((_ tuple.select 2) tuple_191) 2)) true)) (set.some (lambda ((tuple_192 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_192) (+ ((_ tuple.select 0) tuple_190) 0)) (<= ((_ tuple.select 0) tuple_192) (+ ((_ tuple.select 0) tuple_190) 10)))) G)) (=> (and (> ((_ tuple.select 2) tuple_191) 2) true) (set.some (lambda ((tuple_194 (Tuple Int Int))) (and (= ((_ tuple.select 1) tuple_194) (+ ((_ tuple.select 0) tuple_190) 10)) (= ((_ tuple.select 0) tuple_194) (+ ((_ tuple.select 0) tuple_190) 0)))) not_G))) (not ((_ tuple.select 1) tuple_191))) (= ((_ tuple.select 0) tuple_190) ((_ tuple.select 0) tuple_191)))) Measure)) E))
(assert (set.all (lambda ((tuple_207 (Tuple Int))) (set.some (lambda ((tuple_208 (Tuple Int Bool Int Bool))) (and (or (and (=> (and true (and (not (> ((_ tuple.select 2) tuple_208) 3)) true)) (set.some (lambda ((tuple_209 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_209) (+ ((_ tuple.select 0) tuple_207) 0)) (<= ((_ tuple.select 0) tuple_209) (+ ((_ tuple.select 0) tuple_207) 10)))) G)) (=> (and (> ((_ tuple.select 2) tuple_208) 3) true) (set.some (lambda ((tuple_211 (Tuple Int Int))) (and (= ((_ tuple.select 1) tuple_211) (+ ((_ tuple.select 0) tuple_207) 10)) (= ((_ tuple.select 0) tuple_211) (+ ((_ tuple.select 0) tuple_207) 0)))) not_G))) (not ((_ tuple.select 1) tuple_208))) (= ((_ tuple.select 0) tuple_207) ((_ tuple.select 0) tuple_208)))) Measure)) E))
(assert (set.all (lambda ((tuple_224 (Tuple Int))) (set.some (lambda ((tuple_225 (Tuple Int Bool Int Bool))) (and (or (and (=> (and true (and (not (> ((_ tuple.select 2) tuple_225) 1)) true)) (set.some (lambda ((tuple_226 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_226) (+ ((_ tuple.select 0) tuple_224) 0)) (<= ((_ tuple.select 0) tuple_226) (+ ((_ tuple.select 0) tuple_224) 10)))) G)) (=> (and (> ((_ tuple.select 2) tuple_225) 1) true) (set.some (lambda ((tuple_228 (Tuple Int Int))) (and (= ((_ tuple.select 1) tuple_228) (+ ((_ tuple.select 0) tuple_224) 10)) (= ((_ tuple.select 0) tuple_228) (+ ((_ tuple.select 0) tuple_224) 0)))) not_G))) (not ((_ tuple.select 1) tuple_225))) (= ((_ tuple.select 0) tuple_224) ((_ tuple.select 0) tuple_225)))) Measure)) E))
(assert (set.all (lambda ((tuple_241 (Tuple Int))) (set.some (lambda ((tuple_242 (Tuple Int Bool Int Bool))) (and (and (=> (and true (and (not ((_ tuple.select 3) tuple_242)) true)) (set.some (lambda ((tuple_243 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_243) (+ ((_ tuple.select 0) tuple_241) 0)) (<= ((_ tuple.select 0) tuple_243) (+ ((_ tuple.select 0) tuple_241) 5)))) G)) (=> (and ((_ tuple.select 3) tuple_242) true) (set.some (lambda ((tuple_244 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_244) (+ ((_ tuple.select 0) tuple_241) 0)) (<= ((_ tuple.select 0) tuple_244) (+ ((_ tuple.select 0) tuple_241) 10)))) H))) (= ((_ tuple.select 0) tuple_241) ((_ tuple.select 0) tuple_242)))) Measure)) F))
(assert (set.all (lambda ((tuple_253 (Tuple Int))) (set.some (lambda ((tuple_254 (Tuple Int Bool Int Bool))) (and (set.some (lambda ((tuple_255 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_255) (+ ((_ tuple.select 0) tuple_253) 0)) (<= ((_ tuple.select 0) tuple_255) (+ ((_ tuple.select 0) tuple_253) 10)))) F) (= ((_ tuple.select 0) tuple_253) ((_ tuple.select 0) tuple_254)))) Measure)) H))
(assert (set.all (lambda ((tuple_263 (Tuple Int))) (set.some (lambda ((tuple_264 (Tuple Int Bool Int Bool))) (and (set.some (lambda ((tuple_266 (Tuple Int Int))) (and (= ((_ tuple.select 1) tuple_266) (+ ((_ tuple.select 0) tuple_263) 0)) (= ((_ tuple.select 0) tuple_266) (+ ((_ tuple.select 0) tuple_263) 0)))) not_F) (= ((_ tuple.select 0) tuple_263) ((_ tuple.select 0) tuple_264)))) Measure)) H))
(assert (set.all (lambda ((tuple_275 (Tuple Int))) (set.some (lambda ((tuple_276 (Tuple Int Bool Int Bool))) (and (set.some (lambda ((tuple_277 (Tuple Int))) (>= ((_ tuple.select 0) tuple_277) ((_ tuple.select 0) tuple_275))) G) (= ((_ tuple.select 0) tuple_275) ((_ tuple.select 0) tuple_276)))) Measure)) F))
(assert (and (and (forall ((H_time_Int_21 Int) (not_H_start_time_Int_22 Int) (not_H_end_time_Int_23 Int)) (=> (and (set.member (tuple not_H_start_time_Int_22 not_H_end_time_Int_23) not_H) (set.member (tuple H_time_Int_21) H)) (not (and (<= H_time_Int_21 not_H_end_time_Int_23) (<= not_H_start_time_Int_22 H_time_Int_21))))) (and (forall ((G_time_Int_18 Int) (not_G_start_time_Int_19 Int) (not_G_end_time_Int_20 Int)) (=> (and (set.member (tuple not_G_start_time_Int_19 not_G_end_time_Int_20) not_G) (set.member (tuple G_time_Int_18) G)) (not (and (<= G_time_Int_18 not_G_end_time_Int_20) (<= not_G_start_time_Int_19 G_time_Int_18))))) (and (forall ((F_time_Int_15 Int) (not_F_start_time_Int_16 Int) (not_F_end_time_Int_17 Int)) (=> (and (set.member (tuple not_F_start_time_Int_16 not_F_end_time_Int_17) not_F) (set.member (tuple F_time_Int_15) F)) (not (and (<= F_time_Int_15 not_F_end_time_Int_17) (<= not_F_start_time_Int_16 F_time_Int_15))))) (and (forall ((E_time_Int_12 Int) (not_E_start_time_Int_13 Int) (not_E_end_time_Int_14 Int)) (=> (and (set.member (tuple not_E_start_time_Int_13 not_E_end_time_Int_14) not_E) (set.member (tuple E_time_Int_12) E)) (not (and (<= E_time_Int_12 not_E_end_time_Int_14) (<= not_E_start_time_Int_13 E_time_Int_12))))) (and (forall ((D_time_Int_9 Int) (not_D_start_time_Int_10 Int) (not_D_end_time_Int_11 Int)) (=> (and (set.member (tuple not_D_start_time_Int_10 not_D_end_time_Int_11) not_D) (set.member (tuple D_time_Int_9) D)) (not (and (<= D_time_Int_9 not_D_end_time_Int_11) (<= not_D_start_time_Int_10 D_time_Int_9))))) (and (forall ((C_time_Int_6 Int) (not_C_start_time_Int_7 Int) (not_C_end_time_Int_8 Int)) (=> (and (set.member (tuple not_C_start_time_Int_7 not_C_end_time_Int_8) not_C) (set.member (tuple C_time_Int_6) C)) (not (and (<= C_time_Int_6 not_C_end_time_Int_8) (<= not_C_start_time_Int_7 C_time_Int_6))))) (and (forall ((B_time_Int_3 Int) (not_B_start_time_Int_4 Int) (not_B_end_time_Int_5 Int)) (=> (and (set.member (tuple not_B_start_time_Int_4 not_B_end_time_Int_5) not_B) (set.member (tuple B_time_Int_3) B)) (not (and (<= B_time_Int_3 not_B_end_time_Int_5) (<= not_B_start_time_Int_4 B_time_Int_3))))) (forall ((A_time_Int_0 Int) (not_A_start_time_Int_1 Int) (not_A_end_time_Int_2 Int)) (=> (and (set.member (tuple not_A_start_time_Int_1 not_A_end_time_Int_2) not_A) (set.member (tuple A_time_Int_0) A)) (not (and (<= A_time_Int_0 not_A_end_time_Int_2) (<= not_A_start_time_Int_1 A_time_Int_0)))))))))))) (set.all (lambda ((tuple_285 (Tuple Int Bool Int Bool Int Bool Int Bool))) (=> (= ((_ tuple.select 0) tuple_285) ((_ tuple.select 4) tuple_285)) (and (= ((_ tuple.select 3) tuple_285) ((_ tuple.select 7) tuple_285)) (and (= ((_ tuple.select 2) tuple_285) ((_ tuple.select 6) tuple_285)) (and (= ((_ tuple.select 1) tuple_285) ((_ tuple.select 5) tuple_285)) (= ((_ tuple.select 0) tuple_285) ((_ tuple.select 4) tuple_285))))))) (rel.product Measure Measure))))
(assert (=> (set.some (lambda ((tuple_286 (Tuple Int))) true) A) (and (set.some (lambda ((tuple_289 (Tuple Int))) (set.all (lambda ((tuple_290 (Tuple Int))) (<= ((_ tuple.select 0) tuple_290) ((_ tuple.select 0) tuple_289))) A)) A) (set.some (lambda ((tuple_287 (Tuple Int))) (set.all (lambda ((tuple_288 (Tuple Int))) (>= ((_ tuple.select 0) tuple_288) ((_ tuple.select 0) tuple_287))) A)) A))))
(assert (=> (set.some (lambda ((tuple_291 (Tuple Int))) true) B) (and (set.some (lambda ((tuple_294 (Tuple Int))) (set.all (lambda ((tuple_295 (Tuple Int))) (<= ((_ tuple.select 0) tuple_295) ((_ tuple.select 0) tuple_294))) B)) B) (set.some (lambda ((tuple_292 (Tuple Int))) (set.all (lambda ((tuple_293 (Tuple Int))) (>= ((_ tuple.select 0) tuple_293) ((_ tuple.select 0) tuple_292))) B)) B))))
(assert (=> (set.some (lambda ((tuple_296 (Tuple Int))) true) C) (and (set.some (lambda ((tuple_299 (Tuple Int))) (set.all (lambda ((tuple_300 (Tuple Int))) (<= ((_ tuple.select 0) tuple_300) ((_ tuple.select 0) tuple_299))) C)) C) (set.some (lambda ((tuple_297 (Tuple Int))) (set.all (lambda ((tuple_298 (Tuple Int))) (>= ((_ tuple.select 0) tuple_298) ((_ tuple.select 0) tuple_297))) C)) C))))
(assert (=> (set.some (lambda ((tuple_301 (Tuple Int))) true) D) (and (set.some (lambda ((tuple_304 (Tuple Int))) (set.all (lambda ((tuple_305 (Tuple Int))) (<= ((_ tuple.select 0) tuple_305) ((_ tuple.select 0) tuple_304))) D)) D) (set.some (lambda ((tuple_302 (Tuple Int))) (set.all (lambda ((tuple_303 (Tuple Int))) (>= ((_ tuple.select 0) tuple_303) ((_ tuple.select 0) tuple_302))) D)) D))))
(assert (=> (set.some (lambda ((tuple_306 (Tuple Int))) true) E) (and (set.some (lambda ((tuple_309 (Tuple Int))) (set.all (lambda ((tuple_310 (Tuple Int))) (<= ((_ tuple.select 0) tuple_310) ((_ tuple.select 0) tuple_309))) E)) E) (set.some (lambda ((tuple_307 (Tuple Int))) (set.all (lambda ((tuple_308 (Tuple Int))) (>= ((_ tuple.select 0) tuple_308) ((_ tuple.select 0) tuple_307))) E)) E))))
(assert (=> (set.some (lambda ((tuple_311 (Tuple Int))) true) F) (and (set.some (lambda ((tuple_314 (Tuple Int))) (set.all (lambda ((tuple_315 (Tuple Int))) (<= ((_ tuple.select 0) tuple_315) ((_ tuple.select 0) tuple_314))) F)) F) (set.some (lambda ((tuple_312 (Tuple Int))) (set.all (lambda ((tuple_313 (Tuple Int))) (>= ((_ tuple.select 0) tuple_313) ((_ tuple.select 0) tuple_312))) F)) F))))
(assert (=> (set.some (lambda ((tuple_316 (Tuple Int))) true) G) (and (set.some (lambda ((tuple_319 (Tuple Int))) (set.all (lambda ((tuple_320 (Tuple Int))) (<= ((_ tuple.select 0) tuple_320) ((_ tuple.select 0) tuple_319))) G)) G) (set.some (lambda ((tuple_317 (Tuple Int))) (set.all (lambda ((tuple_318 (Tuple Int))) (>= ((_ tuple.select 0) tuple_318) ((_ tuple.select 0) tuple_317))) G)) G))))
(assert (=> (set.some (lambda ((tuple_321 (Tuple Int))) true) H) (and (set.some (lambda ((tuple_324 (Tuple Int))) (set.all (lambda ((tuple_325 (Tuple Int))) (<= ((_ tuple.select 0) tuple_325) ((_ tuple.select 0) tuple_324))) H)) H) (set.some (lambda ((tuple_322 (Tuple Int))) (set.all (lambda ((tuple_323 (Tuple Int))) (>= ((_ tuple.select 0) tuple_323) ((_ tuple.select 0) tuple_322))) H)) H))))
(assert (set.all (lambda ((tuple_1 (Tuple Int))) (>= ((_ tuple.select 0) tuple_1) 0)) time))
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
(assert (set.all (lambda ((tuple_326 (Tuple Int Bool Int Bool))) (set.some (lambda ((tuple_327 (Tuple Int))) (= ((_ tuple.select 0) tuple_327) ((_ tuple.select 0) tuple_326))) time)) Measure))
(check-sat)
