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
(assert (exists ((B_time_Int_73 Int)) (and (exists ((Measure_time_Int_74 Int) (Measure_ba_Bool_38 Bool) (Measure_na_Int_75 Int) (Measure_bb_Bool_39 Bool)) (and (and (and (not (exists ((C_time_Int_76 Int)) (and (and (>= C_time_Int_76 (+ B_time_Int_73 0)) (<= C_time_Int_76 (+ B_time_Int_73 0))) (set.member (tuple C_time_Int_76) C)))) (> Measure_na_Int_75 100)) (= B_time_Int_73 Measure_time_Int_74)) (set.member (tuple Measure_time_Int_74 Measure_ba_Bool_38 Measure_na_Int_75 Measure_bb_Bool_39) Measure))) (set.member (tuple B_time_Int_73) B))))
(assert (forall ((A_time_Int_1 Int)) (=> (set.member (tuple A_time_Int_1) A) (exists ((Measure_time_Int_2 Int) (Measure_ba_Bool_0 Bool) (Measure_na_Int_3 Int) (Measure_bb_Bool_1 Bool)) (and (and (exists ((B_time_Int_4 Int)) (and (and (>= B_time_Int_4 (+ A_time_Int_1 0)) (<= B_time_Int_4 (+ A_time_Int_1 0))) (set.member (tuple B_time_Int_4) B))) (= A_time_Int_1 Measure_time_Int_2)) (set.member (tuple Measure_time_Int_2 Measure_ba_Bool_0 Measure_na_Int_3 Measure_bb_Bool_1) Measure))))))
(assert (forall ((A_time_Int_15 Int)) (=> (set.member (tuple A_time_Int_15) A) (exists ((Measure_time_Int_16 Int) (Measure_ba_Bool_6 Bool) (Measure_na_Int_17 Int) (Measure_bb_Bool_7 Bool)) (and (and (or (exists ((B_time_Int_18 Int)) (and (and (>= B_time_Int_18 (+ A_time_Int_15 0)) (<= B_time_Int_18 (+ A_time_Int_15 0))) (set.member (tuple B_time_Int_18) B))) (not Measure_ba_Bool_6)) (= A_time_Int_15 Measure_time_Int_16)) (set.member (tuple Measure_time_Int_16 Measure_ba_Bool_6 Measure_na_Int_17 Measure_bb_Bool_7) Measure))))))
(assert (forall ((A_time_Int_35 Int)) (=> (set.member (tuple A_time_Int_35) A) (exists ((Measure_time_Int_36 Int) (Measure_ba_Bool_18 Bool) (Measure_na_Int_37 Int) (Measure_bb_Bool_19 Bool)) (and (and (and (=> (and true (and (not Measure_ba_Bool_18) true)) (exists ((B_time_Int_38 Int)) (and (and (>= B_time_Int_38 (+ A_time_Int_35 0)) (<= B_time_Int_38 (+ A_time_Int_35 0))) (set.member (tuple B_time_Int_38) B)))) (=> (and Measure_ba_Bool_18 true) true)) (= A_time_Int_35 Measure_time_Int_36)) (set.member (tuple Measure_time_Int_36 Measure_ba_Bool_18 Measure_na_Int_37 Measure_bb_Bool_19) Measure))))))
(assert (forall ((B_time_Int_49 Int)) (=> (set.member (tuple B_time_Int_49) B) (exists ((Measure_time_Int_50 Int) (Measure_ba_Bool_24 Bool) (Measure_na_Int_51 Int) (Measure_bb_Bool_25 Bool)) (and (and (or (exists ((C_time_Int_52 Int)) (and (and (>= C_time_Int_52 (+ B_time_Int_49 0)) (<= C_time_Int_52 (+ B_time_Int_49 0))) (set.member (tuple C_time_Int_52) C))) (not (> Measure_na_Int_51 50))) (= B_time_Int_49 Measure_time_Int_50)) (set.member (tuple Measure_time_Int_50 Measure_ba_Bool_24 Measure_na_Int_51 Measure_bb_Bool_25) Measure))))))
(assert (forall ((A_time_Int_89 Int)) (=> (set.member (tuple A_time_Int_89) A) (exists ((Measure_time_Int_90 Int) (Measure_ba_Bool_48 Bool) (Measure_na_Int_91 Int) (Measure_bb_Bool_49 Bool)) (and (and (or (exists ((C_time_Int_92 Int)) (and (and (>= C_time_Int_92 (+ A_time_Int_89 0)) (<= C_time_Int_92 (+ A_time_Int_89 0))) (set.member (tuple C_time_Int_92) C))) (not (> Measure_na_Int_91 50))) (= A_time_Int_89 Measure_time_Int_90)) (set.member (tuple Measure_time_Int_90 Measure_ba_Bool_48 Measure_na_Int_91 Measure_bb_Bool_49) Measure))))))
(assert (forall ((C_time_Int_109 Int)) (=> (set.member (tuple C_time_Int_109) C) (exists ((Measure_time_Int_110 Int) (Measure_ba_Bool_60 Bool) (Measure_na_Int_111 Int) (Measure_bb_Bool_61 Bool)) (and (and (exists ((D_time_Int_112 Int)) (and (and (>= D_time_Int_112 (+ C_time_Int_109 0)) (<= D_time_Int_112 (+ C_time_Int_109 300))) (set.member (tuple D_time_Int_112) D))) (= C_time_Int_109 Measure_time_Int_110)) (set.member (tuple Measure_time_Int_110 Measure_ba_Bool_60 Measure_na_Int_111 Measure_bb_Bool_61) Measure))))))
(assert (forall ((C_time_Int_123 Int)) (=> (set.member (tuple C_time_Int_123) C) (exists ((Measure_time_Int_124 Int) (Measure_ba_Bool_66 Bool) (Measure_na_Int_125 Int) (Measure_bb_Bool_67 Bool)) (and (and (exists ((D_time_Int_126 Int)) (and (and (>= D_time_Int_126 (+ C_time_Int_123 0)) (<= D_time_Int_126 (+ C_time_Int_123 301))) (set.member (tuple D_time_Int_126) D))) (= C_time_Int_123 Measure_time_Int_124)) (set.member (tuple Measure_time_Int_124 Measure_ba_Bool_66 Measure_na_Int_125 Measure_bb_Bool_67) Measure))))))
(assert (forall ((C_time_Int_137 Int)) (=> (set.member (tuple C_time_Int_137) C) (exists ((Measure_time_Int_138 Int) (Measure_ba_Bool_72 Bool) (Measure_na_Int_139 Int) (Measure_bb_Bool_73 Bool)) (and (and (=> true (or (exists ((Measure_time_Int_141 Int) (Measure_ba_Bool_74 Bool) (Measure_na_Int_142 Int) (Measure_bb_Bool_75 Bool)) (and (and (exists ((D_time_Int_143 Int)) (and (and (>= D_time_Int_143 (+ Measure_time_Int_141 0)) (<= D_time_Int_143 (+ Measure_time_Int_141 51))) (set.member (tuple D_time_Int_143) D))) (= (+ Measure_time_Int_138 250) Measure_time_Int_141)) (set.member (tuple Measure_time_Int_141 Measure_ba_Bool_74 Measure_na_Int_142 Measure_bb_Bool_75) Measure))) (exists ((D_time_Int_140 Int)) (and (and (>= D_time_Int_140 (+ C_time_Int_137 0)) (<= D_time_Int_140 (+ C_time_Int_137 250))) (set.member (tuple D_time_Int_140) D))))) (= C_time_Int_137 Measure_time_Int_138)) (set.member (tuple Measure_time_Int_138 Measure_ba_Bool_72 Measure_na_Int_139 Measure_bb_Bool_73) Measure))))))
(assert (forall ((C_time_Int_157 Int)) (=> (set.member (tuple C_time_Int_157) C) (exists ((Measure_time_Int_158 Int) (Measure_ba_Bool_82 Bool) (Measure_na_Int_159 Int) (Measure_bb_Bool_83 Bool)) (and (and (=> true (or (exists ((Measure_time_Int_161 Int) (Measure_ba_Bool_84 Bool) (Measure_na_Int_162 Int) (Measure_bb_Bool_85 Bool)) (and (and (=> true (or (exists ((Measure_time_Int_164 Int) (Measure_ba_Bool_86 Bool) (Measure_na_Int_165 Int) (Measure_bb_Bool_87 Bool)) (and (and (exists ((D_time_Int_166 Int)) (and (and (>= D_time_Int_166 (+ Measure_time_Int_164 0)) (<= D_time_Int_166 (+ Measure_time_Int_164 10))) (set.member (tuple D_time_Int_166) D))) (= (+ Measure_time_Int_161 40) Measure_time_Int_164)) (set.member (tuple Measure_time_Int_164 Measure_ba_Bool_86 Measure_na_Int_165 Measure_bb_Bool_87) Measure))) (exists ((D_time_Int_163 Int)) (and (and (>= D_time_Int_163 (+ Measure_time_Int_161 0)) (<= D_time_Int_163 (+ Measure_time_Int_161 40))) (set.member (tuple D_time_Int_163) D))))) (= (+ Measure_time_Int_158 250) Measure_time_Int_161)) (set.member (tuple Measure_time_Int_161 Measure_ba_Bool_84 Measure_na_Int_162 Measure_bb_Bool_85) Measure))) (exists ((D_time_Int_160 Int)) (and (and (>= D_time_Int_160 (+ C_time_Int_157 0)) (<= D_time_Int_160 (+ C_time_Int_157 250))) (set.member (tuple D_time_Int_160) D))))) (= C_time_Int_157 Measure_time_Int_158)) (set.member (tuple Measure_time_Int_158 Measure_ba_Bool_82 Measure_na_Int_159 Measure_bb_Bool_83) Measure))))))
(assert (forall ((C_time_Int_183 Int)) (=> (set.member (tuple C_time_Int_183) C) (exists ((Measure_time_Int_184 Int) (Measure_ba_Bool_96 Bool) (Measure_na_Int_185 Int) (Measure_bb_Bool_97 Bool)) (and (and (=> true (or (exists ((Measure_time_Int_187 Int) (Measure_ba_Bool_98 Bool) (Measure_na_Int_188 Int) (Measure_bb_Bool_99 Bool)) (and (and (=> true (or (exists ((Measure_time_Int_190 Int) (Measure_ba_Bool_100 Bool) (Measure_na_Int_191 Int) (Measure_bb_Bool_101 Bool)) (and (and (and (=> (and true (and (not Measure_ba_Bool_100) true)) (exists ((D_time_Int_192 Int)) (and (and (>= D_time_Int_192 (+ Measure_time_Int_190 0)) (<= D_time_Int_192 (+ Measure_time_Int_190 10))) (set.member (tuple D_time_Int_192) D)))) (=> (and Measure_ba_Bool_100 true) true)) (= (+ Measure_time_Int_187 40) Measure_time_Int_190)) (set.member (tuple Measure_time_Int_190 Measure_ba_Bool_100 Measure_na_Int_191 Measure_bb_Bool_101) Measure))) (exists ((D_time_Int_189 Int)) (and (and (>= D_time_Int_189 (+ Measure_time_Int_187 0)) (<= D_time_Int_189 (+ Measure_time_Int_187 40))) (set.member (tuple D_time_Int_189) D))))) (= (+ Measure_time_Int_184 250) Measure_time_Int_187)) (set.member (tuple Measure_time_Int_187 Measure_ba_Bool_98 Measure_na_Int_188 Measure_bb_Bool_99) Measure))) (exists ((D_time_Int_186 Int)) (and (and (>= D_time_Int_186 (+ C_time_Int_183 0)) (<= D_time_Int_186 (+ C_time_Int_183 250))) (set.member (tuple D_time_Int_186) D))))) (= C_time_Int_183 Measure_time_Int_184)) (set.member (tuple Measure_time_Int_184 Measure_ba_Bool_96 Measure_na_Int_185 Measure_bb_Bool_97) Measure))))))
(assert (forall ((C_time_Int_209 Int)) (=> (set.member (tuple C_time_Int_209) C) (exists ((Measure_time_Int_210 Int) (Measure_ba_Bool_110 Bool) (Measure_na_Int_211 Int) (Measure_bb_Bool_111 Bool)) (and (and (exists ((E_time_Int_212 Int)) (and (and (>= E_time_Int_212 (+ C_time_Int_209 0)) (<= E_time_Int_212 (+ C_time_Int_209 250))) (set.member (tuple E_time_Int_212) E))) (= C_time_Int_209 Measure_time_Int_210)) (set.member (tuple Measure_time_Int_210 Measure_ba_Bool_110 Measure_na_Int_211 Measure_bb_Bool_111) Measure))))))
(assert (forall ((C_time_Int_223 Int)) (=> (set.member (tuple C_time_Int_223) C) (exists ((Measure_time_Int_224 Int) (Measure_ba_Bool_116 Bool) (Measure_na_Int_225 Int) (Measure_bb_Bool_117 Bool)) (and (and (=> true (or (exists ((Measure_time_Int_227 Int) (Measure_ba_Bool_118 Bool) (Measure_na_Int_228 Int) (Measure_bb_Bool_119 Bool)) (and (and (=> true (or (exists ((Measure_time_Int_230 Int) (Measure_ba_Bool_120 Bool) (Measure_na_Int_231 Int) (Measure_bb_Bool_121 Bool)) (and (and (=> true (or (exists ((D_time_Int_233 Int)) (and (and (>= D_time_Int_233 (+ Measure_time_Int_230 0)) (<= D_time_Int_233 (+ Measure_time_Int_230 10))) (set.member (tuple D_time_Int_233) D))) (exists ((E_time_Int_232 Int)) (and (and (>= E_time_Int_232 (+ Measure_time_Int_230 0)) (<= E_time_Int_232 (+ Measure_time_Int_230 0))) (set.member (tuple E_time_Int_232) E))))) (= (+ Measure_time_Int_227 40) Measure_time_Int_230)) (set.member (tuple Measure_time_Int_230 Measure_ba_Bool_120 Measure_na_Int_231 Measure_bb_Bool_121) Measure))) (exists ((D_time_Int_229 Int)) (and (and (>= D_time_Int_229 (+ Measure_time_Int_227 0)) (<= D_time_Int_229 (+ Measure_time_Int_227 40))) (set.member (tuple D_time_Int_229) D))))) (= (+ Measure_time_Int_224 250) Measure_time_Int_227)) (set.member (tuple Measure_time_Int_227 Measure_ba_Bool_118 Measure_na_Int_228 Measure_bb_Bool_119) Measure))) (exists ((D_time_Int_226 Int)) (and (and (>= D_time_Int_226 (+ C_time_Int_223 0)) (<= D_time_Int_226 (+ C_time_Int_223 250))) (set.member (tuple D_time_Int_226) D))))) (= C_time_Int_223 Measure_time_Int_224)) (set.member (tuple Measure_time_Int_224 Measure_ba_Bool_116 Measure_na_Int_225 Measure_bb_Bool_117) Measure))))))
(assert (forall ((E_time_Int_251 Int)) (=> (set.member (tuple E_time_Int_251) E) (exists ((Measure_time_Int_252 Int) (Measure_ba_Bool_130 Bool) (Measure_na_Int_253 Int) (Measure_bb_Bool_131 Bool)) (and (and (and (=> (and true (and (not Measure_ba_Bool_130) (and (not (> Measure_na_Int_253 2)) true))) (exists ((F_time_Int_254 Int)) (and (and (>= F_time_Int_254 (+ E_time_Int_251 0)) (<= F_time_Int_254 (+ E_time_Int_251 5))) (set.member (tuple F_time_Int_254) F)))) (and (=> (and Measure_ba_Bool_130 (and (not (> Measure_na_Int_253 2)) true)) (exists ((G_time_Int_255 Int)) (and (and (>= G_time_Int_255 (+ E_time_Int_251 0)) (<= G_time_Int_255 (+ E_time_Int_251 10))) (set.member (tuple G_time_Int_255) G)))) (=> (and (> Measure_na_Int_253 2) true) (exists ((not_G_start_time_Int_257 Int) (not_G_end_time_Int_258 Int)) (and (and (= not_G_end_time_Int_258 (+ E_time_Int_251 20)) (= not_G_start_time_Int_257 (+ E_time_Int_251 0))) (set.member (tuple not_G_start_time_Int_257 not_G_end_time_Int_258) not_G)))))) (= E_time_Int_251 Measure_time_Int_252)) (set.member (tuple Measure_time_Int_252 Measure_ba_Bool_130 Measure_na_Int_253 Measure_bb_Bool_131) Measure))))))
(assert (forall ((E_time_Int_273 Int)) (=> (set.member (tuple E_time_Int_273) E) (exists ((Measure_time_Int_274 Int) (Measure_ba_Bool_136 Bool) (Measure_na_Int_275 Int) (Measure_bb_Bool_137 Bool)) (and (and (or (and (=> (and true (and (not (> Measure_na_Int_275 2)) true)) (exists ((G_time_Int_276 Int)) (and (and (>= G_time_Int_276 (+ E_time_Int_273 0)) (<= G_time_Int_276 (+ E_time_Int_273 10))) (set.member (tuple G_time_Int_276) G)))) (=> (and (> Measure_na_Int_275 2) true) (exists ((not_G_start_time_Int_278 Int) (not_G_end_time_Int_279 Int)) (and (and (= not_G_end_time_Int_279 (+ E_time_Int_273 10)) (= not_G_start_time_Int_278 (+ E_time_Int_273 0))) (set.member (tuple not_G_start_time_Int_278 not_G_end_time_Int_279) not_G))))) (not Measure_ba_Bool_136)) (= E_time_Int_273 Measure_time_Int_274)) (set.member (tuple Measure_time_Int_274 Measure_ba_Bool_136 Measure_na_Int_275 Measure_bb_Bool_137) Measure))))))
(assert (forall ((E_time_Int_299 Int)) (=> (set.member (tuple E_time_Int_299) E) (exists ((Measure_time_Int_300 Int) (Measure_ba_Bool_148 Bool) (Measure_na_Int_301 Int) (Measure_bb_Bool_149 Bool)) (and (and (or (and (=> (and true (and (not (> Measure_na_Int_301 3)) true)) (exists ((G_time_Int_302 Int)) (and (and (>= G_time_Int_302 (+ E_time_Int_299 0)) (<= G_time_Int_302 (+ E_time_Int_299 10))) (set.member (tuple G_time_Int_302) G)))) (=> (and (> Measure_na_Int_301 3) true) (exists ((not_G_start_time_Int_304 Int) (not_G_end_time_Int_305 Int)) (and (and (= not_G_end_time_Int_305 (+ E_time_Int_299 10)) (= not_G_start_time_Int_304 (+ E_time_Int_299 0))) (set.member (tuple not_G_start_time_Int_304 not_G_end_time_Int_305) not_G))))) (not Measure_ba_Bool_148)) (= E_time_Int_299 Measure_time_Int_300)) (set.member (tuple Measure_time_Int_300 Measure_ba_Bool_148 Measure_na_Int_301 Measure_bb_Bool_149) Measure))))))
(assert (forall ((E_time_Int_325 Int)) (=> (set.member (tuple E_time_Int_325) E) (exists ((Measure_time_Int_326 Int) (Measure_ba_Bool_160 Bool) (Measure_na_Int_327 Int) (Measure_bb_Bool_161 Bool)) (and (and (or (and (=> (and true (and (not (> Measure_na_Int_327 1)) true)) (exists ((G_time_Int_328 Int)) (and (and (>= G_time_Int_328 (+ E_time_Int_325 0)) (<= G_time_Int_328 (+ E_time_Int_325 10))) (set.member (tuple G_time_Int_328) G)))) (=> (and (> Measure_na_Int_327 1) true) (exists ((not_G_start_time_Int_330 Int) (not_G_end_time_Int_331 Int)) (and (and (= not_G_end_time_Int_331 (+ E_time_Int_325 10)) (= not_G_start_time_Int_330 (+ E_time_Int_325 0))) (set.member (tuple not_G_start_time_Int_330 not_G_end_time_Int_331) not_G))))) (not Measure_ba_Bool_160)) (= E_time_Int_325 Measure_time_Int_326)) (set.member (tuple Measure_time_Int_326 Measure_ba_Bool_160 Measure_na_Int_327 Measure_bb_Bool_161) Measure))))))
(assert (forall ((F_time_Int_351 Int)) (=> (set.member (tuple F_time_Int_351) F) (exists ((Measure_time_Int_352 Int) (Measure_ba_Bool_172 Bool) (Measure_na_Int_353 Int) (Measure_bb_Bool_173 Bool)) (and (and (and (=> (and true (and (not Measure_bb_Bool_173) true)) (exists ((G_time_Int_354 Int)) (and (and (>= G_time_Int_354 (+ F_time_Int_351 0)) (<= G_time_Int_354 (+ F_time_Int_351 5))) (set.member (tuple G_time_Int_354) G)))) (=> (and Measure_bb_Bool_173 true) (exists ((H_time_Int_355 Int)) (and (and (>= H_time_Int_355 (+ F_time_Int_351 0)) (<= H_time_Int_355 (+ F_time_Int_351 10))) (set.member (tuple H_time_Int_355) H))))) (= F_time_Int_351 Measure_time_Int_352)) (set.member (tuple Measure_time_Int_352 Measure_ba_Bool_172 Measure_na_Int_353 Measure_bb_Bool_173) Measure))))))
(assert (forall ((H_time_Int_367 Int)) (=> (set.member (tuple H_time_Int_367) H) (exists ((Measure_time_Int_368 Int) (Measure_ba_Bool_178 Bool) (Measure_na_Int_369 Int) (Measure_bb_Bool_179 Bool)) (and (and (exists ((F_time_Int_370 Int)) (and (and (>= F_time_Int_370 (+ H_time_Int_367 0)) (<= F_time_Int_370 (+ H_time_Int_367 10))) (set.member (tuple F_time_Int_370) F))) (= H_time_Int_367 Measure_time_Int_368)) (set.member (tuple Measure_time_Int_368 Measure_ba_Bool_178 Measure_na_Int_369 Measure_bb_Bool_179) Measure))))))
(assert (forall ((H_time_Int_381 Int)) (=> (set.member (tuple H_time_Int_381) H) (exists ((Measure_time_Int_382 Int) (Measure_ba_Bool_184 Bool) (Measure_na_Int_383 Int) (Measure_bb_Bool_185 Bool)) (and (and (exists ((not_F_start_time_Int_385 Int) (not_F_end_time_Int_386 Int)) (and (and (= not_F_end_time_Int_386 (+ H_time_Int_381 0)) (= not_F_start_time_Int_385 (+ H_time_Int_381 0))) (set.member (tuple not_F_start_time_Int_385 not_F_end_time_Int_386) not_F))) (= H_time_Int_381 Measure_time_Int_382)) (set.member (tuple Measure_time_Int_382 Measure_ba_Bool_184 Measure_na_Int_383 Measure_bb_Bool_185) Measure))))))
(assert (forall ((F_time_Int_399 Int)) (=> (set.member (tuple F_time_Int_399) F) (exists ((Measure_time_Int_400 Int) (Measure_ba_Bool_190 Bool) (Measure_na_Int_401 Int) (Measure_bb_Bool_191 Bool)) (and (and (exists ((G_time_Int_402 Int)) (and (>= G_time_Int_402 F_time_Int_399) (set.member (tuple G_time_Int_402) G))) (= F_time_Int_399 Measure_time_Int_400)) (set.member (tuple Measure_time_Int_400 Measure_ba_Bool_190 Measure_na_Int_401 Measure_bb_Bool_191) Measure))))))
(assert (and (and (forall ((H_time_Int_438 Int) (not_H_start_time_Int_439 Int) (not_H_end_time_Int_440 Int)) (=> (and (set.member (tuple not_H_start_time_Int_439 not_H_end_time_Int_440) not_H) (set.member (tuple H_time_Int_438) H)) (not (and (<= H_time_Int_438 not_H_end_time_Int_440) (<= not_H_start_time_Int_439 H_time_Int_438))))) (and (forall ((G_time_Int_435 Int) (not_G_start_time_Int_436 Int) (not_G_end_time_Int_437 Int)) (=> (and (set.member (tuple not_G_start_time_Int_436 not_G_end_time_Int_437) not_G) (set.member (tuple G_time_Int_435) G)) (not (and (<= G_time_Int_435 not_G_end_time_Int_437) (<= not_G_start_time_Int_436 G_time_Int_435))))) (and (forall ((F_time_Int_432 Int) (not_F_start_time_Int_433 Int) (not_F_end_time_Int_434 Int)) (=> (and (set.member (tuple not_F_start_time_Int_433 not_F_end_time_Int_434) not_F) (set.member (tuple F_time_Int_432) F)) (not (and (<= F_time_Int_432 not_F_end_time_Int_434) (<= not_F_start_time_Int_433 F_time_Int_432))))) (and (forall ((E_time_Int_429 Int) (not_E_start_time_Int_430 Int) (not_E_end_time_Int_431 Int)) (=> (and (set.member (tuple not_E_start_time_Int_430 not_E_end_time_Int_431) not_E) (set.member (tuple E_time_Int_429) E)) (not (and (<= E_time_Int_429 not_E_end_time_Int_431) (<= not_E_start_time_Int_430 E_time_Int_429))))) (and (forall ((D_time_Int_426 Int) (not_D_start_time_Int_427 Int) (not_D_end_time_Int_428 Int)) (=> (and (set.member (tuple not_D_start_time_Int_427 not_D_end_time_Int_428) not_D) (set.member (tuple D_time_Int_426) D)) (not (and (<= D_time_Int_426 not_D_end_time_Int_428) (<= not_D_start_time_Int_427 D_time_Int_426))))) (and (forall ((C_time_Int_423 Int) (not_C_start_time_Int_424 Int) (not_C_end_time_Int_425 Int)) (=> (and (set.member (tuple not_C_start_time_Int_424 not_C_end_time_Int_425) not_C) (set.member (tuple C_time_Int_423) C)) (not (and (<= C_time_Int_423 not_C_end_time_Int_425) (<= not_C_start_time_Int_424 C_time_Int_423))))) (and (forall ((B_time_Int_420 Int) (not_B_start_time_Int_421 Int) (not_B_end_time_Int_422 Int)) (=> (and (set.member (tuple not_B_start_time_Int_421 not_B_end_time_Int_422) not_B) (set.member (tuple B_time_Int_420) B)) (not (and (<= B_time_Int_420 not_B_end_time_Int_422) (<= not_B_start_time_Int_421 B_time_Int_420))))) (forall ((A_time_Int_417 Int) (not_A_start_time_Int_418 Int) (not_A_end_time_Int_419 Int)) (=> (and (set.member (tuple not_A_start_time_Int_418 not_A_end_time_Int_419) not_A) (set.member (tuple A_time_Int_417) A)) (not (and (<= A_time_Int_417 not_A_end_time_Int_419) (<= not_A_start_time_Int_418 A_time_Int_417)))))))))))) (forall ((Measure_time_Int_413 Int) (Measure_ba_Bool_196 Bool) (Measure_na_Int_414 Int) (Measure_bb_Bool_197 Bool) (Measure_time_Int_415 Int) (Measure_ba_Bool_198 Bool) (Measure_na_Int_416 Int) (Measure_bb_Bool_199 Bool)) (=> (and (set.member (tuple Measure_time_Int_415 Measure_ba_Bool_198 Measure_na_Int_416 Measure_bb_Bool_199) Measure) (set.member (tuple Measure_time_Int_413 Measure_ba_Bool_196 Measure_na_Int_414 Measure_bb_Bool_197) Measure)) (=> (= Measure_time_Int_413 Measure_time_Int_415) (and (= Measure_bb_Bool_197 Measure_bb_Bool_199) (and (= Measure_na_Int_414 Measure_na_Int_416) (and (= Measure_ba_Bool_196 Measure_ba_Bool_198) (= Measure_time_Int_413 Measure_time_Int_415)))))))))
(assert (=> (exists ((A_time_Int_441 Int)) (and true (set.member (tuple A_time_Int_441) A))) (and (exists ((A_time_Int_444 Int)) (and (forall ((A_time_Int_445 Int)) (=> (set.member (tuple A_time_Int_445) A) (<= A_time_Int_445 A_time_Int_444))) (set.member (tuple A_time_Int_444) A))) (exists ((A_time_Int_442 Int)) (and (forall ((A_time_Int_443 Int)) (=> (set.member (tuple A_time_Int_443) A) (>= A_time_Int_443 A_time_Int_442))) (set.member (tuple A_time_Int_442) A))))))
(assert (=> (exists ((B_time_Int_446 Int)) (and true (set.member (tuple B_time_Int_446) B))) (and (exists ((B_time_Int_449 Int)) (and (forall ((B_time_Int_450 Int)) (=> (set.member (tuple B_time_Int_450) B) (<= B_time_Int_450 B_time_Int_449))) (set.member (tuple B_time_Int_449) B))) (exists ((B_time_Int_447 Int)) (and (forall ((B_time_Int_448 Int)) (=> (set.member (tuple B_time_Int_448) B) (>= B_time_Int_448 B_time_Int_447))) (set.member (tuple B_time_Int_447) B))))))
(assert (=> (exists ((C_time_Int_451 Int)) (and true (set.member (tuple C_time_Int_451) C))) (and (exists ((C_time_Int_454 Int)) (and (forall ((C_time_Int_455 Int)) (=> (set.member (tuple C_time_Int_455) C) (<= C_time_Int_455 C_time_Int_454))) (set.member (tuple C_time_Int_454) C))) (exists ((C_time_Int_452 Int)) (and (forall ((C_time_Int_453 Int)) (=> (set.member (tuple C_time_Int_453) C) (>= C_time_Int_453 C_time_Int_452))) (set.member (tuple C_time_Int_452) C))))))
(assert (=> (exists ((D_time_Int_456 Int)) (and true (set.member (tuple D_time_Int_456) D))) (and (exists ((D_time_Int_459 Int)) (and (forall ((D_time_Int_460 Int)) (=> (set.member (tuple D_time_Int_460) D) (<= D_time_Int_460 D_time_Int_459))) (set.member (tuple D_time_Int_459) D))) (exists ((D_time_Int_457 Int)) (and (forall ((D_time_Int_458 Int)) (=> (set.member (tuple D_time_Int_458) D) (>= D_time_Int_458 D_time_Int_457))) (set.member (tuple D_time_Int_457) D))))))
(assert (=> (exists ((E_time_Int_461 Int)) (and true (set.member (tuple E_time_Int_461) E))) (and (exists ((E_time_Int_464 Int)) (and (forall ((E_time_Int_465 Int)) (=> (set.member (tuple E_time_Int_465) E) (<= E_time_Int_465 E_time_Int_464))) (set.member (tuple E_time_Int_464) E))) (exists ((E_time_Int_462 Int)) (and (forall ((E_time_Int_463 Int)) (=> (set.member (tuple E_time_Int_463) E) (>= E_time_Int_463 E_time_Int_462))) (set.member (tuple E_time_Int_462) E))))))
(assert (=> (exists ((F_time_Int_466 Int)) (and true (set.member (tuple F_time_Int_466) F))) (and (exists ((F_time_Int_469 Int)) (and (forall ((F_time_Int_470 Int)) (=> (set.member (tuple F_time_Int_470) F) (<= F_time_Int_470 F_time_Int_469))) (set.member (tuple F_time_Int_469) F))) (exists ((F_time_Int_467 Int)) (and (forall ((F_time_Int_468 Int)) (=> (set.member (tuple F_time_Int_468) F) (>= F_time_Int_468 F_time_Int_467))) (set.member (tuple F_time_Int_467) F))))))
(assert (=> (exists ((G_time_Int_471 Int)) (and true (set.member (tuple G_time_Int_471) G))) (and (exists ((G_time_Int_474 Int)) (and (forall ((G_time_Int_475 Int)) (=> (set.member (tuple G_time_Int_475) G) (<= G_time_Int_475 G_time_Int_474))) (set.member (tuple G_time_Int_474) G))) (exists ((G_time_Int_472 Int)) (and (forall ((G_time_Int_473 Int)) (=> (set.member (tuple G_time_Int_473) G) (>= G_time_Int_473 G_time_Int_472))) (set.member (tuple G_time_Int_472) G))))))
(assert (=> (exists ((H_time_Int_476 Int)) (and true (set.member (tuple H_time_Int_476) H))) (and (exists ((H_time_Int_479 Int)) (and (forall ((H_time_Int_480 Int)) (=> (set.member (tuple H_time_Int_480) H) (<= H_time_Int_480 H_time_Int_479))) (set.member (tuple H_time_Int_479) H))) (exists ((H_time_Int_477 Int)) (and (forall ((H_time_Int_478 Int)) (=> (set.member (tuple H_time_Int_478) H) (>= H_time_Int_478 H_time_Int_477))) (set.member (tuple H_time_Int_477) H))))))
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
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert (forall ((Measure_time_Int_481 Int) (Measure_ba_Bool_200 Bool) (Measure_na_Int_482 Int) (Measure_bb_Bool_201 Bool)) (=> (set.member (tuple Measure_time_Int_481 Measure_ba_Bool_200 Measure_na_Int_482 Measure_bb_Bool_201) Measure) (exists ((time_val_Int_483 Int)) (and (= time_val_Int_483 Measure_time_Int_481) (set.member (tuple time_val_Int_483) time))))))
(check-sat)
