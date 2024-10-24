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
(declare-const time (Set (Tuple Int)))
(declare-const DressingStarted (Set (Tuple Int)))
(declare-const not_DressingStarted (Set (Tuple Int Int)))
(declare-const DressingComplete (Set (Tuple Int)))
(declare-const not_DressingComplete (Set (Tuple Int Int)))
(declare-const DressingAbandoned (Set (Tuple Int)))
(declare-const not_DressingAbandoned (Set (Tuple Int Int)))
(declare-const CurtainOpenRqt (Set (Tuple Int)))
(declare-const not_CurtainOpenRqt (Set (Tuple Int Int)))
(declare-const CurtainsOpened (Set (Tuple Int)))
(declare-const not_CurtainsOpened (Set (Tuple Int Int)))
(declare-const RefuseRequest (Set (Tuple Int)))
(declare-const not_RefuseRequest (Set (Tuple Int Int)))
(declare-const UserFallen (Set (Tuple Int)))
(declare-const not_UserFallen (Set (Tuple Int Int)))
(declare-const SupportCalled (Set (Tuple Int)))
(declare-const not_SupportCalled (Set (Tuple Int Int)))
(declare-const RetryAgreed (Set (Tuple Int)))
(declare-const not_RetryAgreed (Set (Tuple Int Int)))
(declare-const Measure (Set (Tuple Int Bool Int Bool Int)))
(assert (set.exists ((tuple_108 (Tuple Int Int Bool Int Bool Int))) (rel.product CurtainOpenRqt Measure) (= ((_ tuple.select 0) tuple_108) ((_ tuple.select 1) tuple_108))))
(assert (set.forall ((tuple_2 (Tuple Int))) DressingStarted (set.exists ((tuple_3 (Tuple Int Bool Int Bool Int))) Measure (and (or (and (=> (and true (and (not (< ((_ tuple.select 2) tuple_3) 19)) (and (not (< ((_ tuple.select 2) tuple_3) 17)) true))) (set.exists ((tuple_5 (Tuple Int))) DressingComplete (and (>= ((_ tuple.select 0) tuple_5) (+ ((_ tuple.select 0) tuple_2) 0)) (<= ((_ tuple.select 0) tuple_5) (+ ((_ tuple.select 0) tuple_2) 120))))) (and (=> (and (< ((_ tuple.select 2) tuple_3) 19) (and (not (< ((_ tuple.select 2) tuple_3) 17)) true)) (set.exists ((tuple_6 (Tuple Int))) DressingComplete (and (>= ((_ tuple.select 0) tuple_6) (+ ((_ tuple.select 0) tuple_2) 0)) (<= ((_ tuple.select 0) tuple_6) (+ ((_ tuple.select 0) tuple_2) 90))))) (=> (and (< ((_ tuple.select 2) tuple_3) 17) true) (set.exists ((tuple_7 (Tuple Int))) DressingComplete (and (>= ((_ tuple.select 0) tuple_7) (+ ((_ tuple.select 0) tuple_2) 0)) (<= ((_ tuple.select 0) tuple_7) (+ ((_ tuple.select 0) tuple_2) 60))))))) (set.exists ((tuple_4 (Tuple Int))) DressingAbandoned (and (>= ((_ tuple.select 0) tuple_4) (+ ((_ tuple.select 0) tuple_2) 0)) (<= ((_ tuple.select 0) tuple_4) (+ ((_ tuple.select 0) tuple_2) 120))))) (= ((_ tuple.select 0) tuple_2) ((_ tuple.select 0) tuple_3))))))
(assert (set.forall ((tuple_18 (Tuple Int))) DressingStarted (set.exists ((tuple_19 (Tuple Int Bool Int Bool Int))) Measure (and (or (and (=> (and true (and (not (<= ((_ tuple.select 2) tuple_19) 22)) (and (not (and ((_ tuple.select 1) tuple_19) (<= ((_ tuple.select 2) tuple_19) 11))) true))) (set.exists ((tuple_21 (Tuple Int))) DressingComplete (and (>= ((_ tuple.select 0) tuple_21) (+ ((_ tuple.select 0) tuple_18) 0)) (<= ((_ tuple.select 0) tuple_21) (+ ((_ tuple.select 0) tuple_18) 120))))) (and (=> (and (<= ((_ tuple.select 2) tuple_19) 22) (and (not (and ((_ tuple.select 1) tuple_19) (<= ((_ tuple.select 2) tuple_19) 11))) true)) (set.exists ((tuple_22 (Tuple Int))) DressingComplete (and (>= ((_ tuple.select 0) tuple_22) (+ ((_ tuple.select 0) tuple_18) 0)) (<= ((_ tuple.select 0) tuple_22) (+ ((_ tuple.select 0) tuple_18) (* (- 120 (* (- 22 ((_ tuple.select 2) tuple_19)) 15)) 1)))))) (=> (and (and ((_ tuple.select 1) tuple_19) (<= ((_ tuple.select 2) tuple_19) 11)) true) (and (=> (and true (and (not (not ((_ tuple.select 3) tuple_19))) true)) (set.exists ((tuple_23 (Tuple Int))) SupportCalled (and (>= ((_ tuple.select 0) tuple_23) (+ ((_ tuple.select 0) tuple_18) 0)) (<= ((_ tuple.select 0) tuple_23) (+ ((_ tuple.select 0) tuple_18) 0))))) (=> (and (not ((_ tuple.select 3) tuple_19)) true) true))))) (set.exists ((tuple_20 (Tuple Int))) DressingAbandoned (and (>= ((_ tuple.select 0) tuple_20) (+ ((_ tuple.select 0) tuple_18) 0)) (<= ((_ tuple.select 0) tuple_20) (+ ((_ tuple.select 0) tuple_18) 120))))) (= ((_ tuple.select 0) tuple_18) ((_ tuple.select 0) tuple_19))))))
(assert (set.forall ((tuple_34 (Tuple Int))) DressingStarted (set.exists ((tuple_35 (Tuple Int Bool Int Bool Int))) Measure (and (or (set.exists ((tuple_36 (Tuple Int))) DressingAbandoned (and (>= ((_ tuple.select 0) tuple_36) (+ ((_ tuple.select 0) tuple_34) 0)) (<= ((_ tuple.select 0) tuple_36) (+ ((_ tuple.select 0) tuple_34) 0)))) (not (> ((_ tuple.select 4) tuple_35) 2))) (= ((_ tuple.select 0) tuple_34) ((_ tuple.select 0) tuple_35))))))
(assert (set.forall ((tuple_47 (Tuple Int))) DressingStarted (set.exists ((tuple_48 (Tuple Int Bool Int Bool Int))) Measure (and (or (and (=> (and true (and (not (not ((_ tuple.select 3) tuple_48))) true)) (set.exists ((tuple_49 (Tuple Int))) SupportCalled (and (>= ((_ tuple.select 0) tuple_49) (+ ((_ tuple.select 0) tuple_47) 0)) (<= ((_ tuple.select 0) tuple_49) (+ ((_ tuple.select 0) tuple_47) 0))))) (=> (and (not ((_ tuple.select 3) tuple_48)) true) true)) (not (> ((_ tuple.select 4) tuple_48) 2))) (= ((_ tuple.select 0) tuple_47) ((_ tuple.select 0) tuple_48))))))
(assert (set.forall ((tuple_60 (Tuple Int))) RetryAgreed (set.exists ((tuple_61 (Tuple Int Bool Int Bool Int))) Measure (and (set.exists ((tuple_62 (Tuple Int))) DressingStarted (and (>= ((_ tuple.select 0) tuple_62) (+ ((_ tuple.select 0) tuple_60) 1)) (<= ((_ tuple.select 0) tuple_62) (+ ((_ tuple.select 0) tuple_60) 30)))) (= ((_ tuple.select 0) tuple_60) ((_ tuple.select 0) tuple_61))))))
(assert (set.forall ((tuple_70 (Tuple Int))) RetryAgreed (set.exists ((tuple_71 (Tuple Int Bool Int Bool Int))) Measure (and (and (=> (and true (and (not (= ((_ tuple.select 4) tuple_71) 3)) true)) (set.exists ((tuple_72 (Tuple Int))) DressingStarted (>= ((_ tuple.select 0) tuple_72) ((_ tuple.select 0) tuple_70)))) (=> (and (= ((_ tuple.select 4) tuple_71) 3) true) (=> true (or (set.exists ((tuple_74 (Tuple Int Bool Int Bool Int))) Measure (and (set.exists ((tuple_75 (Tuple Int))) SupportCalled (and (>= ((_ tuple.select 0) tuple_75) (+ ((_ tuple.select 0) tuple_74) 0)) (<= ((_ tuple.select 0) tuple_75) (+ ((_ tuple.select 0) tuple_74) 30)))) (= (+ ((_ tuple.select 0) tuple_71) 30) ((_ tuple.select 0) tuple_74)))) (set.exists ((tuple_73 (Tuple Int))) DressingStarted (and (>= ((_ tuple.select 0) tuple_73) (+ ((_ tuple.select 0) tuple_70) 0)) (<= ((_ tuple.select 0) tuple_73) (+ ((_ tuple.select 0) tuple_70) 30)))))))) (= ((_ tuple.select 0) tuple_70) ((_ tuple.select 0) tuple_71))))))
(assert (set.forall ((tuple_86 (Tuple Int))) RetryAgreed (set.exists ((tuple_87 (Tuple Int Bool Int Bool Int))) Measure (and (or (set.exists ((tuple_89 (Tuple Int))) DressingAbandoned (>= ((_ tuple.select 0) tuple_89) ((_ tuple.select 0) tuple_86))) (set.exists ((tuple_88 (Tuple Int))) DressingComplete (>= ((_ tuple.select 0) tuple_88) ((_ tuple.select 0) tuple_86)))) (= ((_ tuple.select 0) tuple_86) ((_ tuple.select 0) tuple_87))))))
(assert (set.forall ((tuple_98 (Tuple Int))) CurtainOpenRqt (set.exists ((tuple_99 (Tuple Int Bool Int Bool Int))) Measure (and (and (=> (and true (and (not ((_ tuple.select 1) tuple_99)) (and (not (> ((_ tuple.select 4) tuple_99) 2)) true))) (set.exists ((tuple_100 (Tuple Int))) CurtainsOpened (and (>= ((_ tuple.select 0) tuple_100) (+ ((_ tuple.select 0) tuple_98) 0)) (<= ((_ tuple.select 0) tuple_100) (+ ((_ tuple.select 0) tuple_98) 60))))) (and (=> (and ((_ tuple.select 1) tuple_99) (and (not (> ((_ tuple.select 4) tuple_99) 2)) true)) (set.exists ((tuple_101 (Tuple Int))) RefuseRequest (and (>= ((_ tuple.select 0) tuple_101) (+ ((_ tuple.select 0) tuple_98) 0)) (<= ((_ tuple.select 0) tuple_101) (+ ((_ tuple.select 0) tuple_98) 30))))) (=> (and (> ((_ tuple.select 4) tuple_99) 2) true) (set.exists ((tuple_102 (Tuple Int))) CurtainsOpened (and (>= ((_ tuple.select 0) tuple_102) (+ ((_ tuple.select 0) tuple_98) 0)) (<= ((_ tuple.select 0) tuple_102) (+ ((_ tuple.select 0) tuple_98) 60))))))) (= ((_ tuple.select 0) tuple_98) ((_ tuple.select 0) tuple_99))))))
(assert (set.forall ((tuple_112 (Tuple Int))) UserFallen (set.exists ((tuple_113 (Tuple Int Bool Int Bool Int))) Measure (and (and (=> (and true (and (not (not ((_ tuple.select 3) tuple_113))) true)) (set.exists ((tuple_114 (Tuple Int))) SupportCalled (and (>= ((_ tuple.select 0) tuple_114) (+ ((_ tuple.select 0) tuple_112) 0)) (<= ((_ tuple.select 0) tuple_114) (+ ((_ tuple.select 0) tuple_112) 0))))) (=> (and (not ((_ tuple.select 3) tuple_113)) true) true)) (= ((_ tuple.select 0) tuple_112) ((_ tuple.select 0) tuple_113))))))
(assert (set.forall ((tuple_122 (Tuple Int))) DressingAbandoned (set.exists ((tuple_123 (Tuple Int Bool Int Bool Int))) Measure (and (=> true (or (set.exists ((tuple_125 (Tuple Int Bool Int Bool Int))) Measure (and (and (=> (and true (and (not (not ((_ tuple.select 3) tuple_125))) true)) (set.exists ((tuple_126 (Tuple Int))) SupportCalled (and (>= ((_ tuple.select 0) tuple_126) (+ ((_ tuple.select 0) tuple_125) 0)) (<= ((_ tuple.select 0) tuple_126) (+ ((_ tuple.select 0) tuple_125) 0))))) (=> (and (not ((_ tuple.select 3) tuple_125)) true) true)) (= (+ ((_ tuple.select 0) tuple_123) 1800) ((_ tuple.select 0) tuple_125)))) (set.exists ((tuple_124 (Tuple Int))) RetryAgreed (and (>= ((_ tuple.select 0) tuple_124) (+ ((_ tuple.select 0) tuple_122) 0)) (<= ((_ tuple.select 0) tuple_124) (+ ((_ tuple.select 0) tuple_122) 1800)))))) (= ((_ tuple.select 0) tuple_122) ((_ tuple.select 0) tuple_123))))))
(assert (set.forall ((tuple_136 (Tuple Int))) DressingStarted (set.exists ((tuple_137 (Tuple Int Bool Int Bool Int))) Measure (and (or (or (set.exists ((tuple_139 (Tuple Int))) DressingComplete (and (>= ((_ tuple.select 0) tuple_139) (+ ((_ tuple.select 0) tuple_136) 0)) (<= ((_ tuple.select 0) tuple_139) (+ ((_ tuple.select 0) tuple_136) 60)))) (set.exists ((tuple_138 (Tuple Int))) DressingAbandoned (and (>= ((_ tuple.select 0) tuple_138) (+ ((_ tuple.select 0) tuple_136) 0)) (<= ((_ tuple.select 0) tuple_138) (+ ((_ tuple.select 0) tuple_136) 120))))) (not (or ((_ tuple.select 1) tuple_137) (< ((_ tuple.select 2) tuple_137) 16)))) (= ((_ tuple.select 0) tuple_136) ((_ tuple.select 0) tuple_137))))))
(assert (set.forall ((tuple_151 (Tuple Int))) UserFallen (set.exists ((tuple_152 (Tuple Int Bool Int Bool Int))) Measure (and (or (set.exists ((tuple_154 (Tuple Int Int))) not_SupportCalled (and (= ((_ tuple.select 1) tuple_154) (+ ((_ tuple.select 0) tuple_151) 120)) (= ((_ tuple.select 0) tuple_154) (+ ((_ tuple.select 0) tuple_151) 0)))) (not ((_ tuple.select 3) tuple_152))) (= ((_ tuple.select 0) tuple_151) ((_ tuple.select 0) tuple_152))))))
(assert (and (and (forall ((RetryAgreed_time_Int_24 Int) (not_RetryAgreed_start_time_Int_25 Int) (not_RetryAgreed_end_time_Int_26 Int)) (=> (and (set.member (tuple not_RetryAgreed_start_time_Int_25 not_RetryAgreed_end_time_Int_26) not_RetryAgreed) (set.member (tuple RetryAgreed_time_Int_24) RetryAgreed)) (not (and (<= RetryAgreed_time_Int_24 not_RetryAgreed_end_time_Int_26) (<= not_RetryAgreed_start_time_Int_25 RetryAgreed_time_Int_24))))) (and (forall ((SupportCalled_time_Int_21 Int) (not_SupportCalled_start_time_Int_22 Int) (not_SupportCalled_end_time_Int_23 Int)) (=> (and (set.member (tuple not_SupportCalled_start_time_Int_22 not_SupportCalled_end_time_Int_23) not_SupportCalled) (set.member (tuple SupportCalled_time_Int_21) SupportCalled)) (not (and (<= SupportCalled_time_Int_21 not_SupportCalled_end_time_Int_23) (<= not_SupportCalled_start_time_Int_22 SupportCalled_time_Int_21))))) (and (forall ((UserFallen_time_Int_18 Int) (not_UserFallen_start_time_Int_19 Int) (not_UserFallen_end_time_Int_20 Int)) (=> (and (set.member (tuple not_UserFallen_start_time_Int_19 not_UserFallen_end_time_Int_20) not_UserFallen) (set.member (tuple UserFallen_time_Int_18) UserFallen)) (not (and (<= UserFallen_time_Int_18 not_UserFallen_end_time_Int_20) (<= not_UserFallen_start_time_Int_19 UserFallen_time_Int_18))))) (and (forall ((RefuseRequest_time_Int_15 Int) (not_RefuseRequest_start_time_Int_16 Int) (not_RefuseRequest_end_time_Int_17 Int)) (=> (and (set.member (tuple not_RefuseRequest_start_time_Int_16 not_RefuseRequest_end_time_Int_17) not_RefuseRequest) (set.member (tuple RefuseRequest_time_Int_15) RefuseRequest)) (not (and (<= RefuseRequest_time_Int_15 not_RefuseRequest_end_time_Int_17) (<= not_RefuseRequest_start_time_Int_16 RefuseRequest_time_Int_15))))) (and (forall ((CurtainsOpened_time_Int_12 Int) (not_CurtainsOpened_start_time_Int_13 Int) (not_CurtainsOpened_end_time_Int_14 Int)) (=> (and (set.member (tuple not_CurtainsOpened_start_time_Int_13 not_CurtainsOpened_end_time_Int_14) not_CurtainsOpened) (set.member (tuple CurtainsOpened_time_Int_12) CurtainsOpened)) (not (and (<= CurtainsOpened_time_Int_12 not_CurtainsOpened_end_time_Int_14) (<= not_CurtainsOpened_start_time_Int_13 CurtainsOpened_time_Int_12))))) (and (forall ((CurtainOpenRqt_time_Int_9 Int) (not_CurtainOpenRqt_start_time_Int_10 Int) (not_CurtainOpenRqt_end_time_Int_11 Int)) (=> (and (set.member (tuple not_CurtainOpenRqt_start_time_Int_10 not_CurtainOpenRqt_end_time_Int_11) not_CurtainOpenRqt) (set.member (tuple CurtainOpenRqt_time_Int_9) CurtainOpenRqt)) (not (and (<= CurtainOpenRqt_time_Int_9 not_CurtainOpenRqt_end_time_Int_11) (<= not_CurtainOpenRqt_start_time_Int_10 CurtainOpenRqt_time_Int_9))))) (and (forall ((DressingAbandoned_time_Int_6 Int) (not_DressingAbandoned_start_time_Int_7 Int) (not_DressingAbandoned_end_time_Int_8 Int)) (=> (and (set.member (tuple not_DressingAbandoned_start_time_Int_7 not_DressingAbandoned_end_time_Int_8) not_DressingAbandoned) (set.member (tuple DressingAbandoned_time_Int_6) DressingAbandoned)) (not (and (<= DressingAbandoned_time_Int_6 not_DressingAbandoned_end_time_Int_8) (<= not_DressingAbandoned_start_time_Int_7 DressingAbandoned_time_Int_6))))) (and (forall ((DressingComplete_time_Int_3 Int) (not_DressingComplete_start_time_Int_4 Int) (not_DressingComplete_end_time_Int_5 Int)) (=> (and (set.member (tuple not_DressingComplete_start_time_Int_4 not_DressingComplete_end_time_Int_5) not_DressingComplete) (set.member (tuple DressingComplete_time_Int_3) DressingComplete)) (not (and (<= DressingComplete_time_Int_3 not_DressingComplete_end_time_Int_5) (<= not_DressingComplete_start_time_Int_4 DressingComplete_time_Int_3))))) (forall ((DressingStarted_time_Int_0 Int) (not_DressingStarted_start_time_Int_1 Int) (not_DressingStarted_end_time_Int_2 Int)) (=> (and (set.member (tuple not_DressingStarted_start_time_Int_1 not_DressingStarted_end_time_Int_2) not_DressingStarted) (set.member (tuple DressingStarted_time_Int_0) DressingStarted)) (not (and (<= DressingStarted_time_Int_0 not_DressingStarted_end_time_Int_2) (<= not_DressingStarted_start_time_Int_1 DressingStarted_time_Int_0))))))))))))) (set.forall ((tuple_215 (Tuple Int Bool Int Bool Int Int Bool Int Bool Int))) (rel.product Measure Measure) (=> (= ((_ tuple.select 0) tuple_215) ((_ tuple.select 5) tuple_215)) (and (= ((_ tuple.select 4) tuple_215) ((_ tuple.select 9) tuple_215)) (and (= ((_ tuple.select 3) tuple_215) ((_ tuple.select 8) tuple_215)) (and (= ((_ tuple.select 2) tuple_215) ((_ tuple.select 7) tuple_215)) (and (= ((_ tuple.select 1) tuple_215) ((_ tuple.select 6) tuple_215)) (= ((_ tuple.select 0) tuple_215) ((_ tuple.select 5) tuple_215))))))))))
(assert (=> (set.exists ((tuple_170 (Tuple Int))) DressingStarted true) (and (set.exists ((tuple_173 (Tuple Int))) DressingStarted (set.forall ((tuple_174 (Tuple Int))) DressingStarted (<= ((_ tuple.select 0) tuple_174) ((_ tuple.select 0) tuple_173)))) (set.exists ((tuple_171 (Tuple Int))) DressingStarted (set.forall ((tuple_172 (Tuple Int))) DressingStarted (>= ((_ tuple.select 0) tuple_172) ((_ tuple.select 0) tuple_171)))))))
(assert (=> (set.exists ((tuple_175 (Tuple Int))) DressingComplete true) (and (set.exists ((tuple_178 (Tuple Int))) DressingComplete (set.forall ((tuple_179 (Tuple Int))) DressingComplete (<= ((_ tuple.select 0) tuple_179) ((_ tuple.select 0) tuple_178)))) (set.exists ((tuple_176 (Tuple Int))) DressingComplete (set.forall ((tuple_177 (Tuple Int))) DressingComplete (>= ((_ tuple.select 0) tuple_177) ((_ tuple.select 0) tuple_176)))))))
(assert (=> (set.exists ((tuple_180 (Tuple Int))) DressingAbandoned true) (and (set.exists ((tuple_183 (Tuple Int))) DressingAbandoned (set.forall ((tuple_184 (Tuple Int))) DressingAbandoned (<= ((_ tuple.select 0) tuple_184) ((_ tuple.select 0) tuple_183)))) (set.exists ((tuple_181 (Tuple Int))) DressingAbandoned (set.forall ((tuple_182 (Tuple Int))) DressingAbandoned (>= ((_ tuple.select 0) tuple_182) ((_ tuple.select 0) tuple_181)))))))
(assert (=> (set.exists ((tuple_185 (Tuple Int))) CurtainOpenRqt true) (and (set.exists ((tuple_188 (Tuple Int))) CurtainOpenRqt (set.forall ((tuple_189 (Tuple Int))) CurtainOpenRqt (<= ((_ tuple.select 0) tuple_189) ((_ tuple.select 0) tuple_188)))) (set.exists ((tuple_186 (Tuple Int))) CurtainOpenRqt (set.forall ((tuple_187 (Tuple Int))) CurtainOpenRqt (>= ((_ tuple.select 0) tuple_187) ((_ tuple.select 0) tuple_186)))))))
(assert (=> (set.exists ((tuple_190 (Tuple Int))) CurtainsOpened true) (and (set.exists ((tuple_193 (Tuple Int))) CurtainsOpened (set.forall ((tuple_194 (Tuple Int))) CurtainsOpened (<= ((_ tuple.select 0) tuple_194) ((_ tuple.select 0) tuple_193)))) (set.exists ((tuple_191 (Tuple Int))) CurtainsOpened (set.forall ((tuple_192 (Tuple Int))) CurtainsOpened (>= ((_ tuple.select 0) tuple_192) ((_ tuple.select 0) tuple_191)))))))
(assert (=> (set.exists ((tuple_195 (Tuple Int))) RefuseRequest true) (and (set.exists ((tuple_198 (Tuple Int))) RefuseRequest (set.forall ((tuple_199 (Tuple Int))) RefuseRequest (<= ((_ tuple.select 0) tuple_199) ((_ tuple.select 0) tuple_198)))) (set.exists ((tuple_196 (Tuple Int))) RefuseRequest (set.forall ((tuple_197 (Tuple Int))) RefuseRequest (>= ((_ tuple.select 0) tuple_197) ((_ tuple.select 0) tuple_196)))))))
(assert (=> (set.exists ((tuple_200 (Tuple Int))) UserFallen true) (and (set.exists ((tuple_203 (Tuple Int))) UserFallen (set.forall ((tuple_204 (Tuple Int))) UserFallen (<= ((_ tuple.select 0) tuple_204) ((_ tuple.select 0) tuple_203)))) (set.exists ((tuple_201 (Tuple Int))) UserFallen (set.forall ((tuple_202 (Tuple Int))) UserFallen (>= ((_ tuple.select 0) tuple_202) ((_ tuple.select 0) tuple_201)))))))
(assert (=> (set.exists ((tuple_205 (Tuple Int))) SupportCalled true) (and (set.exists ((tuple_208 (Tuple Int))) SupportCalled (set.forall ((tuple_209 (Tuple Int))) SupportCalled (<= ((_ tuple.select 0) tuple_209) ((_ tuple.select 0) tuple_208)))) (set.exists ((tuple_206 (Tuple Int))) SupportCalled (set.forall ((tuple_207 (Tuple Int))) SupportCalled (>= ((_ tuple.select 0) tuple_207) ((_ tuple.select 0) tuple_206)))))))
(assert (=> (set.exists ((tuple_210 (Tuple Int))) RetryAgreed true) (and (set.exists ((tuple_213 (Tuple Int))) RetryAgreed (set.forall ((tuple_214 (Tuple Int))) RetryAgreed (<= ((_ tuple.select 0) tuple_214) ((_ tuple.select 0) tuple_213)))) (set.exists ((tuple_211 (Tuple Int))) RetryAgreed (set.forall ((tuple_212 (Tuple Int))) RetryAgreed (>= ((_ tuple.select 0) tuple_212) ((_ tuple.select 0) tuple_211)))))))
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
(assert true)
(assert true)
(assert (set.forall ((tuple_216 (Tuple Int Bool Int Bool Int))) Measure (set.exists ((tuple_217 (Tuple Int))) time (= ((_ tuple.select 0) tuple_217) ((_ tuple.select 0) tuple_216)))))
(check-sat)
(get-model)
