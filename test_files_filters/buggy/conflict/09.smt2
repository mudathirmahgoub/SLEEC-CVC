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
(assert (set.some (lambda ((tuple_132 (Tuple Int Int Bool Int Bool Int))) (= ((_ tuple.select 0) tuple_132) ((_ tuple.select 1) tuple_132))) (rel.product DressingAbandoned Measure)))
(assert (set.all (lambda ((tuple_2 (Tuple Int))) (set.some (lambda ((tuple_3 (Tuple Int Bool Int Bool Int))) (and (or (and (=> (and true (and (not (< ((_ tuple.select 2) tuple_3) 19)) (and (not (< ((_ tuple.select 2) tuple_3) 17)) true))) (set.some (lambda ((tuple_5 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_5) (+ ((_ tuple.select 0) tuple_2) 0)) (<= ((_ tuple.select 0) tuple_5) (+ ((_ tuple.select 0) tuple_2) 120)))) DressingComplete)) (and (=> (and (< ((_ tuple.select 2) tuple_3) 19) (and (not (< ((_ tuple.select 2) tuple_3) 17)) true)) (set.some (lambda ((tuple_6 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_6) (+ ((_ tuple.select 0) tuple_2) 0)) (<= ((_ tuple.select 0) tuple_6) (+ ((_ tuple.select 0) tuple_2) 90)))) DressingComplete)) (=> (and (< ((_ tuple.select 2) tuple_3) 17) true) (set.some (lambda ((tuple_7 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_7) (+ ((_ tuple.select 0) tuple_2) 0)) (<= ((_ tuple.select 0) tuple_7) (+ ((_ tuple.select 0) tuple_2) 60)))) DressingComplete)))) (set.some (lambda ((tuple_4 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_4) (+ ((_ tuple.select 0) tuple_2) 0)) (<= ((_ tuple.select 0) tuple_4) (+ ((_ tuple.select 0) tuple_2) 120)))) DressingAbandoned)) (= ((_ tuple.select 0) tuple_2) ((_ tuple.select 0) tuple_3)))) Measure)) DressingStarted))
(assert (set.all (lambda ((tuple_18 (Tuple Int))) (set.some (lambda ((tuple_19 (Tuple Int Bool Int Bool Int))) (and (or (and (=> (and true (and (not (<= ((_ tuple.select 2) tuple_19) 22)) (and (not (and ((_ tuple.select 1) tuple_19) (<= ((_ tuple.select 2) tuple_19) 11))) true))) (set.some (lambda ((tuple_21 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_21) (+ ((_ tuple.select 0) tuple_18) 0)) (<= ((_ tuple.select 0) tuple_21) (+ ((_ tuple.select 0) tuple_18) 120)))) DressingComplete)) (and (=> (and (<= ((_ tuple.select 2) tuple_19) 22) (and (not (and ((_ tuple.select 1) tuple_19) (<= ((_ tuple.select 2) tuple_19) 11))) true)) (set.some (lambda ((tuple_22 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_22) (+ ((_ tuple.select 0) tuple_18) 0)) (<= ((_ tuple.select 0) tuple_22) (+ ((_ tuple.select 0) tuple_18) (* (- 120 (* (- 22 ((_ tuple.select 2) tuple_19)) 15)) 1))))) DressingComplete)) (=> (and (and ((_ tuple.select 1) tuple_19) (<= ((_ tuple.select 2) tuple_19) 11)) true) (and (=> (and true (and (not (not ((_ tuple.select 3) tuple_19))) true)) (set.some (lambda ((tuple_23 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_23) (+ ((_ tuple.select 0) tuple_18) 0)) (<= ((_ tuple.select 0) tuple_23) (+ ((_ tuple.select 0) tuple_18) 0)))) SupportCalled)) (=> (and (not ((_ tuple.select 3) tuple_19)) true) true))))) (set.some (lambda ((tuple_20 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_20) (+ ((_ tuple.select 0) tuple_18) 0)) (<= ((_ tuple.select 0) tuple_20) (+ ((_ tuple.select 0) tuple_18) 120)))) DressingAbandoned)) (= ((_ tuple.select 0) tuple_18) ((_ tuple.select 0) tuple_19)))) Measure)) DressingStarted))
(assert (set.all (lambda ((tuple_34 (Tuple Int))) (set.some (lambda ((tuple_35 (Tuple Int Bool Int Bool Int))) (and (or (set.some (lambda ((tuple_36 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_36) (+ ((_ tuple.select 0) tuple_34) 0)) (<= ((_ tuple.select 0) tuple_36) (+ ((_ tuple.select 0) tuple_34) 0)))) DressingAbandoned) (not (> ((_ tuple.select 4) tuple_35) 2))) (= ((_ tuple.select 0) tuple_34) ((_ tuple.select 0) tuple_35)))) Measure)) DressingStarted))
(assert (set.all (lambda ((tuple_47 (Tuple Int))) (set.some (lambda ((tuple_48 (Tuple Int Bool Int Bool Int))) (and (or (and (=> (and true (and (not (not ((_ tuple.select 3) tuple_48))) true)) (set.some (lambda ((tuple_49 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_49) (+ ((_ tuple.select 0) tuple_47) 0)) (<= ((_ tuple.select 0) tuple_49) (+ ((_ tuple.select 0) tuple_47) 0)))) SupportCalled)) (=> (and (not ((_ tuple.select 3) tuple_48)) true) true)) (not (> ((_ tuple.select 4) tuple_48) 2))) (= ((_ tuple.select 0) tuple_47) ((_ tuple.select 0) tuple_48)))) Measure)) DressingStarted))
(assert (set.all (lambda ((tuple_60 (Tuple Int))) (set.some (lambda ((tuple_61 (Tuple Int Bool Int Bool Int))) (and (set.some (lambda ((tuple_62 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_62) (+ ((_ tuple.select 0) tuple_60) 1)) (<= ((_ tuple.select 0) tuple_62) (+ ((_ tuple.select 0) tuple_60) 30)))) DressingStarted) (= ((_ tuple.select 0) tuple_60) ((_ tuple.select 0) tuple_61)))) Measure)) RetryAgreed))
(assert (set.all (lambda ((tuple_70 (Tuple Int))) (set.some (lambda ((tuple_71 (Tuple Int Bool Int Bool Int))) (and (and (=> (and true (and (not (= ((_ tuple.select 4) tuple_71) 3)) true)) (set.some (lambda ((tuple_72 (Tuple Int))) (>= ((_ tuple.select 0) tuple_72) ((_ tuple.select 0) tuple_70))) DressingStarted)) (=> (and (= ((_ tuple.select 4) tuple_71) 3) true) (=> true (or (set.some (lambda ((tuple_74 (Tuple Int Bool Int Bool Int))) (and (set.some (lambda ((tuple_75 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_75) (+ ((_ tuple.select 0) tuple_74) 0)) (<= ((_ tuple.select 0) tuple_75) (+ ((_ tuple.select 0) tuple_74) 30)))) SupportCalled) (= (+ ((_ tuple.select 0) tuple_71) 30) ((_ tuple.select 0) tuple_74)))) Measure) (set.some (lambda ((tuple_73 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_73) (+ ((_ tuple.select 0) tuple_70) 0)) (<= ((_ tuple.select 0) tuple_73) (+ ((_ tuple.select 0) tuple_70) 30)))) DressingStarted))))) (= ((_ tuple.select 0) tuple_70) ((_ tuple.select 0) tuple_71)))) Measure)) RetryAgreed))
(assert (set.all (lambda ((tuple_86 (Tuple Int))) (set.some (lambda ((tuple_87 (Tuple Int Bool Int Bool Int))) (and (or (set.some (lambda ((tuple_89 (Tuple Int))) (>= ((_ tuple.select 0) tuple_89) ((_ tuple.select 0) tuple_86))) DressingAbandoned) (set.some (lambda ((tuple_88 (Tuple Int))) (>= ((_ tuple.select 0) tuple_88) ((_ tuple.select 0) tuple_86))) DressingComplete)) (= ((_ tuple.select 0) tuple_86) ((_ tuple.select 0) tuple_87)))) Measure)) RetryAgreed))
(assert (set.all (lambda ((tuple_98 (Tuple Int))) (set.some (lambda ((tuple_99 (Tuple Int Bool Int Bool Int))) (and (and (=> (and true (and (not ((_ tuple.select 1) tuple_99)) (and (not (> ((_ tuple.select 4) tuple_99) 2)) true))) (set.some (lambda ((tuple_100 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_100) (+ ((_ tuple.select 0) tuple_98) 0)) (<= ((_ tuple.select 0) tuple_100) (+ ((_ tuple.select 0) tuple_98) 60)))) CurtainsOpened)) (and (=> (and ((_ tuple.select 1) tuple_99) (and (not (> ((_ tuple.select 4) tuple_99) 2)) true)) (set.some (lambda ((tuple_101 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_101) (+ ((_ tuple.select 0) tuple_98) 0)) (<= ((_ tuple.select 0) tuple_101) (+ ((_ tuple.select 0) tuple_98) 30)))) RefuseRequest)) (=> (and (> ((_ tuple.select 4) tuple_99) 2) true) (set.some (lambda ((tuple_102 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_102) (+ ((_ tuple.select 0) tuple_98) 0)) (<= ((_ tuple.select 0) tuple_102) (+ ((_ tuple.select 0) tuple_98) 60)))) CurtainsOpened)))) (= ((_ tuple.select 0) tuple_98) ((_ tuple.select 0) tuple_99)))) Measure)) CurtainOpenRqt))
(assert (set.all (lambda ((tuple_112 (Tuple Int))) (set.some (lambda ((tuple_113 (Tuple Int Bool Int Bool Int))) (and (and (=> (and true (and (not (not ((_ tuple.select 3) tuple_113))) true)) (set.some (lambda ((tuple_114 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_114) (+ ((_ tuple.select 0) tuple_112) 0)) (<= ((_ tuple.select 0) tuple_114) (+ ((_ tuple.select 0) tuple_112) 0)))) SupportCalled)) (=> (and (not ((_ tuple.select 3) tuple_113)) true) true)) (= ((_ tuple.select 0) tuple_112) ((_ tuple.select 0) tuple_113)))) Measure)) UserFallen))
(assert (set.all (lambda ((tuple_122 (Tuple Int))) (set.some (lambda ((tuple_123 (Tuple Int Bool Int Bool Int))) (and (=> true (or (set.some (lambda ((tuple_125 (Tuple Int Bool Int Bool Int))) (and (and (=> (and true (and (not (not ((_ tuple.select 3) tuple_125))) true)) (set.some (lambda ((tuple_126 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_126) (+ ((_ tuple.select 0) tuple_125) 0)) (<= ((_ tuple.select 0) tuple_126) (+ ((_ tuple.select 0) tuple_125) 0)))) SupportCalled)) (=> (and (not ((_ tuple.select 3) tuple_125)) true) true)) (= (+ ((_ tuple.select 0) tuple_123) 1800) ((_ tuple.select 0) tuple_125)))) Measure) (set.some (lambda ((tuple_124 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_124) (+ ((_ tuple.select 0) tuple_122) 0)) (<= ((_ tuple.select 0) tuple_124) (+ ((_ tuple.select 0) tuple_122) 1800)))) RetryAgreed))) (= ((_ tuple.select 0) tuple_122) ((_ tuple.select 0) tuple_123)))) Measure)) DressingAbandoned))
(assert (set.all (lambda ((tuple_136 (Tuple Int))) (set.some (lambda ((tuple_137 (Tuple Int Bool Int Bool Int))) (and (or (or (set.some (lambda ((tuple_139 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_139) (+ ((_ tuple.select 0) tuple_136) 0)) (<= ((_ tuple.select 0) tuple_139) (+ ((_ tuple.select 0) tuple_136) 60)))) DressingComplete) (set.some (lambda ((tuple_138 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_138) (+ ((_ tuple.select 0) tuple_136) 0)) (<= ((_ tuple.select 0) tuple_138) (+ ((_ tuple.select 0) tuple_136) 120)))) DressingAbandoned)) (not (or ((_ tuple.select 1) tuple_137) (< ((_ tuple.select 2) tuple_137) 16)))) (= ((_ tuple.select 0) tuple_136) ((_ tuple.select 0) tuple_137)))) Measure)) DressingStarted))
(assert (set.all (lambda ((tuple_151 (Tuple Int))) (set.some (lambda ((tuple_152 (Tuple Int Bool Int Bool Int))) (and (or (set.some (lambda ((tuple_154 (Tuple Int Int))) (and (= ((_ tuple.select 1) tuple_154) (+ ((_ tuple.select 0) tuple_151) 120)) (= ((_ tuple.select 0) tuple_154) (+ ((_ tuple.select 0) tuple_151) 0)))) not_SupportCalled) (not ((_ tuple.select 3) tuple_152))) (= ((_ tuple.select 0) tuple_151) ((_ tuple.select 0) tuple_152)))) Measure)) UserFallen))
(assert (and (and (forall ((RetryAgreed_time_Int_24 Int) (not_RetryAgreed_start_time_Int_25 Int) (not_RetryAgreed_end_time_Int_26 Int)) (=> (and (set.member (tuple not_RetryAgreed_start_time_Int_25 not_RetryAgreed_end_time_Int_26) not_RetryAgreed) (set.member (tuple RetryAgreed_time_Int_24) RetryAgreed)) (not (and (<= RetryAgreed_time_Int_24 not_RetryAgreed_end_time_Int_26) (<= not_RetryAgreed_start_time_Int_25 RetryAgreed_time_Int_24))))) (and (forall ((SupportCalled_time_Int_21 Int) (not_SupportCalled_start_time_Int_22 Int) (not_SupportCalled_end_time_Int_23 Int)) (=> (and (set.member (tuple not_SupportCalled_start_time_Int_22 not_SupportCalled_end_time_Int_23) not_SupportCalled) (set.member (tuple SupportCalled_time_Int_21) SupportCalled)) (not (and (<= SupportCalled_time_Int_21 not_SupportCalled_end_time_Int_23) (<= not_SupportCalled_start_time_Int_22 SupportCalled_time_Int_21))))) (and (forall ((UserFallen_time_Int_18 Int) (not_UserFallen_start_time_Int_19 Int) (not_UserFallen_end_time_Int_20 Int)) (=> (and (set.member (tuple not_UserFallen_start_time_Int_19 not_UserFallen_end_time_Int_20) not_UserFallen) (set.member (tuple UserFallen_time_Int_18) UserFallen)) (not (and (<= UserFallen_time_Int_18 not_UserFallen_end_time_Int_20) (<= not_UserFallen_start_time_Int_19 UserFallen_time_Int_18))))) (and (forall ((RefuseRequest_time_Int_15 Int) (not_RefuseRequest_start_time_Int_16 Int) (not_RefuseRequest_end_time_Int_17 Int)) (=> (and (set.member (tuple not_RefuseRequest_start_time_Int_16 not_RefuseRequest_end_time_Int_17) not_RefuseRequest) (set.member (tuple RefuseRequest_time_Int_15) RefuseRequest)) (not (and (<= RefuseRequest_time_Int_15 not_RefuseRequest_end_time_Int_17) (<= not_RefuseRequest_start_time_Int_16 RefuseRequest_time_Int_15))))) (and (forall ((CurtainsOpened_time_Int_12 Int) (not_CurtainsOpened_start_time_Int_13 Int) (not_CurtainsOpened_end_time_Int_14 Int)) (=> (and (set.member (tuple not_CurtainsOpened_start_time_Int_13 not_CurtainsOpened_end_time_Int_14) not_CurtainsOpened) (set.member (tuple CurtainsOpened_time_Int_12) CurtainsOpened)) (not (and (<= CurtainsOpened_time_Int_12 not_CurtainsOpened_end_time_Int_14) (<= not_CurtainsOpened_start_time_Int_13 CurtainsOpened_time_Int_12))))) (and (forall ((CurtainOpenRqt_time_Int_9 Int) (not_CurtainOpenRqt_start_time_Int_10 Int) (not_CurtainOpenRqt_end_time_Int_11 Int)) (=> (and (set.member (tuple not_CurtainOpenRqt_start_time_Int_10 not_CurtainOpenRqt_end_time_Int_11) not_CurtainOpenRqt) (set.member (tuple CurtainOpenRqt_time_Int_9) CurtainOpenRqt)) (not (and (<= CurtainOpenRqt_time_Int_9 not_CurtainOpenRqt_end_time_Int_11) (<= not_CurtainOpenRqt_start_time_Int_10 CurtainOpenRqt_time_Int_9))))) (and (forall ((DressingAbandoned_time_Int_6 Int) (not_DressingAbandoned_start_time_Int_7 Int) (not_DressingAbandoned_end_time_Int_8 Int)) (=> (and (set.member (tuple not_DressingAbandoned_start_time_Int_7 not_DressingAbandoned_end_time_Int_8) not_DressingAbandoned) (set.member (tuple DressingAbandoned_time_Int_6) DressingAbandoned)) (not (and (<= DressingAbandoned_time_Int_6 not_DressingAbandoned_end_time_Int_8) (<= not_DressingAbandoned_start_time_Int_7 DressingAbandoned_time_Int_6))))) (and (forall ((DressingComplete_time_Int_3 Int) (not_DressingComplete_start_time_Int_4 Int) (not_DressingComplete_end_time_Int_5 Int)) (=> (and (set.member (tuple not_DressingComplete_start_time_Int_4 not_DressingComplete_end_time_Int_5) not_DressingComplete) (set.member (tuple DressingComplete_time_Int_3) DressingComplete)) (not (and (<= DressingComplete_time_Int_3 not_DressingComplete_end_time_Int_5) (<= not_DressingComplete_start_time_Int_4 DressingComplete_time_Int_3))))) (forall ((DressingStarted_time_Int_0 Int) (not_DressingStarted_start_time_Int_1 Int) (not_DressingStarted_end_time_Int_2 Int)) (=> (and (set.member (tuple not_DressingStarted_start_time_Int_1 not_DressingStarted_end_time_Int_2) not_DressingStarted) (set.member (tuple DressingStarted_time_Int_0) DressingStarted)) (not (and (<= DressingStarted_time_Int_0 not_DressingStarted_end_time_Int_2) (<= not_DressingStarted_start_time_Int_1 DressingStarted_time_Int_0))))))))))))) (set.all (lambda ((tuple_215 (Tuple Int Bool Int Bool Int Int Bool Int Bool Int))) (=> (= ((_ tuple.select 0) tuple_215) ((_ tuple.select 5) tuple_215)) (and (= ((_ tuple.select 4) tuple_215) ((_ tuple.select 9) tuple_215)) (and (= ((_ tuple.select 3) tuple_215) ((_ tuple.select 8) tuple_215)) (and (= ((_ tuple.select 2) tuple_215) ((_ tuple.select 7) tuple_215)) (and (= ((_ tuple.select 1) tuple_215) ((_ tuple.select 6) tuple_215)) (= ((_ tuple.select 0) tuple_215) ((_ tuple.select 5) tuple_215)))))))) (rel.product Measure Measure))))
(assert (=> (set.some (lambda ((tuple_170 (Tuple Int))) true) DressingStarted) (and (set.some (lambda ((tuple_173 (Tuple Int))) (set.all (lambda ((tuple_174 (Tuple Int))) (<= ((_ tuple.select 0) tuple_174) ((_ tuple.select 0) tuple_173))) DressingStarted)) DressingStarted) (set.some (lambda ((tuple_171 (Tuple Int))) (set.all (lambda ((tuple_172 (Tuple Int))) (>= ((_ tuple.select 0) tuple_172) ((_ tuple.select 0) tuple_171))) DressingStarted)) DressingStarted))))
(assert (=> (set.some (lambda ((tuple_175 (Tuple Int))) true) DressingComplete) (and (set.some (lambda ((tuple_178 (Tuple Int))) (set.all (lambda ((tuple_179 (Tuple Int))) (<= ((_ tuple.select 0) tuple_179) ((_ tuple.select 0) tuple_178))) DressingComplete)) DressingComplete) (set.some (lambda ((tuple_176 (Tuple Int))) (set.all (lambda ((tuple_177 (Tuple Int))) (>= ((_ tuple.select 0) tuple_177) ((_ tuple.select 0) tuple_176))) DressingComplete)) DressingComplete))))
(assert (=> (set.some (lambda ((tuple_180 (Tuple Int))) true) DressingAbandoned) (and (set.some (lambda ((tuple_183 (Tuple Int))) (set.all (lambda ((tuple_184 (Tuple Int))) (<= ((_ tuple.select 0) tuple_184) ((_ tuple.select 0) tuple_183))) DressingAbandoned)) DressingAbandoned) (set.some (lambda ((tuple_181 (Tuple Int))) (set.all (lambda ((tuple_182 (Tuple Int))) (>= ((_ tuple.select 0) tuple_182) ((_ tuple.select 0) tuple_181))) DressingAbandoned)) DressingAbandoned))))
(assert (=> (set.some (lambda ((tuple_185 (Tuple Int))) true) CurtainOpenRqt) (and (set.some (lambda ((tuple_188 (Tuple Int))) (set.all (lambda ((tuple_189 (Tuple Int))) (<= ((_ tuple.select 0) tuple_189) ((_ tuple.select 0) tuple_188))) CurtainOpenRqt)) CurtainOpenRqt) (set.some (lambda ((tuple_186 (Tuple Int))) (set.all (lambda ((tuple_187 (Tuple Int))) (>= ((_ tuple.select 0) tuple_187) ((_ tuple.select 0) tuple_186))) CurtainOpenRqt)) CurtainOpenRqt))))
(assert (=> (set.some (lambda ((tuple_190 (Tuple Int))) true) CurtainsOpened) (and (set.some (lambda ((tuple_193 (Tuple Int))) (set.all (lambda ((tuple_194 (Tuple Int))) (<= ((_ tuple.select 0) tuple_194) ((_ tuple.select 0) tuple_193))) CurtainsOpened)) CurtainsOpened) (set.some (lambda ((tuple_191 (Tuple Int))) (set.all (lambda ((tuple_192 (Tuple Int))) (>= ((_ tuple.select 0) tuple_192) ((_ tuple.select 0) tuple_191))) CurtainsOpened)) CurtainsOpened))))
(assert (=> (set.some (lambda ((tuple_195 (Tuple Int))) true) RefuseRequest) (and (set.some (lambda ((tuple_198 (Tuple Int))) (set.all (lambda ((tuple_199 (Tuple Int))) (<= ((_ tuple.select 0) tuple_199) ((_ tuple.select 0) tuple_198))) RefuseRequest)) RefuseRequest) (set.some (lambda ((tuple_196 (Tuple Int))) (set.all (lambda ((tuple_197 (Tuple Int))) (>= ((_ tuple.select 0) tuple_197) ((_ tuple.select 0) tuple_196))) RefuseRequest)) RefuseRequest))))
(assert (=> (set.some (lambda ((tuple_200 (Tuple Int))) true) UserFallen) (and (set.some (lambda ((tuple_203 (Tuple Int))) (set.all (lambda ((tuple_204 (Tuple Int))) (<= ((_ tuple.select 0) tuple_204) ((_ tuple.select 0) tuple_203))) UserFallen)) UserFallen) (set.some (lambda ((tuple_201 (Tuple Int))) (set.all (lambda ((tuple_202 (Tuple Int))) (>= ((_ tuple.select 0) tuple_202) ((_ tuple.select 0) tuple_201))) UserFallen)) UserFallen))))
(assert (=> (set.some (lambda ((tuple_205 (Tuple Int))) true) SupportCalled) (and (set.some (lambda ((tuple_208 (Tuple Int))) (set.all (lambda ((tuple_209 (Tuple Int))) (<= ((_ tuple.select 0) tuple_209) ((_ tuple.select 0) tuple_208))) SupportCalled)) SupportCalled) (set.some (lambda ((tuple_206 (Tuple Int))) (set.all (lambda ((tuple_207 (Tuple Int))) (>= ((_ tuple.select 0) tuple_207) ((_ tuple.select 0) tuple_206))) SupportCalled)) SupportCalled))))
(assert (=> (set.some (lambda ((tuple_210 (Tuple Int))) true) RetryAgreed) (and (set.some (lambda ((tuple_213 (Tuple Int))) (set.all (lambda ((tuple_214 (Tuple Int))) (<= ((_ tuple.select 0) tuple_214) ((_ tuple.select 0) tuple_213))) RetryAgreed)) RetryAgreed) (set.some (lambda ((tuple_211 (Tuple Int))) (set.all (lambda ((tuple_212 (Tuple Int))) (>= ((_ tuple.select 0) tuple_212) ((_ tuple.select 0) tuple_211))) RetryAgreed)) RetryAgreed))))
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
(assert true)
(assert true)
(assert (set.all (lambda ((tuple_216 (Tuple Int Bool Int Bool Int))) (set.some (lambda ((tuple_217 (Tuple Int))) (= ((_ tuple.select 0) tuple_217) ((_ tuple.select 0) tuple_216))) time)) Measure))
(check-sat)
(get-model)
