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
(assert (not (= (as set.empty (Set (Tuple Int Int Bool Int Bool Int))) (set.filter (lambda ((tuple_132 (Tuple Int Int Bool Int Bool Int))) (= ((_ tuple.select 0) tuple_132) ((_ tuple.select 1) tuple_132))) (rel.product DressingAbandoned Measure)))))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_2 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool Int))) (set.filter (lambda ((tuple_3 (Tuple Int Bool Int Bool Int))) (and (or (and (=> (and true (and (not (< ((_ tuple.select 2) tuple_3) 19)) (and (not (< ((_ tuple.select 2) tuple_3) 17)) true))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_5 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_5) (+ ((_ tuple.select 0) tuple_2) 0)) (<= ((_ tuple.select 0) tuple_5) (+ ((_ tuple.select 0) tuple_2) 120)))) DressingComplete)))) (and (=> (and (< ((_ tuple.select 2) tuple_3) 19) (and (not (< ((_ tuple.select 2) tuple_3) 17)) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_6 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_6) (+ ((_ tuple.select 0) tuple_2) 0)) (<= ((_ tuple.select 0) tuple_6) (+ ((_ tuple.select 0) tuple_2) 90)))) DressingComplete)))) (=> (and (< ((_ tuple.select 2) tuple_3) 17) true) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_7 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_7) (+ ((_ tuple.select 0) tuple_2) 0)) (<= ((_ tuple.select 0) tuple_7) (+ ((_ tuple.select 0) tuple_2) 60)))) DressingComplete)))))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_4 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_4) (+ ((_ tuple.select 0) tuple_2) 0)) (<= ((_ tuple.select 0) tuple_4) (+ ((_ tuple.select 0) tuple_2) 120)))) DressingAbandoned)))) (= ((_ tuple.select 0) tuple_2) ((_ tuple.select 0) tuple_3)))) Measure))))) DressingStarted)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_18 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool Int))) (set.filter (lambda ((tuple_19 (Tuple Int Bool Int Bool Int))) (and (or (and (=> (and true (and (not (<= ((_ tuple.select 2) tuple_19) 22)) (and (not (and ((_ tuple.select 1) tuple_19) (<= ((_ tuple.select 2) tuple_19) 11))) true))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_21 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_21) (+ ((_ tuple.select 0) tuple_18) 0)) (<= ((_ tuple.select 0) tuple_21) (+ ((_ tuple.select 0) tuple_18) 120)))) DressingComplete)))) (and (=> (and (<= ((_ tuple.select 2) tuple_19) 22) (and (not (and ((_ tuple.select 1) tuple_19) (<= ((_ tuple.select 2) tuple_19) 11))) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_22 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_22) (+ ((_ tuple.select 0) tuple_18) 0)) (<= ((_ tuple.select 0) tuple_22) (+ ((_ tuple.select 0) tuple_18) (* (- 120 (* (- 22 ((_ tuple.select 2) tuple_19)) 15)) 1))))) DressingComplete)))) (=> (and (and ((_ tuple.select 1) tuple_19) (<= ((_ tuple.select 2) tuple_19) 11)) true) (and (=> (and true (and (not (not ((_ tuple.select 3) tuple_19))) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_23 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_23) (+ ((_ tuple.select 0) tuple_18) 0)) (<= ((_ tuple.select 0) tuple_23) (+ ((_ tuple.select 0) tuple_18) 0)))) SupportCalled)))) (=> (and (not ((_ tuple.select 3) tuple_19)) true) true))))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_20 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_20) (+ ((_ tuple.select 0) tuple_18) 0)) (<= ((_ tuple.select 0) tuple_20) (+ ((_ tuple.select 0) tuple_18) 120)))) DressingAbandoned)))) (= ((_ tuple.select 0) tuple_18) ((_ tuple.select 0) tuple_19)))) Measure))))) DressingStarted)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_34 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool Int))) (set.filter (lambda ((tuple_35 (Tuple Int Bool Int Bool Int))) (and (or (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_36 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_36) (+ ((_ tuple.select 0) tuple_34) 0)) (<= ((_ tuple.select 0) tuple_36) (+ ((_ tuple.select 0) tuple_34) 0)))) DressingAbandoned))) (not (> ((_ tuple.select 4) tuple_35) 2))) (= ((_ tuple.select 0) tuple_34) ((_ tuple.select 0) tuple_35)))) Measure))))) DressingStarted)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_47 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool Int))) (set.filter (lambda ((tuple_48 (Tuple Int Bool Int Bool Int))) (and (or (and (=> (and true (and (not (not ((_ tuple.select 3) tuple_48))) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_49 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_49) (+ ((_ tuple.select 0) tuple_47) 0)) (<= ((_ tuple.select 0) tuple_49) (+ ((_ tuple.select 0) tuple_47) 0)))) SupportCalled)))) (=> (and (not ((_ tuple.select 3) tuple_48)) true) true)) (not (> ((_ tuple.select 4) tuple_48) 2))) (= ((_ tuple.select 0) tuple_47) ((_ tuple.select 0) tuple_48)))) Measure))))) DressingStarted)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_60 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool Int))) (set.filter (lambda ((tuple_61 (Tuple Int Bool Int Bool Int))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_62 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_62) (+ ((_ tuple.select 0) tuple_60) 1)) (<= ((_ tuple.select 0) tuple_62) (+ ((_ tuple.select 0) tuple_60) 30)))) DressingStarted))) (= ((_ tuple.select 0) tuple_60) ((_ tuple.select 0) tuple_61)))) Measure))))) RetryAgreed)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_70 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool Int))) (set.filter (lambda ((tuple_71 (Tuple Int Bool Int Bool Int))) (and (and (=> (and true (and (not (= ((_ tuple.select 4) tuple_71) 3)) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_72 (Tuple Int))) (>= ((_ tuple.select 0) tuple_72) ((_ tuple.select 0) tuple_70))) DressingStarted)))) (=> (and (= ((_ tuple.select 4) tuple_71) 3) true) (=> true (or (not (= (as set.empty (Set (Tuple Int Bool Int Bool Int))) (set.filter (lambda ((tuple_74 (Tuple Int Bool Int Bool Int))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_75 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_75) (+ ((_ tuple.select 0) tuple_74) 0)) (<= ((_ tuple.select 0) tuple_75) (+ ((_ tuple.select 0) tuple_74) 30)))) SupportCalled))) (= (+ ((_ tuple.select 0) tuple_71) 30) ((_ tuple.select 0) tuple_74)))) Measure))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_73 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_73) (+ ((_ tuple.select 0) tuple_70) 0)) (<= ((_ tuple.select 0) tuple_73) (+ ((_ tuple.select 0) tuple_70) 30)))) DressingStarted))))))) (= ((_ tuple.select 0) tuple_70) ((_ tuple.select 0) tuple_71)))) Measure))))) RetryAgreed)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_86 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool Int))) (set.filter (lambda ((tuple_87 (Tuple Int Bool Int Bool Int))) (and (or (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_89 (Tuple Int))) (>= ((_ tuple.select 0) tuple_89) ((_ tuple.select 0) tuple_86))) DressingAbandoned))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_88 (Tuple Int))) (>= ((_ tuple.select 0) tuple_88) ((_ tuple.select 0) tuple_86))) DressingComplete)))) (= ((_ tuple.select 0) tuple_86) ((_ tuple.select 0) tuple_87)))) Measure))))) RetryAgreed)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_98 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool Int))) (set.filter (lambda ((tuple_99 (Tuple Int Bool Int Bool Int))) (and (and (=> (and true (and (not ((_ tuple.select 1) tuple_99)) (and (not (> ((_ tuple.select 4) tuple_99) 2)) true))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_100 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_100) (+ ((_ tuple.select 0) tuple_98) 0)) (<= ((_ tuple.select 0) tuple_100) (+ ((_ tuple.select 0) tuple_98) 60)))) CurtainsOpened)))) (and (=> (and ((_ tuple.select 1) tuple_99) (and (not (> ((_ tuple.select 4) tuple_99) 2)) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_101 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_101) (+ ((_ tuple.select 0) tuple_98) 0)) (<= ((_ tuple.select 0) tuple_101) (+ ((_ tuple.select 0) tuple_98) 30)))) RefuseRequest)))) (=> (and (> ((_ tuple.select 4) tuple_99) 2) true) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_102 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_102) (+ ((_ tuple.select 0) tuple_98) 0)) (<= ((_ tuple.select 0) tuple_102) (+ ((_ tuple.select 0) tuple_98) 60)))) CurtainsOpened)))))) (= ((_ tuple.select 0) tuple_98) ((_ tuple.select 0) tuple_99)))) Measure))))) CurtainOpenRqt)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_112 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool Int))) (set.filter (lambda ((tuple_113 (Tuple Int Bool Int Bool Int))) (and (and (=> (and true (and (not (not ((_ tuple.select 3) tuple_113))) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_114 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_114) (+ ((_ tuple.select 0) tuple_112) 0)) (<= ((_ tuple.select 0) tuple_114) (+ ((_ tuple.select 0) tuple_112) 0)))) SupportCalled)))) (=> (and (not ((_ tuple.select 3) tuple_113)) true) true)) (= ((_ tuple.select 0) tuple_112) ((_ tuple.select 0) tuple_113)))) Measure))))) UserFallen)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_122 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool Int))) (set.filter (lambda ((tuple_123 (Tuple Int Bool Int Bool Int))) (and (=> true (or (not (= (as set.empty (Set (Tuple Int Bool Int Bool Int))) (set.filter (lambda ((tuple_125 (Tuple Int Bool Int Bool Int))) (and (and (=> (and true (and (not (not ((_ tuple.select 3) tuple_125))) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_126 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_126) (+ ((_ tuple.select 0) tuple_125) 0)) (<= ((_ tuple.select 0) tuple_126) (+ ((_ tuple.select 0) tuple_125) 0)))) SupportCalled)))) (=> (and (not ((_ tuple.select 3) tuple_125)) true) true)) (= (+ ((_ tuple.select 0) tuple_123) 1800) ((_ tuple.select 0) tuple_125)))) Measure))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_124 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_124) (+ ((_ tuple.select 0) tuple_122) 0)) (<= ((_ tuple.select 0) tuple_124) (+ ((_ tuple.select 0) tuple_122) 1800)))) RetryAgreed))))) (= ((_ tuple.select 0) tuple_122) ((_ tuple.select 0) tuple_123)))) Measure))))) DressingAbandoned)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_136 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool Int))) (set.filter (lambda ((tuple_137 (Tuple Int Bool Int Bool Int))) (and (or (or (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_139 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_139) (+ ((_ tuple.select 0) tuple_136) 0)) (<= ((_ tuple.select 0) tuple_139) (+ ((_ tuple.select 0) tuple_136) 60)))) DressingComplete))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_138 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_138) (+ ((_ tuple.select 0) tuple_136) 0)) (<= ((_ tuple.select 0) tuple_138) (+ ((_ tuple.select 0) tuple_136) 120)))) DressingAbandoned)))) (not (or ((_ tuple.select 1) tuple_137) (< ((_ tuple.select 2) tuple_137) 16)))) (= ((_ tuple.select 0) tuple_136) ((_ tuple.select 0) tuple_137)))) Measure))))) DressingStarted)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_151 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool Int))) (set.filter (lambda ((tuple_152 (Tuple Int Bool Int Bool Int))) (and (or (not (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_154 (Tuple Int Int))) (and (= ((_ tuple.select 1) tuple_154) (+ ((_ tuple.select 0) tuple_151) 120)) (= ((_ tuple.select 0) tuple_154) (+ ((_ tuple.select 0) tuple_151) 0)))) not_SupportCalled))) (not ((_ tuple.select 3) tuple_152))) (= ((_ tuple.select 0) tuple_151) ((_ tuple.select 0) tuple_152)))) Measure))))) UserFallen)))
(assert (and (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_224 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_224) ((_ tuple.select 2) tuple_224)) (<= ((_ tuple.select 1) tuple_224) ((_ tuple.select 0) tuple_224)))))) (rel.product RetryAgreed not_RetryAgreed))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_223 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_223) ((_ tuple.select 2) tuple_223)) (<= ((_ tuple.select 1) tuple_223) ((_ tuple.select 0) tuple_223)))))) (rel.product SupportCalled not_SupportCalled))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_222 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_222) ((_ tuple.select 2) tuple_222)) (<= ((_ tuple.select 1) tuple_222) ((_ tuple.select 0) tuple_222)))))) (rel.product UserFallen not_UserFallen))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_221 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_221) ((_ tuple.select 2) tuple_221)) (<= ((_ tuple.select 1) tuple_221) ((_ tuple.select 0) tuple_221)))))) (rel.product RefuseRequest not_RefuseRequest))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_220 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_220) ((_ tuple.select 2) tuple_220)) (<= ((_ tuple.select 1) tuple_220) ((_ tuple.select 0) tuple_220)))))) (rel.product CurtainsOpened not_CurtainsOpened))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_219 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_219) ((_ tuple.select 2) tuple_219)) (<= ((_ tuple.select 1) tuple_219) ((_ tuple.select 0) tuple_219)))))) (rel.product CurtainOpenRqt not_CurtainOpenRqt))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_218 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_218) ((_ tuple.select 2) tuple_218)) (<= ((_ tuple.select 1) tuple_218) ((_ tuple.select 0) tuple_218)))))) (rel.product DressingAbandoned not_DressingAbandoned))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_217 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_217) ((_ tuple.select 2) tuple_217)) (<= ((_ tuple.select 1) tuple_217) ((_ tuple.select 0) tuple_217)))))) (rel.product DressingComplete not_DressingComplete))) (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_216 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_216) ((_ tuple.select 2) tuple_216)) (<= ((_ tuple.select 1) tuple_216) ((_ tuple.select 0) tuple_216)))))) (rel.product DressingStarted not_DressingStarted))))))))))) (= (as set.empty (Set (Tuple Int Bool Int Bool Int Int Bool Int Bool Int))) (set.filter (lambda ((tuple_215 (Tuple Int Bool Int Bool Int Int Bool Int Bool Int))) (not (=> (= ((_ tuple.select 0) tuple_215) ((_ tuple.select 5) tuple_215)) (and (= ((_ tuple.select 4) tuple_215) ((_ tuple.select 9) tuple_215)) (and (= ((_ tuple.select 3) tuple_215) ((_ tuple.select 8) tuple_215)) (and (= ((_ tuple.select 2) tuple_215) ((_ tuple.select 7) tuple_215)) (and (= ((_ tuple.select 1) tuple_215) ((_ tuple.select 6) tuple_215)) (= ((_ tuple.select 0) tuple_215) ((_ tuple.select 5) tuple_215))))))))) (rel.product Measure Measure)))))
(assert (=> (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_170 (Tuple Int))) true) DressingStarted))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_173 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_174 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_174) ((_ tuple.select 0) tuple_173)))) DressingStarted))) DressingStarted))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_171 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_172 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_172) ((_ tuple.select 0) tuple_171)))) DressingStarted))) DressingStarted))))))
(assert (=> (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_175 (Tuple Int))) true) DressingComplete))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_178 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_179 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_179) ((_ tuple.select 0) tuple_178)))) DressingComplete))) DressingComplete))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_176 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_177 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_177) ((_ tuple.select 0) tuple_176)))) DressingComplete))) DressingComplete))))))
(assert (=> (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_180 (Tuple Int))) true) DressingAbandoned))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_183 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_184 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_184) ((_ tuple.select 0) tuple_183)))) DressingAbandoned))) DressingAbandoned))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_181 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_182 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_182) ((_ tuple.select 0) tuple_181)))) DressingAbandoned))) DressingAbandoned))))))
(assert (=> (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_185 (Tuple Int))) true) CurtainOpenRqt))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_188 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_189 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_189) ((_ tuple.select 0) tuple_188)))) CurtainOpenRqt))) CurtainOpenRqt))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_186 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_187 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_187) ((_ tuple.select 0) tuple_186)))) CurtainOpenRqt))) CurtainOpenRqt))))))
(assert (=> (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_190 (Tuple Int))) true) CurtainsOpened))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_193 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_194 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_194) ((_ tuple.select 0) tuple_193)))) CurtainsOpened))) CurtainsOpened))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_191 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_192 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_192) ((_ tuple.select 0) tuple_191)))) CurtainsOpened))) CurtainsOpened))))))
(assert (=> (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_195 (Tuple Int))) true) RefuseRequest))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_198 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_199 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_199) ((_ tuple.select 0) tuple_198)))) RefuseRequest))) RefuseRequest))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_196 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_197 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_197) ((_ tuple.select 0) tuple_196)))) RefuseRequest))) RefuseRequest))))))
(assert (=> (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_200 (Tuple Int))) true) UserFallen))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_203 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_204 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_204) ((_ tuple.select 0) tuple_203)))) UserFallen))) UserFallen))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_201 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_202 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_202) ((_ tuple.select 0) tuple_201)))) UserFallen))) UserFallen))))))
(assert (=> (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_205 (Tuple Int))) true) SupportCalled))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_208 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_209 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_209) ((_ tuple.select 0) tuple_208)))) SupportCalled))) SupportCalled))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_206 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_207 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_207) ((_ tuple.select 0) tuple_206)))) SupportCalled))) SupportCalled))))))
(assert (=> (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_210 (Tuple Int))) true) RetryAgreed))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_213 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_214 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_214) ((_ tuple.select 0) tuple_213)))) RetryAgreed))) RetryAgreed))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_211 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_212 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_212) ((_ tuple.select 0) tuple_211)))) RetryAgreed))) RetryAgreed))))))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_1 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_1) 0))) time)))
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
(assert (= (as set.empty (Set (Tuple Int Bool Int Bool Int))) (set.filter (lambda ((tuple_225 (Tuple Int Bool Int Bool Int))) (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_226 (Tuple Int))) (= ((_ tuple.select 0) tuple_226) ((_ tuple.select 0) tuple_225))) time))))) Measure)))
(check-sat)
(get-model)
