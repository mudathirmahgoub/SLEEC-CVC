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
(assert (not (= (as set.empty (Set (Tuple Int Int Bool Int Bool))) (set.filter (lambda ((tuple_217 (Tuple Int Int Bool Int Bool))) (and ((_ tuple.select 2) tuple_217) (= ((_ tuple.select 0) tuple_217) ((_ tuple.select 1) tuple_217)))) (rel.product E Measure)))))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_2 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_3 (Tuple Int Bool Int Bool))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_4 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_4) (+ ((_ tuple.select 0) tuple_2) 0)) (<= ((_ tuple.select 0) tuple_4) (+ ((_ tuple.select 0) tuple_2) 0)))) B))) (= ((_ tuple.select 0) tuple_2) ((_ tuple.select 0) tuple_3)))) Measure))))) A)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_12 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_13 (Tuple Int Bool Int Bool))) (and (or (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_14 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_14) (+ ((_ tuple.select 0) tuple_12) 0)) (<= ((_ tuple.select 0) tuple_14) (+ ((_ tuple.select 0) tuple_12) 0)))) B))) (not ((_ tuple.select 1) tuple_13))) (= ((_ tuple.select 0) tuple_12) ((_ tuple.select 0) tuple_13)))) Measure))))) A)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_25 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_26 (Tuple Int Bool Int Bool))) (and (and (=> (and true (and (not ((_ tuple.select 1) tuple_26)) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_27 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_27) (+ ((_ tuple.select 0) tuple_25) 0)) (<= ((_ tuple.select 0) tuple_27) (+ ((_ tuple.select 0) tuple_25) 0)))) B)))) (=> (and ((_ tuple.select 1) tuple_26) true) true)) (= ((_ tuple.select 0) tuple_25) ((_ tuple.select 0) tuple_26)))) Measure))))) A)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_35 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_36 (Tuple Int Bool Int Bool))) (and (or (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_37 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_37) (+ ((_ tuple.select 0) tuple_35) 0)) (<= ((_ tuple.select 0) tuple_37) (+ ((_ tuple.select 0) tuple_35) 0)))) C))) (not (> ((_ tuple.select 2) tuple_36) 50))) (= ((_ tuple.select 0) tuple_35) ((_ tuple.select 0) tuple_36)))) Measure))))) B)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_48 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_49 (Tuple Int Bool Int Bool))) (and (or (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_50 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_50) (+ ((_ tuple.select 0) tuple_48) 0)) (<= ((_ tuple.select 0) tuple_50) (+ ((_ tuple.select 0) tuple_48) 0)))) C))) (not (> ((_ tuple.select 2) tuple_49) 100))) (= ((_ tuple.select 0) tuple_48) ((_ tuple.select 0) tuple_49)))) Measure))))) B)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_61 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_62 (Tuple Int Bool Int Bool))) (and (or (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_63 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_63) (+ ((_ tuple.select 0) tuple_61) 0)) (<= ((_ tuple.select 0) tuple_63) (+ ((_ tuple.select 0) tuple_61) 0)))) C))) (not (> ((_ tuple.select 2) tuple_62) 50))) (= ((_ tuple.select 0) tuple_61) ((_ tuple.select 0) tuple_62)))) Measure))))) A)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_74 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_75 (Tuple Int Bool Int Bool))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_76 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_76) (+ ((_ tuple.select 0) tuple_74) 0)) (<= ((_ tuple.select 0) tuple_76) (+ ((_ tuple.select 0) tuple_74) 300)))) D))) (= ((_ tuple.select 0) tuple_74) ((_ tuple.select 0) tuple_75)))) Measure))))) C)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_84 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_85 (Tuple Int Bool Int Bool))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_86 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_86) (+ ((_ tuple.select 0) tuple_84) 0)) (<= ((_ tuple.select 0) tuple_86) (+ ((_ tuple.select 0) tuple_84) 301)))) D))) (= ((_ tuple.select 0) tuple_84) ((_ tuple.select 0) tuple_85)))) Measure))))) C)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_94 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_95 (Tuple Int Bool Int Bool))) (and (=> true (or (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_97 (Tuple Int Bool Int Bool))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_98 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_98) (+ ((_ tuple.select 0) tuple_97) 0)) (<= ((_ tuple.select 0) tuple_98) (+ ((_ tuple.select 0) tuple_97) 51)))) D))) (= (+ ((_ tuple.select 0) tuple_95) 250) ((_ tuple.select 0) tuple_97)))) Measure))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_96 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_96) (+ ((_ tuple.select 0) tuple_94) 0)) (<= ((_ tuple.select 0) tuple_96) (+ ((_ tuple.select 0) tuple_94) 250)))) D))))) (= ((_ tuple.select 0) tuple_94) ((_ tuple.select 0) tuple_95)))) Measure))))) C)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_108 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_109 (Tuple Int Bool Int Bool))) (and (=> true (or (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_111 (Tuple Int Bool Int Bool))) (and (=> true (or (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_113 (Tuple Int Bool Int Bool))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_114 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_114) (+ ((_ tuple.select 0) tuple_113) 0)) (<= ((_ tuple.select 0) tuple_114) (+ ((_ tuple.select 0) tuple_113) 10)))) D))) (= (+ ((_ tuple.select 0) tuple_111) 40) ((_ tuple.select 0) tuple_113)))) Measure))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_112 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_112) (+ ((_ tuple.select 0) tuple_111) 0)) (<= ((_ tuple.select 0) tuple_112) (+ ((_ tuple.select 0) tuple_111) 40)))) D))))) (= (+ ((_ tuple.select 0) tuple_109) 250) ((_ tuple.select 0) tuple_111)))) Measure))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_110 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_110) (+ ((_ tuple.select 0) tuple_108) 0)) (<= ((_ tuple.select 0) tuple_110) (+ ((_ tuple.select 0) tuple_108) 250)))) D))))) (= ((_ tuple.select 0) tuple_108) ((_ tuple.select 0) tuple_109)))) Measure))))) C)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_126 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_127 (Tuple Int Bool Int Bool))) (and (=> true (or (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_129 (Tuple Int Bool Int Bool))) (and (=> true (or (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_131 (Tuple Int Bool Int Bool))) (and (and (=> (and true (and (not ((_ tuple.select 1) tuple_131)) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_132 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_132) (+ ((_ tuple.select 0) tuple_131) 0)) (<= ((_ tuple.select 0) tuple_132) (+ ((_ tuple.select 0) tuple_131) 10)))) D)))) (=> (and ((_ tuple.select 1) tuple_131) true) true)) (= (+ ((_ tuple.select 0) tuple_129) 40) ((_ tuple.select 0) tuple_131)))) Measure))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_130 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_130) (+ ((_ tuple.select 0) tuple_129) 0)) (<= ((_ tuple.select 0) tuple_130) (+ ((_ tuple.select 0) tuple_129) 40)))) D))))) (= (+ ((_ tuple.select 0) tuple_127) 250) ((_ tuple.select 0) tuple_129)))) Measure))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_128 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_128) (+ ((_ tuple.select 0) tuple_126) 0)) (<= ((_ tuple.select 0) tuple_128) (+ ((_ tuple.select 0) tuple_126) 250)))) D))))) (= ((_ tuple.select 0) tuple_126) ((_ tuple.select 0) tuple_127)))) Measure))))) C)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_144 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_145 (Tuple Int Bool Int Bool))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_146 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_146) (+ ((_ tuple.select 0) tuple_144) 0)) (<= ((_ tuple.select 0) tuple_146) (+ ((_ tuple.select 0) tuple_144) 250)))) E))) (= ((_ tuple.select 0) tuple_144) ((_ tuple.select 0) tuple_145)))) Measure))))) C)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_154 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_155 (Tuple Int Bool Int Bool))) (and (=> true (or (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_157 (Tuple Int Bool Int Bool))) (and (=> true (or (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_159 (Tuple Int Bool Int Bool))) (and (=> true (or (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_161 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_161) (+ ((_ tuple.select 0) tuple_159) 0)) (<= ((_ tuple.select 0) tuple_161) (+ ((_ tuple.select 0) tuple_159) 10)))) D))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_160 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_160) (+ ((_ tuple.select 0) tuple_159) 0)) (<= ((_ tuple.select 0) tuple_160) (+ ((_ tuple.select 0) tuple_159) 0)))) E))))) (= (+ ((_ tuple.select 0) tuple_157) 40) ((_ tuple.select 0) tuple_159)))) Measure))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_158 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_158) (+ ((_ tuple.select 0) tuple_157) 0)) (<= ((_ tuple.select 0) tuple_158) (+ ((_ tuple.select 0) tuple_157) 40)))) D))))) (= (+ ((_ tuple.select 0) tuple_155) 250) ((_ tuple.select 0) tuple_157)))) Measure))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_156 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_156) (+ ((_ tuple.select 0) tuple_154) 0)) (<= ((_ tuple.select 0) tuple_156) (+ ((_ tuple.select 0) tuple_154) 250)))) D))))) (= ((_ tuple.select 0) tuple_154) ((_ tuple.select 0) tuple_155)))) Measure))))) C)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_174 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_175 (Tuple Int Bool Int Bool))) (and (and (=> (and true (and (not ((_ tuple.select 1) tuple_175)) (and (not (> ((_ tuple.select 2) tuple_175) 2)) true))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_176 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_176) (+ ((_ tuple.select 0) tuple_174) 0)) (<= ((_ tuple.select 0) tuple_176) (+ ((_ tuple.select 0) tuple_174) 5)))) F)))) (and (=> (and ((_ tuple.select 1) tuple_175) (and (not (> ((_ tuple.select 2) tuple_175) 2)) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_177 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_177) (+ ((_ tuple.select 0) tuple_174) 0)) (<= ((_ tuple.select 0) tuple_177) (+ ((_ tuple.select 0) tuple_174) 10)))) G)))) (=> (and (> ((_ tuple.select 2) tuple_175) 2) true) (not (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_179 (Tuple Int Int))) (and (= ((_ tuple.select 1) tuple_179) (+ ((_ tuple.select 0) tuple_174) 20)) (= ((_ tuple.select 0) tuple_179) (+ ((_ tuple.select 0) tuple_174) 0)))) not_G)))))) (= ((_ tuple.select 0) tuple_174) ((_ tuple.select 0) tuple_175)))) Measure))))) E)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_190 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_191 (Tuple Int Bool Int Bool))) (and (or (and (=> (and true (and (not (> ((_ tuple.select 2) tuple_191) 2)) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_192 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_192) (+ ((_ tuple.select 0) tuple_190) 0)) (<= ((_ tuple.select 0) tuple_192) (+ ((_ tuple.select 0) tuple_190) 10)))) G)))) (=> (and (> ((_ tuple.select 2) tuple_191) 2) true) (not (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_194 (Tuple Int Int))) (and (= ((_ tuple.select 1) tuple_194) (+ ((_ tuple.select 0) tuple_190) 10)) (= ((_ tuple.select 0) tuple_194) (+ ((_ tuple.select 0) tuple_190) 0)))) not_G))))) (not ((_ tuple.select 1) tuple_191))) (= ((_ tuple.select 0) tuple_190) ((_ tuple.select 0) tuple_191)))) Measure))))) E)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_207 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_208 (Tuple Int Bool Int Bool))) (and (or (and (=> (and true (and (not (> ((_ tuple.select 2) tuple_208) 3)) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_209 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_209) (+ ((_ tuple.select 0) tuple_207) 0)) (<= ((_ tuple.select 0) tuple_209) (+ ((_ tuple.select 0) tuple_207) 10)))) G)))) (=> (and (> ((_ tuple.select 2) tuple_208) 3) true) (not (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_211 (Tuple Int Int))) (and (= ((_ tuple.select 1) tuple_211) (+ ((_ tuple.select 0) tuple_207) 10)) (= ((_ tuple.select 0) tuple_211) (+ ((_ tuple.select 0) tuple_207) 0)))) not_G))))) (not ((_ tuple.select 1) tuple_208))) (= ((_ tuple.select 0) tuple_207) ((_ tuple.select 0) tuple_208)))) Measure))))) E)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_224 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_225 (Tuple Int Bool Int Bool))) (and (or (and (=> (and true (and (not (> ((_ tuple.select 2) tuple_225) 1)) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_226 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_226) (+ ((_ tuple.select 0) tuple_224) 0)) (<= ((_ tuple.select 0) tuple_226) (+ ((_ tuple.select 0) tuple_224) 10)))) G)))) (=> (and (> ((_ tuple.select 2) tuple_225) 1) true) (not (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_228 (Tuple Int Int))) (and (= ((_ tuple.select 1) tuple_228) (+ ((_ tuple.select 0) tuple_224) 10)) (= ((_ tuple.select 0) tuple_228) (+ ((_ tuple.select 0) tuple_224) 0)))) not_G))))) (not ((_ tuple.select 1) tuple_225))) (= ((_ tuple.select 0) tuple_224) ((_ tuple.select 0) tuple_225)))) Measure))))) E)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_241 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_242 (Tuple Int Bool Int Bool))) (and (and (=> (and true (and (not ((_ tuple.select 3) tuple_242)) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_243 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_243) (+ ((_ tuple.select 0) tuple_241) 0)) (<= ((_ tuple.select 0) tuple_243) (+ ((_ tuple.select 0) tuple_241) 5)))) G)))) (=> (and ((_ tuple.select 3) tuple_242) true) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_244 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_244) (+ ((_ tuple.select 0) tuple_241) 0)) (<= ((_ tuple.select 0) tuple_244) (+ ((_ tuple.select 0) tuple_241) 10)))) H))))) (= ((_ tuple.select 0) tuple_241) ((_ tuple.select 0) tuple_242)))) Measure))))) F)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_253 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_254 (Tuple Int Bool Int Bool))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_255 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_255) (+ ((_ tuple.select 0) tuple_253) 0)) (<= ((_ tuple.select 0) tuple_255) (+ ((_ tuple.select 0) tuple_253) 10)))) F))) (= ((_ tuple.select 0) tuple_253) ((_ tuple.select 0) tuple_254)))) Measure))))) H)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_263 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_264 (Tuple Int Bool Int Bool))) (and (not (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_266 (Tuple Int Int))) (and (= ((_ tuple.select 1) tuple_266) (+ ((_ tuple.select 0) tuple_263) 0)) (= ((_ tuple.select 0) tuple_266) (+ ((_ tuple.select 0) tuple_263) 0)))) not_F))) (= ((_ tuple.select 0) tuple_263) ((_ tuple.select 0) tuple_264)))) Measure))))) H)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_275 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_276 (Tuple Int Bool Int Bool))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_277 (Tuple Int))) (>= ((_ tuple.select 0) tuple_277) ((_ tuple.select 0) tuple_275))) G))) (= ((_ tuple.select 0) tuple_275) ((_ tuple.select 0) tuple_276)))) Measure))))) F)))
(assert (and (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_333 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_333) ((_ tuple.select 2) tuple_333)) (<= ((_ tuple.select 1) tuple_333) ((_ tuple.select 0) tuple_333)))))) (rel.product H not_H))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_332 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_332) ((_ tuple.select 2) tuple_332)) (<= ((_ tuple.select 1) tuple_332) ((_ tuple.select 0) tuple_332)))))) (rel.product G not_G))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_331 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_331) ((_ tuple.select 2) tuple_331)) (<= ((_ tuple.select 1) tuple_331) ((_ tuple.select 0) tuple_331)))))) (rel.product F not_F))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_330 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_330) ((_ tuple.select 2) tuple_330)) (<= ((_ tuple.select 1) tuple_330) ((_ tuple.select 0) tuple_330)))))) (rel.product E not_E))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_329 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_329) ((_ tuple.select 2) tuple_329)) (<= ((_ tuple.select 1) tuple_329) ((_ tuple.select 0) tuple_329)))))) (rel.product D not_D))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_328 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_328) ((_ tuple.select 2) tuple_328)) (<= ((_ tuple.select 1) tuple_328) ((_ tuple.select 0) tuple_328)))))) (rel.product C not_C))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_327 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_327) ((_ tuple.select 2) tuple_327)) (<= ((_ tuple.select 1) tuple_327) ((_ tuple.select 0) tuple_327)))))) (rel.product B not_B))) (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_326 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_326) ((_ tuple.select 2) tuple_326)) (<= ((_ tuple.select 1) tuple_326) ((_ tuple.select 0) tuple_326)))))) (rel.product A not_A)))))))))) (= (as set.empty (Set (Tuple Int Bool Int Bool Int Bool Int Bool))) (set.filter (lambda ((tuple_325 (Tuple Int Bool Int Bool Int Bool Int Bool))) (not (=> (= ((_ tuple.select 0) tuple_325) ((_ tuple.select 4) tuple_325)) (and (= ((_ tuple.select 3) tuple_325) ((_ tuple.select 7) tuple_325)) (and (= ((_ tuple.select 2) tuple_325) ((_ tuple.select 6) tuple_325)) (and (= ((_ tuple.select 1) tuple_325) ((_ tuple.select 5) tuple_325)) (= ((_ tuple.select 0) tuple_325) ((_ tuple.select 4) tuple_325)))))))) (rel.product Measure Measure)))))
(assert (=> (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_285 (Tuple Int))) true) A))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_288 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_289 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_289) ((_ tuple.select 0) tuple_288)))) A))) A))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_286 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_287 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_287) ((_ tuple.select 0) tuple_286)))) A))) A))))))
(assert (=> (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_290 (Tuple Int))) true) B))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_293 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_294 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_294) ((_ tuple.select 0) tuple_293)))) B))) B))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_291 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_292 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_292) ((_ tuple.select 0) tuple_291)))) B))) B))))))
(assert (=> (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_295 (Tuple Int))) true) C))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_298 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_299 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_299) ((_ tuple.select 0) tuple_298)))) C))) C))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_296 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_297 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_297) ((_ tuple.select 0) tuple_296)))) C))) C))))))
(assert (=> (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_300 (Tuple Int))) true) D))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_303 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_304 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_304) ((_ tuple.select 0) tuple_303)))) D))) D))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_301 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_302 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_302) ((_ tuple.select 0) tuple_301)))) D))) D))))))
(assert (=> (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_305 (Tuple Int))) true) E))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_308 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_309 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_309) ((_ tuple.select 0) tuple_308)))) E))) E))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_306 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_307 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_307) ((_ tuple.select 0) tuple_306)))) E))) E))))))
(assert (=> (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_310 (Tuple Int))) true) F))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_313 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_314 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_314) ((_ tuple.select 0) tuple_313)))) F))) F))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_311 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_312 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_312) ((_ tuple.select 0) tuple_311)))) F))) F))))))
(assert (=> (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_315 (Tuple Int))) true) G))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_318 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_319 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_319) ((_ tuple.select 0) tuple_318)))) G))) G))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_316 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_317 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_317) ((_ tuple.select 0) tuple_316)))) G))) G))))))
(assert (=> (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_320 (Tuple Int))) true) H))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_323 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_324 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_324) ((_ tuple.select 0) tuple_323)))) H))) H))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_321 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_322 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_322) ((_ tuple.select 0) tuple_321)))) H))) H))))))
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
(assert (= (as set.empty (Set (Tuple Int Bool Int Bool))) (set.filter (lambda ((tuple_334 (Tuple Int Bool Int Bool))) (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_335 (Tuple Int))) (= ((_ tuple.select 0) tuple_335) ((_ tuple.select 0) tuple_334))) time))))) Measure)))
(check-sat)
(get-model)
