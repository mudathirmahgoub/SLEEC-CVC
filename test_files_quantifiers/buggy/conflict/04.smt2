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
(assert (exists ((RetryAgreed_time_Int_109 Int) (Measure_time_Int_110 Int) (Measure_userUnderDressed_Bool_40 Bool) (Measure_roomTemperature_Int_111 Int) (Measure_assentToSupportCalls_Bool_41 Bool) (Measure_userDistressed_Int_112 Int)) (and (= RetryAgreed_time_Int_109 Measure_time_Int_110) (and (set.member (tuple Measure_time_Int_110 Measure_userUnderDressed_Bool_40 Measure_roomTemperature_Int_111 Measure_assentToSupportCalls_Bool_41 Measure_userDistressed_Int_112) Measure) (set.member (tuple RetryAgreed_time_Int_109) RetryAgreed)))))
(assert (forall ((DressingStarted_time_Int_1 Int)) (=> (set.member (tuple DressingStarted_time_Int_1) DressingStarted) (exists ((Measure_time_Int_2 Int) (Measure_userUnderDressed_Bool_0 Bool) (Measure_roomTemperature_Int_3 Int) (Measure_assentToSupportCalls_Bool_1 Bool) (Measure_userDistressed_Int_4 Int)) (and (and (or (and (=> (and true (and (not (< Measure_roomTemperature_Int_3 19)) (and (not (< Measure_roomTemperature_Int_3 17)) true))) (exists ((DressingComplete_time_Int_6 Int)) (and (and (>= DressingComplete_time_Int_6 (+ DressingStarted_time_Int_1 0)) (<= DressingComplete_time_Int_6 (+ DressingStarted_time_Int_1 120))) (set.member (tuple DressingComplete_time_Int_6) DressingComplete)))) (and (=> (and (< Measure_roomTemperature_Int_3 19) (and (not (< Measure_roomTemperature_Int_3 17)) true)) (exists ((DressingComplete_time_Int_7 Int)) (and (and (>= DressingComplete_time_Int_7 (+ DressingStarted_time_Int_1 0)) (<= DressingComplete_time_Int_7 (+ DressingStarted_time_Int_1 90))) (set.member (tuple DressingComplete_time_Int_7) DressingComplete)))) (=> (and (< Measure_roomTemperature_Int_3 17) true) (exists ((DressingComplete_time_Int_8 Int)) (and (and (>= DressingComplete_time_Int_8 (+ DressingStarted_time_Int_1 0)) (<= DressingComplete_time_Int_8 (+ DressingStarted_time_Int_1 60))) (set.member (tuple DressingComplete_time_Int_8) DressingComplete)))))) (exists ((DressingAbandoned_time_Int_5 Int)) (and (and (>= DressingAbandoned_time_Int_5 (+ DressingStarted_time_Int_1 0)) (<= DressingAbandoned_time_Int_5 (+ DressingStarted_time_Int_1 120))) (set.member (tuple DressingAbandoned_time_Int_5) DressingAbandoned)))) (= DressingStarted_time_Int_1 Measure_time_Int_2)) (set.member (tuple Measure_time_Int_2 Measure_userUnderDressed_Bool_0 Measure_roomTemperature_Int_3 Measure_assentToSupportCalls_Bool_1 Measure_userDistressed_Int_4) Measure))))))
(assert (forall ((DressingStarted_time_Int_24 Int)) (=> (set.member (tuple DressingStarted_time_Int_24) DressingStarted) (exists ((Measure_time_Int_25 Int) (Measure_userUnderDressed_Bool_6 Bool) (Measure_roomTemperature_Int_26 Int) (Measure_assentToSupportCalls_Bool_7 Bool) (Measure_userDistressed_Int_27 Int)) (and (and (or (and (=> (and true (and (not (<= Measure_roomTemperature_Int_26 22)) (and (not (and Measure_userUnderDressed_Bool_6 (<= Measure_roomTemperature_Int_26 11))) true))) (exists ((DressingComplete_time_Int_29 Int)) (and (and (>= DressingComplete_time_Int_29 (+ DressingStarted_time_Int_24 0)) (<= DressingComplete_time_Int_29 (+ DressingStarted_time_Int_24 120))) (set.member (tuple DressingComplete_time_Int_29) DressingComplete)))) (and (=> (and (<= Measure_roomTemperature_Int_26 22) (and (not (and Measure_userUnderDressed_Bool_6 (<= Measure_roomTemperature_Int_26 11))) true)) (exists ((DressingComplete_time_Int_30 Int)) (and (and (>= DressingComplete_time_Int_30 (+ DressingStarted_time_Int_24 0)) (<= DressingComplete_time_Int_30 (+ DressingStarted_time_Int_24 (* (- 120 (* (- 22 Measure_roomTemperature_Int_26) 15)) 1)))) (set.member (tuple DressingComplete_time_Int_30) DressingComplete)))) (=> (and (and Measure_userUnderDressed_Bool_6 (<= Measure_roomTemperature_Int_26 11)) true) (and (=> (and true (and (not (not Measure_assentToSupportCalls_Bool_7)) true)) (exists ((SupportCalled_time_Int_31 Int)) (and (and (>= SupportCalled_time_Int_31 (+ DressingStarted_time_Int_24 0)) (<= SupportCalled_time_Int_31 (+ DressingStarted_time_Int_24 0))) (set.member (tuple SupportCalled_time_Int_31) SupportCalled)))) (=> (and (not Measure_assentToSupportCalls_Bool_7) true) true))))) (exists ((DressingAbandoned_time_Int_28 Int)) (and (and (>= DressingAbandoned_time_Int_28 (+ DressingStarted_time_Int_24 0)) (<= DressingAbandoned_time_Int_28 (+ DressingStarted_time_Int_24 120))) (set.member (tuple DressingAbandoned_time_Int_28) DressingAbandoned)))) (= DressingStarted_time_Int_24 Measure_time_Int_25)) (set.member (tuple Measure_time_Int_25 Measure_userUnderDressed_Bool_6 Measure_roomTemperature_Int_26 Measure_assentToSupportCalls_Bool_7 Measure_userDistressed_Int_27) Measure))))))
(assert (forall ((DressingStarted_time_Int_47 Int)) (=> (set.member (tuple DressingStarted_time_Int_47) DressingStarted) (exists ((Measure_time_Int_48 Int) (Measure_userUnderDressed_Bool_12 Bool) (Measure_roomTemperature_Int_49 Int) (Measure_assentToSupportCalls_Bool_13 Bool) (Measure_userDistressed_Int_50 Int)) (and (and (or (exists ((DressingAbandoned_time_Int_51 Int)) (and (and (>= DressingAbandoned_time_Int_51 (+ DressingStarted_time_Int_47 0)) (<= DressingAbandoned_time_Int_51 (+ DressingStarted_time_Int_47 0))) (set.member (tuple DressingAbandoned_time_Int_51) DressingAbandoned))) (not (> Measure_userDistressed_Int_50 2))) (= DressingStarted_time_Int_47 Measure_time_Int_48)) (set.member (tuple Measure_time_Int_48 Measure_userUnderDressed_Bool_12 Measure_roomTemperature_Int_49 Measure_assentToSupportCalls_Bool_13 Measure_userDistressed_Int_50) Measure))))))
(assert (forall ((DressingStarted_time_Int_73 Int)) (=> (set.member (tuple DressingStarted_time_Int_73) DressingStarted) (exists ((Measure_time_Int_74 Int) (Measure_userUnderDressed_Bool_24 Bool) (Measure_roomTemperature_Int_75 Int) (Measure_assentToSupportCalls_Bool_25 Bool) (Measure_userDistressed_Int_76 Int)) (and (and (or (and (=> (and true (and (not (not Measure_assentToSupportCalls_Bool_25)) true)) (exists ((SupportCalled_time_Int_77 Int)) (and (and (>= SupportCalled_time_Int_77 (+ DressingStarted_time_Int_73 0)) (<= SupportCalled_time_Int_77 (+ DressingStarted_time_Int_73 0))) (set.member (tuple SupportCalled_time_Int_77) SupportCalled)))) (=> (and (not Measure_assentToSupportCalls_Bool_25) true) true)) (not (> Measure_userDistressed_Int_76 2))) (= DressingStarted_time_Int_73 Measure_time_Int_74)) (set.member (tuple Measure_time_Int_74 Measure_userUnderDressed_Bool_24 Measure_roomTemperature_Int_75 Measure_assentToSupportCalls_Bool_25 Measure_userDistressed_Int_76) Measure))))))
(assert (forall ((RetryAgreed_time_Int_99 Int)) (=> (set.member (tuple RetryAgreed_time_Int_99) RetryAgreed) (exists ((Measure_time_Int_100 Int) (Measure_userUnderDressed_Bool_36 Bool) (Measure_roomTemperature_Int_101 Int) (Measure_assentToSupportCalls_Bool_37 Bool) (Measure_userDistressed_Int_102 Int)) (and (and (exists ((DressingStarted_time_Int_103 Int)) (and (and (>= DressingStarted_time_Int_103 (+ RetryAgreed_time_Int_99 1)) (<= DressingStarted_time_Int_103 (+ RetryAgreed_time_Int_99 30))) (set.member (tuple DressingStarted_time_Int_103) DressingStarted))) (= RetryAgreed_time_Int_99 Measure_time_Int_100)) (set.member (tuple Measure_time_Int_100 Measure_userUnderDressed_Bool_36 Measure_roomTemperature_Int_101 Measure_assentToSupportCalls_Bool_37 Measure_userDistressed_Int_102) Measure))))))
(assert (forall ((RetryAgreed_time_Int_116 Int)) (=> (set.member (tuple RetryAgreed_time_Int_116) RetryAgreed) (exists ((Measure_time_Int_117 Int) (Measure_userUnderDressed_Bool_42 Bool) (Measure_roomTemperature_Int_118 Int) (Measure_assentToSupportCalls_Bool_43 Bool) (Measure_userDistressed_Int_119 Int)) (and (and (and (=> (and true (and (not (= Measure_userDistressed_Int_119 3)) true)) (exists ((DressingStarted_time_Int_120 Int)) (and (>= DressingStarted_time_Int_120 RetryAgreed_time_Int_116) (set.member (tuple DressingStarted_time_Int_120) DressingStarted)))) (=> (and (= Measure_userDistressed_Int_119 3) true) (=> true (or (exists ((Measure_time_Int_122 Int) (Measure_userUnderDressed_Bool_44 Bool) (Measure_roomTemperature_Int_123 Int) (Measure_assentToSupportCalls_Bool_45 Bool) (Measure_userDistressed_Int_124 Int)) (and (and (exists ((SupportCalled_time_Int_125 Int)) (and (and (>= SupportCalled_time_Int_125 (+ Measure_time_Int_122 0)) (<= SupportCalled_time_Int_125 (+ Measure_time_Int_122 30))) (set.member (tuple SupportCalled_time_Int_125) SupportCalled))) (= (+ Measure_time_Int_117 30) Measure_time_Int_122)) (set.member (tuple Measure_time_Int_122 Measure_userUnderDressed_Bool_44 Measure_roomTemperature_Int_123 Measure_assentToSupportCalls_Bool_45 Measure_userDistressed_Int_124) Measure))) (exists ((DressingStarted_time_Int_121 Int)) (and (and (>= DressingStarted_time_Int_121 (+ RetryAgreed_time_Int_116 0)) (<= DressingStarted_time_Int_121 (+ RetryAgreed_time_Int_116 30))) (set.member (tuple DressingStarted_time_Int_121) DressingStarted))))))) (= RetryAgreed_time_Int_116 Measure_time_Int_117)) (set.member (tuple Measure_time_Int_117 Measure_userUnderDressed_Bool_42 Measure_roomTemperature_Int_118 Measure_assentToSupportCalls_Bool_43 Measure_userDistressed_Int_119) Measure))))))
(assert (forall ((RetryAgreed_time_Int_143 Int)) (=> (set.member (tuple RetryAgreed_time_Int_143) RetryAgreed) (exists ((Measure_time_Int_144 Int) (Measure_userUnderDressed_Bool_52 Bool) (Measure_roomTemperature_Int_145 Int) (Measure_assentToSupportCalls_Bool_53 Bool) (Measure_userDistressed_Int_146 Int)) (and (and (or (exists ((DressingAbandoned_time_Int_148 Int)) (and (>= DressingAbandoned_time_Int_148 RetryAgreed_time_Int_143) (set.member (tuple DressingAbandoned_time_Int_148) DressingAbandoned))) (exists ((DressingComplete_time_Int_147 Int)) (and (>= DressingComplete_time_Int_147 RetryAgreed_time_Int_143) (set.member (tuple DressingComplete_time_Int_147) DressingComplete)))) (= RetryAgreed_time_Int_143 Measure_time_Int_144)) (set.member (tuple Measure_time_Int_144 Measure_userUnderDressed_Bool_52 Measure_roomTemperature_Int_145 Measure_assentToSupportCalls_Bool_53 Measure_userDistressed_Int_146) Measure))))))
(assert (forall ((CurtainOpenRqt_time_Int_162 Int)) (=> (set.member (tuple CurtainOpenRqt_time_Int_162) CurtainOpenRqt) (exists ((Measure_time_Int_163 Int) (Measure_userUnderDressed_Bool_58 Bool) (Measure_roomTemperature_Int_164 Int) (Measure_assentToSupportCalls_Bool_59 Bool) (Measure_userDistressed_Int_165 Int)) (and (and (and (=> (and true (and (not Measure_userUnderDressed_Bool_58) (and (not (> Measure_userDistressed_Int_165 2)) true))) (exists ((CurtainsOpened_time_Int_166 Int)) (and (and (>= CurtainsOpened_time_Int_166 (+ CurtainOpenRqt_time_Int_162 0)) (<= CurtainsOpened_time_Int_166 (+ CurtainOpenRqt_time_Int_162 60))) (set.member (tuple CurtainsOpened_time_Int_166) CurtainsOpened)))) (and (=> (and Measure_userUnderDressed_Bool_58 (and (not (> Measure_userDistressed_Int_165 2)) true)) (exists ((RefuseRequest_time_Int_167 Int)) (and (and (>= RefuseRequest_time_Int_167 (+ CurtainOpenRqt_time_Int_162 0)) (<= RefuseRequest_time_Int_167 (+ CurtainOpenRqt_time_Int_162 30))) (set.member (tuple RefuseRequest_time_Int_167) RefuseRequest)))) (=> (and (> Measure_userDistressed_Int_165 2) true) (exists ((CurtainsOpened_time_Int_168 Int)) (and (and (>= CurtainsOpened_time_Int_168 (+ CurtainOpenRqt_time_Int_162 0)) (<= CurtainsOpened_time_Int_168 (+ CurtainOpenRqt_time_Int_162 60))) (set.member (tuple CurtainsOpened_time_Int_168) CurtainsOpened)))))) (= CurtainOpenRqt_time_Int_162 Measure_time_Int_163)) (set.member (tuple Measure_time_Int_163 Measure_userUnderDressed_Bool_58 Measure_roomTemperature_Int_164 Measure_assentToSupportCalls_Bool_59 Measure_userDistressed_Int_165) Measure))))))
(assert (forall ((UserFallen_time_Int_183 Int)) (=> (set.member (tuple UserFallen_time_Int_183) UserFallen) (exists ((Measure_time_Int_184 Int) (Measure_userUnderDressed_Bool_64 Bool) (Measure_roomTemperature_Int_185 Int) (Measure_assentToSupportCalls_Bool_65 Bool) (Measure_userDistressed_Int_186 Int)) (and (and (and (=> (and true (and (not (not Measure_assentToSupportCalls_Bool_65)) true)) (exists ((SupportCalled_time_Int_187 Int)) (and (and (>= SupportCalled_time_Int_187 (+ UserFallen_time_Int_183 0)) (<= SupportCalled_time_Int_187 (+ UserFallen_time_Int_183 0))) (set.member (tuple SupportCalled_time_Int_187) SupportCalled)))) (=> (and (not Measure_assentToSupportCalls_Bool_65) true) true)) (= UserFallen_time_Int_183 Measure_time_Int_184)) (set.member (tuple Measure_time_Int_184 Measure_userUnderDressed_Bool_64 Measure_roomTemperature_Int_185 Measure_assentToSupportCalls_Bool_65 Measure_userDistressed_Int_186) Measure))))))
(assert (forall ((DressingAbandoned_time_Int_200 Int)) (=> (set.member (tuple DressingAbandoned_time_Int_200) DressingAbandoned) (exists ((Measure_time_Int_201 Int) (Measure_userUnderDressed_Bool_70 Bool) (Measure_roomTemperature_Int_202 Int) (Measure_assentToSupportCalls_Bool_71 Bool) (Measure_userDistressed_Int_203 Int)) (and (and (=> true (or (exists ((Measure_time_Int_205 Int) (Measure_userUnderDressed_Bool_72 Bool) (Measure_roomTemperature_Int_206 Int) (Measure_assentToSupportCalls_Bool_73 Bool) (Measure_userDistressed_Int_207 Int)) (and (and (and (=> (and true (and (not (not Measure_assentToSupportCalls_Bool_73)) true)) (exists ((SupportCalled_time_Int_208 Int)) (and (and (>= SupportCalled_time_Int_208 (+ Measure_time_Int_205 0)) (<= SupportCalled_time_Int_208 (+ Measure_time_Int_205 0))) (set.member (tuple SupportCalled_time_Int_208) SupportCalled)))) (=> (and (not Measure_assentToSupportCalls_Bool_73) true) true)) (= (+ Measure_time_Int_201 1800) Measure_time_Int_205)) (set.member (tuple Measure_time_Int_205 Measure_userUnderDressed_Bool_72 Measure_roomTemperature_Int_206 Measure_assentToSupportCalls_Bool_73 Measure_userDistressed_Int_207) Measure))) (exists ((RetryAgreed_time_Int_204 Int)) (and (and (>= RetryAgreed_time_Int_204 (+ DressingAbandoned_time_Int_200 0)) (<= RetryAgreed_time_Int_204 (+ DressingAbandoned_time_Int_200 1800))) (set.member (tuple RetryAgreed_time_Int_204) RetryAgreed))))) (= DressingAbandoned_time_Int_200 Measure_time_Int_201)) (set.member (tuple Measure_time_Int_201 Measure_userUnderDressed_Bool_70 Measure_roomTemperature_Int_202 Measure_assentToSupportCalls_Bool_71 Measure_userDistressed_Int_203) Measure))))))
(assert (forall ((DressingStarted_time_Int_225 Int)) (=> (set.member (tuple DressingStarted_time_Int_225) DressingStarted) (exists ((Measure_time_Int_226 Int) (Measure_userUnderDressed_Bool_80 Bool) (Measure_roomTemperature_Int_227 Int) (Measure_assentToSupportCalls_Bool_81 Bool) (Measure_userDistressed_Int_228 Int)) (and (and (or (or (exists ((DressingComplete_time_Int_230 Int)) (and (and (>= DressingComplete_time_Int_230 (+ DressingStarted_time_Int_225 0)) (<= DressingComplete_time_Int_230 (+ DressingStarted_time_Int_225 60))) (set.member (tuple DressingComplete_time_Int_230) DressingComplete))) (exists ((DressingAbandoned_time_Int_229 Int)) (and (and (>= DressingAbandoned_time_Int_229 (+ DressingStarted_time_Int_225 0)) (<= DressingAbandoned_time_Int_229 (+ DressingStarted_time_Int_225 120))) (set.member (tuple DressingAbandoned_time_Int_229) DressingAbandoned)))) (not (or Measure_userUnderDressed_Bool_80 (< Measure_roomTemperature_Int_227 16)))) (= DressingStarted_time_Int_225 Measure_time_Int_226)) (set.member (tuple Measure_time_Int_226 Measure_userUnderDressed_Bool_80 Measure_roomTemperature_Int_227 Measure_assentToSupportCalls_Bool_81 Measure_userDistressed_Int_228) Measure))))))
(assert (forall ((UserFallen_time_Int_253 Int)) (=> (set.member (tuple UserFallen_time_Int_253) UserFallen) (exists ((Measure_time_Int_254 Int) (Measure_userUnderDressed_Bool_92 Bool) (Measure_roomTemperature_Int_255 Int) (Measure_assentToSupportCalls_Bool_93 Bool) (Measure_userDistressed_Int_256 Int)) (and (and (or (exists ((not_SupportCalled_start_time_Int_258 Int) (not_SupportCalled_end_time_Int_259 Int)) (and (and (= not_SupportCalled_end_time_Int_259 (+ UserFallen_time_Int_253 120)) (= not_SupportCalled_start_time_Int_258 (+ UserFallen_time_Int_253 0))) (set.member (tuple not_SupportCalled_start_time_Int_258 not_SupportCalled_end_time_Int_259) not_SupportCalled))) (not Measure_assentToSupportCalls_Bool_93)) (= UserFallen_time_Int_253 Measure_time_Int_254)) (set.member (tuple Measure_time_Int_254 Measure_userUnderDressed_Bool_92 Measure_roomTemperature_Int_255 Measure_assentToSupportCalls_Bool_93 Measure_userDistressed_Int_256) Measure))))))
(assert (and (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_9 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_9) ((_ tuple.select 2) tuple_9)) (<= ((_ tuple.select 1) tuple_9) ((_ tuple.select 0) tuple_9)))))) (rel.product RetryAgreed not_RetryAgreed))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_8 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_8) ((_ tuple.select 2) tuple_8)) (<= ((_ tuple.select 1) tuple_8) ((_ tuple.select 0) tuple_8)))))) (rel.product SupportCalled not_SupportCalled))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_7 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_7) ((_ tuple.select 2) tuple_7)) (<= ((_ tuple.select 1) tuple_7) ((_ tuple.select 0) tuple_7)))))) (rel.product UserFallen not_UserFallen))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_6 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_6) ((_ tuple.select 2) tuple_6)) (<= ((_ tuple.select 1) tuple_6) ((_ tuple.select 0) tuple_6)))))) (rel.product RefuseRequest not_RefuseRequest))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_5 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_5) ((_ tuple.select 2) tuple_5)) (<= ((_ tuple.select 1) tuple_5) ((_ tuple.select 0) tuple_5)))))) (rel.product CurtainsOpened not_CurtainsOpened))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_4 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_4) ((_ tuple.select 2) tuple_4)) (<= ((_ tuple.select 1) tuple_4) ((_ tuple.select 0) tuple_4)))))) (rel.product CurtainOpenRqt not_CurtainOpenRqt))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_3 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_3) ((_ tuple.select 2) tuple_3)) (<= ((_ tuple.select 1) tuple_3) ((_ tuple.select 0) tuple_3)))))) (rel.product DressingAbandoned not_DressingAbandoned))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_2 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_2) ((_ tuple.select 2) tuple_2)) (<= ((_ tuple.select 1) tuple_2) ((_ tuple.select 0) tuple_2)))))) (rel.product DressingComplete not_DressingComplete))) (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_1 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_1) ((_ tuple.select 2) tuple_1)) (<= ((_ tuple.select 1) tuple_1) ((_ tuple.select 0) tuple_1)))))) (rel.product DressingStarted not_DressingStarted))))))))))) (forall ((Measure_time_Int_335 Int) (Measure_userUnderDressed_Bool_106 Bool) (Measure_roomTemperature_Int_336 Int) (Measure_assentToSupportCalls_Bool_107 Bool) (Measure_userDistressed_Int_337 Int) (Measure_time_Int_338 Int) (Measure_userUnderDressed_Bool_108 Bool) (Measure_roomTemperature_Int_339 Int) (Measure_assentToSupportCalls_Bool_109 Bool) (Measure_userDistressed_Int_340 Int)) (=> (and (set.member (tuple Measure_time_Int_338 Measure_userUnderDressed_Bool_108 Measure_roomTemperature_Int_339 Measure_assentToSupportCalls_Bool_109 Measure_userDistressed_Int_340) Measure) (set.member (tuple Measure_time_Int_335 Measure_userUnderDressed_Bool_106 Measure_roomTemperature_Int_336 Measure_assentToSupportCalls_Bool_107 Measure_userDistressed_Int_337) Measure)) (=> (= Measure_time_Int_335 Measure_time_Int_338) (and (= Measure_userDistressed_Int_337 Measure_userDistressed_Int_340) (and (= Measure_assentToSupportCalls_Bool_107 Measure_assentToSupportCalls_Bool_109) (and (= Measure_roomTemperature_Int_336 Measure_roomTemperature_Int_339) (and (= Measure_userUnderDressed_Bool_106 Measure_userUnderDressed_Bool_108) (= Measure_time_Int_335 Measure_time_Int_338))))))))))
(assert (=> (exists ((DressingStarted_time_Int_290 Int)) (and true (set.member (tuple DressingStarted_time_Int_290) DressingStarted))) (and (exists ((DressingStarted_time_Int_293 Int)) (and (forall ((DressingStarted_time_Int_294 Int)) (=> (set.member (tuple DressingStarted_time_Int_294) DressingStarted) (<= DressingStarted_time_Int_294 DressingStarted_time_Int_293))) (set.member (tuple DressingStarted_time_Int_293) DressingStarted))) (exists ((DressingStarted_time_Int_291 Int)) (and (forall ((DressingStarted_time_Int_292 Int)) (=> (set.member (tuple DressingStarted_time_Int_292) DressingStarted) (>= DressingStarted_time_Int_292 DressingStarted_time_Int_291))) (set.member (tuple DressingStarted_time_Int_291) DressingStarted))))))
(assert (=> (exists ((DressingComplete_time_Int_295 Int)) (and true (set.member (tuple DressingComplete_time_Int_295) DressingComplete))) (and (exists ((DressingComplete_time_Int_298 Int)) (and (forall ((DressingComplete_time_Int_299 Int)) (=> (set.member (tuple DressingComplete_time_Int_299) DressingComplete) (<= DressingComplete_time_Int_299 DressingComplete_time_Int_298))) (set.member (tuple DressingComplete_time_Int_298) DressingComplete))) (exists ((DressingComplete_time_Int_296 Int)) (and (forall ((DressingComplete_time_Int_297 Int)) (=> (set.member (tuple DressingComplete_time_Int_297) DressingComplete) (>= DressingComplete_time_Int_297 DressingComplete_time_Int_296))) (set.member (tuple DressingComplete_time_Int_296) DressingComplete))))))
(assert (=> (exists ((DressingAbandoned_time_Int_300 Int)) (and true (set.member (tuple DressingAbandoned_time_Int_300) DressingAbandoned))) (and (exists ((DressingAbandoned_time_Int_303 Int)) (and (forall ((DressingAbandoned_time_Int_304 Int)) (=> (set.member (tuple DressingAbandoned_time_Int_304) DressingAbandoned) (<= DressingAbandoned_time_Int_304 DressingAbandoned_time_Int_303))) (set.member (tuple DressingAbandoned_time_Int_303) DressingAbandoned))) (exists ((DressingAbandoned_time_Int_301 Int)) (and (forall ((DressingAbandoned_time_Int_302 Int)) (=> (set.member (tuple DressingAbandoned_time_Int_302) DressingAbandoned) (>= DressingAbandoned_time_Int_302 DressingAbandoned_time_Int_301))) (set.member (tuple DressingAbandoned_time_Int_301) DressingAbandoned))))))
(assert (=> (exists ((CurtainOpenRqt_time_Int_305 Int)) (and true (set.member (tuple CurtainOpenRqt_time_Int_305) CurtainOpenRqt))) (and (exists ((CurtainOpenRqt_time_Int_308 Int)) (and (forall ((CurtainOpenRqt_time_Int_309 Int)) (=> (set.member (tuple CurtainOpenRqt_time_Int_309) CurtainOpenRqt) (<= CurtainOpenRqt_time_Int_309 CurtainOpenRqt_time_Int_308))) (set.member (tuple CurtainOpenRqt_time_Int_308) CurtainOpenRqt))) (exists ((CurtainOpenRqt_time_Int_306 Int)) (and (forall ((CurtainOpenRqt_time_Int_307 Int)) (=> (set.member (tuple CurtainOpenRqt_time_Int_307) CurtainOpenRqt) (>= CurtainOpenRqt_time_Int_307 CurtainOpenRqt_time_Int_306))) (set.member (tuple CurtainOpenRqt_time_Int_306) CurtainOpenRqt))))))
(assert (=> (exists ((CurtainsOpened_time_Int_310 Int)) (and true (set.member (tuple CurtainsOpened_time_Int_310) CurtainsOpened))) (and (exists ((CurtainsOpened_time_Int_313 Int)) (and (forall ((CurtainsOpened_time_Int_314 Int)) (=> (set.member (tuple CurtainsOpened_time_Int_314) CurtainsOpened) (<= CurtainsOpened_time_Int_314 CurtainsOpened_time_Int_313))) (set.member (tuple CurtainsOpened_time_Int_313) CurtainsOpened))) (exists ((CurtainsOpened_time_Int_311 Int)) (and (forall ((CurtainsOpened_time_Int_312 Int)) (=> (set.member (tuple CurtainsOpened_time_Int_312) CurtainsOpened) (>= CurtainsOpened_time_Int_312 CurtainsOpened_time_Int_311))) (set.member (tuple CurtainsOpened_time_Int_311) CurtainsOpened))))))
(assert (=> (exists ((RefuseRequest_time_Int_315 Int)) (and true (set.member (tuple RefuseRequest_time_Int_315) RefuseRequest))) (and (exists ((RefuseRequest_time_Int_318 Int)) (and (forall ((RefuseRequest_time_Int_319 Int)) (=> (set.member (tuple RefuseRequest_time_Int_319) RefuseRequest) (<= RefuseRequest_time_Int_319 RefuseRequest_time_Int_318))) (set.member (tuple RefuseRequest_time_Int_318) RefuseRequest))) (exists ((RefuseRequest_time_Int_316 Int)) (and (forall ((RefuseRequest_time_Int_317 Int)) (=> (set.member (tuple RefuseRequest_time_Int_317) RefuseRequest) (>= RefuseRequest_time_Int_317 RefuseRequest_time_Int_316))) (set.member (tuple RefuseRequest_time_Int_316) RefuseRequest))))))
(assert (=> (exists ((UserFallen_time_Int_320 Int)) (and true (set.member (tuple UserFallen_time_Int_320) UserFallen))) (and (exists ((UserFallen_time_Int_323 Int)) (and (forall ((UserFallen_time_Int_324 Int)) (=> (set.member (tuple UserFallen_time_Int_324) UserFallen) (<= UserFallen_time_Int_324 UserFallen_time_Int_323))) (set.member (tuple UserFallen_time_Int_323) UserFallen))) (exists ((UserFallen_time_Int_321 Int)) (and (forall ((UserFallen_time_Int_322 Int)) (=> (set.member (tuple UserFallen_time_Int_322) UserFallen) (>= UserFallen_time_Int_322 UserFallen_time_Int_321))) (set.member (tuple UserFallen_time_Int_321) UserFallen))))))
(assert (=> (exists ((SupportCalled_time_Int_325 Int)) (and true (set.member (tuple SupportCalled_time_Int_325) SupportCalled))) (and (exists ((SupportCalled_time_Int_328 Int)) (and (forall ((SupportCalled_time_Int_329 Int)) (=> (set.member (tuple SupportCalled_time_Int_329) SupportCalled) (<= SupportCalled_time_Int_329 SupportCalled_time_Int_328))) (set.member (tuple SupportCalled_time_Int_328) SupportCalled))) (exists ((SupportCalled_time_Int_326 Int)) (and (forall ((SupportCalled_time_Int_327 Int)) (=> (set.member (tuple SupportCalled_time_Int_327) SupportCalled) (>= SupportCalled_time_Int_327 SupportCalled_time_Int_326))) (set.member (tuple SupportCalled_time_Int_326) SupportCalled))))))
(assert (=> (exists ((RetryAgreed_time_Int_330 Int)) (and true (set.member (tuple RetryAgreed_time_Int_330) RetryAgreed))) (and (exists ((RetryAgreed_time_Int_333 Int)) (and (forall ((RetryAgreed_time_Int_334 Int)) (=> (set.member (tuple RetryAgreed_time_Int_334) RetryAgreed) (<= RetryAgreed_time_Int_334 RetryAgreed_time_Int_333))) (set.member (tuple RetryAgreed_time_Int_333) RetryAgreed))) (exists ((RetryAgreed_time_Int_331 Int)) (and (forall ((RetryAgreed_time_Int_332 Int)) (=> (set.member (tuple RetryAgreed_time_Int_332) RetryAgreed) (>= RetryAgreed_time_Int_332 RetryAgreed_time_Int_331))) (set.member (tuple RetryAgreed_time_Int_331) RetryAgreed))))))
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
(assert true)
(assert true)
(assert (forall ((Measure_time_Int_341 Int) (Measure_userUnderDressed_Bool_110 Bool) (Measure_roomTemperature_Int_342 Int) (Measure_assentToSupportCalls_Bool_111 Bool) (Measure_userDistressed_Int_343 Int)) (=> (set.member (tuple Measure_time_Int_341 Measure_userUnderDressed_Bool_110 Measure_roomTemperature_Int_342 Measure_assentToSupportCalls_Bool_111 Measure_userDistressed_Int_343) Measure) (exists ((time_val_Int_344 Int)) (and (= time_val_Int_344 Measure_time_Int_341) (set.member (tuple time_val_Int_344) time))))))
(check-sat)
