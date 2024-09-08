(set-logic HO_ALL)
(set-option :produce-models true)
(set-option :finite-model-find true)
(set-option :check-models true)
(set-option :sets-ext true)
(set-option :dag-thresh 0)
(set-option :uf-lazy-ll true)
(set-option :fmf-bound true)
(set-option :tlimit-per 10000)
(set-option :produce-models true)
(set-option :finite-model-find true)
(set-option :check-models true)
(set-option :sets-ext true)
(set-option :dag-thresh 0)
(set-option :uf-lazy-ll true)
(set-option :fmf-bound true)
(set-option :tlimit-per 10000)
(declare-const time (Set (Tuple Int)))
(declare-const A (Set (Tuple Int)))
(declare-const not_A (Set (Tuple Int Int)))
(declare-const B (Set (Tuple Int)))
(declare-const not_B (Set (Tuple Int Int)))
(declare-const C (Set (Tuple Int)))
(declare-const not_C (Set (Tuple Int Int)))
(declare-const Measure (Set (Tuple Int Int)))
(assert (not (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_18 (Tuple Int Int Int))) (= ((_ tuple.select 0) tuple_18) ((_ tuple.select 1) tuple_18))) (rel.product B Measure)))))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_2 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_3 (Tuple Int Int))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_4 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_4) (+ ((_ tuple.select 0) tuple_2) 0)) (<= ((_ tuple.select 0) tuple_4) (+ ((_ tuple.select 0) tuple_2) 7)))) B))) (= ((_ tuple.select 0) tuple_2) ((_ tuple.select 0) tuple_3)))) Measure))))) A)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_12 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_13 (Tuple Int Int))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_14 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_14) (+ ((_ tuple.select 0) tuple_12) 0)) (<= ((_ tuple.select 0) tuple_14) (+ ((_ tuple.select 0) tuple_12) 7)))) C))) (= ((_ tuple.select 0) tuple_12) ((_ tuple.select 0) tuple_13)))) Measure))))) B)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_22 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_23 (Tuple Int Int))) (and (or (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_24 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_24) (+ ((_ tuple.select 0) tuple_22) 0)) (<= ((_ tuple.select 0) tuple_24) (+ ((_ tuple.select 0) tuple_22) 15)))) C))) (not (< ((_ tuple.select 1) tuple_23) 20))) (= ((_ tuple.select 0) tuple_22) ((_ tuple.select 0) tuple_23)))) Measure))))) A)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_35 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_36 (Tuple Int Int))) (and (not (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_38 (Tuple Int Int))) (and (= ((_ tuple.select 1) tuple_38) (+ ((_ tuple.select 0) tuple_35) 11)) (= ((_ tuple.select 0) tuple_38) (+ ((_ tuple.select 0) tuple_35) 0)))) not_C))) (= ((_ tuple.select 0) tuple_35) ((_ tuple.select 0) tuple_36)))) Measure))))) A)))
(assert (and (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_62 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_62) ((_ tuple.select 2) tuple_62)) (<= ((_ tuple.select 1) tuple_62) ((_ tuple.select 0) tuple_62)))))) (rel.product C not_C))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_61 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_61) ((_ tuple.select 2) tuple_61)) (<= ((_ tuple.select 1) tuple_61) ((_ tuple.select 0) tuple_61)))))) (rel.product B not_B))) (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_60 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_60) ((_ tuple.select 2) tuple_60)) (<= ((_ tuple.select 1) tuple_60) ((_ tuple.select 0) tuple_60)))))) (rel.product A not_A))))) (= (as set.empty (Set (Tuple Int Int Int Int))) (set.filter (lambda ((tuple_59 (Tuple Int Int Int Int))) (not (=> (= ((_ tuple.select 0) tuple_59) ((_ tuple.select 2) tuple_59)) (and (= ((_ tuple.select 1) tuple_59) ((_ tuple.select 3) tuple_59)) (= ((_ tuple.select 0) tuple_59) ((_ tuple.select 2) tuple_59)))))) (rel.product Measure Measure)))))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_47 (Tuple Int))) (not (or (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_49 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_50 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_50) ((_ tuple.select 0) tuple_47)))) A)) (> ((_ tuple.select 0) tuple_49) ((_ tuple.select 0) tuple_47)))) A))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_48 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_48) ((_ tuple.select 0) tuple_47)))) A))))) A)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_51 (Tuple Int))) (not (or (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_53 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_54 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_54) ((_ tuple.select 0) tuple_51)))) B)) (> ((_ tuple.select 0) tuple_53) ((_ tuple.select 0) tuple_51)))) B))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_52 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_52) ((_ tuple.select 0) tuple_51)))) B))))) B)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_55 (Tuple Int))) (not (or (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_57 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_58 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_58) ((_ tuple.select 0) tuple_55)))) C)) (> ((_ tuple.select 0) tuple_57) ((_ tuple.select 0) tuple_55)))) C))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_56 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_56) ((_ tuple.select 0) tuple_55)))) C))))) C)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_1 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_1) 0))) time)))
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_63 (Tuple Int Int))) (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_64 (Tuple Int))) (= ((_ tuple.select 0) tuple_64) ((_ tuple.select 0) tuple_63))) time))))) Measure)))
(check-sat)
(get-model)
