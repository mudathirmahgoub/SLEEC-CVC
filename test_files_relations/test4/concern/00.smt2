(set-logic HO_ALL)
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
(assert (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_40 (Tuple Int))) (not (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_41 (Tuple Int Int))) (and (not (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_43 (Tuple Int Int))) (and (= ((_ tuple.select 1) tuple_43) (+ ((_ tuple.select 0) tuple_40) 30)) (= ((_ tuple.select 0) tuple_43) (+ ((_ tuple.select 0) tuple_40) 1)))) not_D))) (= ((_ tuple.select 0) tuple_40) ((_ tuple.select 0) tuple_41)))) Measure)))) C))))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_2 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_3 (Tuple Int Int))) (and (=> true (or (not (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_5 (Tuple Int Int))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_6 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_6) (+ ((_ tuple.select 0) tuple_5) 0)) (<= ((_ tuple.select 0) tuple_6) (+ ((_ tuple.select 0) tuple_5) 5)))) D))) (= (+ ((_ tuple.select 0) tuple_3) 10) ((_ tuple.select 0) tuple_5)))) Measure))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_4 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_4) (+ ((_ tuple.select 0) tuple_2) 0)) (<= ((_ tuple.select 0) tuple_4) (+ ((_ tuple.select 0) tuple_2) 10)))) B))))) (= ((_ tuple.select 0) tuple_2) ((_ tuple.select 0) tuple_3)))) Measure))))) A)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_16 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_17 (Tuple Int Int))) (and (=> true (or (not (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_19 (Tuple Int Int))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_20 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_20) (+ ((_ tuple.select 0) tuple_19) 0)) (<= ((_ tuple.select 0) tuple_20) (+ ((_ tuple.select 0) tuple_19) 5)))) B))) (= (+ ((_ tuple.select 0) tuple_17) 10) ((_ tuple.select 0) tuple_19)))) Measure))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_18 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_18) (+ ((_ tuple.select 0) tuple_16) 1)) (<= ((_ tuple.select 0) tuple_18) (+ ((_ tuple.select 0) tuple_16) 10)))) A))))) (= ((_ tuple.select 0) tuple_16) ((_ tuple.select 0) tuple_17)))) Measure))))) C)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_30 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_31 (Tuple Int Int))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_32 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_32) (+ ((_ tuple.select 0) tuple_30) 0)) (<= ((_ tuple.select 0) tuple_32) (+ ((_ tuple.select 0) tuple_30) 1)))) D))) (= ((_ tuple.select 0) tuple_30) ((_ tuple.select 0) tuple_31)))) Measure))))) B)))
(assert (and (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_68 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_68) ((_ tuple.select 2) tuple_68)) (<= ((_ tuple.select 1) tuple_68) ((_ tuple.select 0) tuple_68)))))) (rel.product D not_D))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_67 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_67) ((_ tuple.select 2) tuple_67)) (<= ((_ tuple.select 1) tuple_67) ((_ tuple.select 0) tuple_67)))))) (rel.product C not_C))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_66 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_66) ((_ tuple.select 2) tuple_66)) (<= ((_ tuple.select 1) tuple_66) ((_ tuple.select 0) tuple_66)))))) (rel.product B not_B))) (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_65 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_65) ((_ tuple.select 2) tuple_65)) (<= ((_ tuple.select 1) tuple_65) ((_ tuple.select 0) tuple_65)))))) (rel.product A not_A)))))) (= (as set.empty (Set (Tuple Int Int Int Int))) (set.filter (lambda ((tuple_64 (Tuple Int Int Int Int))) (not (=> (= ((_ tuple.select 0) tuple_64) ((_ tuple.select 2) tuple_64)) (and (= ((_ tuple.select 1) tuple_64) ((_ tuple.select 3) tuple_64)) (= ((_ tuple.select 0) tuple_64) ((_ tuple.select 2) tuple_64)))))) (rel.product Measure Measure)))))
(assert (=> (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_44 (Tuple Int))) true) A))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_47 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_48 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_48) ((_ tuple.select 0) tuple_47)))) A))) A))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_45 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_46 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_46) ((_ tuple.select 0) tuple_45)))) A))) A))))))
(assert (=> (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_49 (Tuple Int))) true) B))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_52 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_53 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_53) ((_ tuple.select 0) tuple_52)))) B))) B))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_50 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_51 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_51) ((_ tuple.select 0) tuple_50)))) B))) B))))))
(assert (=> (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_54 (Tuple Int))) true) C))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_57 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_58 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_58) ((_ tuple.select 0) tuple_57)))) C))) C))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_55 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_56 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_56) ((_ tuple.select 0) tuple_55)))) C))) C))))))
(assert (=> (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_59 (Tuple Int))) true) D))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_62 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_63 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_63) ((_ tuple.select 0) tuple_62)))) D))) D))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_60 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_61 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_61) ((_ tuple.select 0) tuple_60)))) D))) D))))))
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
(assert (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_69 (Tuple Int Int))) (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_70 (Tuple Int))) (= ((_ tuple.select 0) tuple_70) ((_ tuple.select 0) tuple_69))) time))))) Measure)))
(check-sat)
