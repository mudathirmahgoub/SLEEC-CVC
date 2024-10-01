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
(declare-const Measure (Set (Tuple Int Int)))
(assert (not (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_12 (Tuple Int Int Int))) (= ((_ tuple.select 0) tuple_12) ((_ tuple.select 1) tuple_12))) (rel.product A Measure)))))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_2 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_3 (Tuple Int Int))) (and (=> true (or (not (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_5 (Tuple Int Int))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_6 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_6) (+ ((_ tuple.select 0) tuple_5) 0)) (<= ((_ tuple.select 0) tuple_6) (+ ((_ tuple.select 0) tuple_5) 5)))) C))) (= (+ ((_ tuple.select 0) tuple_3) 10) ((_ tuple.select 0) tuple_5)))) Measure))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_4 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_4) (+ ((_ tuple.select 0) tuple_2) 0)) (<= ((_ tuple.select 0) tuple_4) (+ ((_ tuple.select 0) tuple_2) 10)))) B))))) (= ((_ tuple.select 0) tuple_2) ((_ tuple.select 0) tuple_3)))) Measure))))) A)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_16 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_17 (Tuple Int Int))) (and (=> true (or (not (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_19 (Tuple Int Int))) (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_20 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_20) (+ ((_ tuple.select 0) tuple_19) 0)) (<= ((_ tuple.select 0) tuple_20) (+ ((_ tuple.select 0) tuple_19) 5)))) B))) (= (+ ((_ tuple.select 0) tuple_17) 10) ((_ tuple.select 0) tuple_19)))) Measure))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_18 (Tuple Int))) (and (>= ((_ tuple.select 0) tuple_18) (+ ((_ tuple.select 0) tuple_16) 0)) (<= ((_ tuple.select 0) tuple_18) (+ ((_ tuple.select 0) tuple_16) 10)))) A))))) (= ((_ tuple.select 0) tuple_16) ((_ tuple.select 0) tuple_17)))) Measure))))) C)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_30 (Tuple Int))) (not (not (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_31 (Tuple Int Int))) (and (not (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_33 (Tuple Int Int))) (and (= ((_ tuple.select 1) tuple_33) (+ ((_ tuple.select 0) tuple_30) 30)) (= ((_ tuple.select 0) tuple_33) (+ ((_ tuple.select 0) tuple_30) 0)))) not_B))) (= ((_ tuple.select 0) tuple_30) ((_ tuple.select 0) tuple_31)))) Measure))))) A)))
(assert (and (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_57 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_57) ((_ tuple.select 2) tuple_57)) (<= ((_ tuple.select 1) tuple_57) ((_ tuple.select 0) tuple_57)))))) (rel.product C not_C))) (and (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_56 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_56) ((_ tuple.select 2) tuple_56)) (<= ((_ tuple.select 1) tuple_56) ((_ tuple.select 0) tuple_56)))))) (rel.product B not_B))) (= (as set.empty (Set (Tuple Int Int Int))) (set.filter (lambda ((tuple_55 (Tuple Int Int Int))) (not (not (and (<= ((_ tuple.select 0) tuple_55) ((_ tuple.select 2) tuple_55)) (<= ((_ tuple.select 1) tuple_55) ((_ tuple.select 0) tuple_55)))))) (rel.product A not_A))))) (= (as set.empty (Set (Tuple Int Int Int Int))) (set.filter (lambda ((tuple_54 (Tuple Int Int Int Int))) (not (=> (= ((_ tuple.select 0) tuple_54) ((_ tuple.select 2) tuple_54)) (and (= ((_ tuple.select 1) tuple_54) ((_ tuple.select 3) tuple_54)) (= ((_ tuple.select 0) tuple_54) ((_ tuple.select 2) tuple_54)))))) (rel.product Measure Measure)))))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_42 (Tuple Int))) (not (or (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_44 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_45 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_45) ((_ tuple.select 0) tuple_42)))) A)) (> ((_ tuple.select 0) tuple_44) ((_ tuple.select 0) tuple_42)))) A))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_43 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_43) ((_ tuple.select 0) tuple_42)))) A))))) A)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_46 (Tuple Int))) (not (or (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_48 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_49 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_49) ((_ tuple.select 0) tuple_46)))) B)) (> ((_ tuple.select 0) tuple_48) ((_ tuple.select 0) tuple_46)))) B))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_47 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_47) ((_ tuple.select 0) tuple_46)))) B))))) B)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_50 (Tuple Int))) (not (or (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_52 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_53 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_53) ((_ tuple.select 0) tuple_50)))) C)) (> ((_ tuple.select 0) tuple_52) ((_ tuple.select 0) tuple_50)))) C))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_51 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_51) ((_ tuple.select 0) tuple_50)))) C))))) C)))
(assert (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_1 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_1) 0))) time)))
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(assert (= (as set.empty (Set (Tuple Int Int))) (set.filter (lambda ((tuple_58 (Tuple Int Int))) (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_59 (Tuple Int))) (= ((_ tuple.select 0) tuple_59) ((_ tuple.select 0) tuple_58))) time))))) Measure)))
(check-sat)
