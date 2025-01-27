lhs: (<= ((_ tuple.select 0) tuple_2) 2)
rhs: (>= ((_ tuple.select 0) tuple_2) 0)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (<= ((_ tuple.select 0) tuple_3) 2)
rhs: (>= ((_ tuple.select 0) tuple_3) 0)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_6) (+ ((_ tuple.select 0) tuple_4) 0))
rhs: (<= ((_ tuple.select 0) tuple_6) (+ ((_ tuple.select 0) tuple_4) 600))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_7) (+ ((_ tuple.select 0) tuple_4) 0))
rhs: (<= ((_ tuple.select 0) tuple_7) (+ ((_ tuple.select 0) tuple_4) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: ((_ tuple.select 1) tuple_5)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and ((_ tuple.select 1) tuple_5) true)
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_7 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_4) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_7))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindLater)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not ((_ tuple.select 1) tuple_5))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (and (not ((_ tuple.select 1) tuple_5)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and true (and (not ((_ tuple.select 1) tuple_5)) true))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_6 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_4))) (let ((_let_2 ((_ tuple.select 0) tuple_6))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 600)))))) InformUser)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not ((_ tuple.select 1) tuple_5)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not ((_ tuple.select 1) tuple_5)) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_6 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_4))) (let ((_let_2 ((_ tuple.select 0) tuple_6))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 600)))))) InformUser))))
rhs: (=> (and ((_ tuple.select 1) tuple_5) true) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_7 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_4) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_7))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindLater))))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 ((_ tuple.select 1) tuple_5))) (and (=> (and true (and (not _let_1) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_6 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_4))) (let ((_let_2 ((_ tuple.select 0) tuple_6))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 600)))))) InformUser)))) (=> (and _let_1 true) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_7 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_4) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_7))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindLater))))))
rhs: (= ((_ tuple.select 0) tuple_4) ((_ tuple.select 0) tuple_5))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_10) (+ ((_ tuple.select 0) tuple_8) 0))
rhs: (<= ((_ tuple.select 0) tuple_10) (+ ((_ tuple.select 0) tuple_8) 600))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_11) (+ ((_ tuple.select 0) tuple_8) 0))
rhs: (<= ((_ tuple.select 0) tuple_11) (+ ((_ tuple.select 0) tuple_8) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: ((_ tuple.select 1) tuple_9)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and ((_ tuple.select 1) tuple_9) true)
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_11 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_8) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_11))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindLater)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not ((_ tuple.select 1) tuple_9))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (and (not ((_ tuple.select 1) tuple_9)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and true (and (not ((_ tuple.select 1) tuple_9)) true))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_10 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_8))) (let ((_let_2 ((_ tuple.select 0) tuple_10))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 600)))))) InformUser)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not ((_ tuple.select 1) tuple_9)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not ((_ tuple.select 1) tuple_9)) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_10 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_8))) (let ((_let_2 ((_ tuple.select 0) tuple_10))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 600)))))) InformUser))))
rhs: (=> (and ((_ tuple.select 1) tuple_9) true) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_11 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_8) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_11))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindLater))))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 ((_ tuple.select 1) tuple_9))) (not (and (=> (and true (and (not _let_1) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_10 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_8))) (let ((_let_2 ((_ tuple.select 0) tuple_10))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 600)))))) InformUser)))) (=> (and _let_1 true) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_11 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_8) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_11))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindLater)))))))
rhs: (= ((_ tuple.select 0) tuple_8) ((_ tuple.select 0) tuple_9))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_14) ((_ tuple.select 0) tuple_15))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_15 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_14) ((_ tuple.select 0) tuple_15))))) MonitorMealTime))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_13 (Tuple Int))) true) MonitorMealTime)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_14 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_15 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_14) ((_ tuple.select 0) tuple_15))))) MonitorMealTime)) true)) MonitorMealTime)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_18) (+ ((_ tuple.select 0) tuple_16) 0))
rhs: (<= ((_ tuple.select 0) tuple_18) (+ ((_ tuple.select 0) tuple_16) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_18 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_16) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_18))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) TrackTime)))
rhs: (= ((_ tuple.select 0) tuple_16) ((_ tuple.select 0) tuple_17))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_21) (+ ((_ tuple.select 0) tuple_19) 0))
rhs: (<= ((_ tuple.select 0) tuple_21) (+ ((_ tuple.select 0) tuple_19) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_21 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_19) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_21))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) TrackTime))))
rhs: (= ((_ tuple.select 0) tuple_19) ((_ tuple.select 0) tuple_20))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_24) ((_ tuple.select 0) tuple_25))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_25 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_24) ((_ tuple.select 0) tuple_25))))) AgentDeployed))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_23 (Tuple Int))) true) AgentDeployed)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_24 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_25 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_24) ((_ tuple.select 0) tuple_25))))) AgentDeployed)) true)) AgentDeployed)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_28) (+ ((_ tuple.select 0) tuple_26) 0))
rhs: (<= ((_ tuple.select 0) tuple_28) (+ ((_ tuple.select 0) tuple_26) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_28 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_26) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_28))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver)))
rhs: (not (> ((_ tuple.select 2) tuple_27) 28800))
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (or (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_28 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_26) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_28))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver))) (not (> ((_ tuple.select 2) tuple_27) 28800)))
rhs: (= ((_ tuple.select 0) tuple_26) ((_ tuple.select 0) tuple_27))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_31) (+ ((_ tuple.select 0) tuple_29) 0))
rhs: (<= ((_ tuple.select 0) tuple_31) (+ ((_ tuple.select 0) tuple_29) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_31 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_29) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_31))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver))))
rhs: (> ((_ tuple.select 2) tuple_30) 28800)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_31 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_29) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_31))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver)))) (> ((_ tuple.select 2) tuple_30) 28800))
rhs: (= ((_ tuple.select 0) tuple_29) ((_ tuple.select 0) tuple_30))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (> ((_ tuple.select 3) tuple_32) 28800)
rhs: (= ((_ tuple.select 0) tuple_32) ((_ tuple.select 1) tuple_32))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (> ((_ tuple.select 2) tuple_34) 28800)
rhs: (= ((_ tuple.select 0) tuple_34) ((_ tuple.select 0) tuple_33))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (> ((_ tuple.select 2) tuple_36) 28800)
rhs: (= ((_ tuple.select 0) tuple_36) ((_ tuple.select 0) tuple_35))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (> ((_ tuple.select 2) tuple_38) 28800)
rhs: (= ((_ tuple.select 0) tuple_38) ((_ tuple.select 0) tuple_37))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_38 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_38) 28800) (= ((_ tuple.select 0) tuple_38) ((_ tuple.select 0) tuple_37)))) Measure)))
rhs: (>= ((_ tuple.select 0) tuple_35) ((_ tuple.select 0) tuple_37))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_37 (Tuple Int))) (not (=> (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_38 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_38) 28800) (= ((_ tuple.select 0) tuple_38) ((_ tuple.select 0) tuple_37)))) Measure))) (>= ((_ tuple.select 0) tuple_35) ((_ tuple.select 0) tuple_37))))) TrackTime))
rhs: (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_36 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_36) 28800) (= ((_ tuple.select 0) tuple_36) ((_ tuple.select 0) tuple_35)))) Measure)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_33 (Tuple Int))) (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_34 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_34) 28800) (= ((_ tuple.select 0) tuple_34) ((_ tuple.select 0) tuple_33)))) Measure)))) TrackTime)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_35 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_37 (Tuple Int))) (not (=> (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_38 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_38) 28800) (= ((_ tuple.select 0) tuple_38) ((_ tuple.select 0) tuple_37)))) Measure))) (>= ((_ tuple.select 0) tuple_35) ((_ tuple.select 0) tuple_37))))) TrackTime)) (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_36 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_36) 28800) (= ((_ tuple.select 0) tuple_36) ((_ tuple.select 0) tuple_35)))) Measure))))) TrackTime)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_41) (+ ((_ tuple.select 0) tuple_39) 0))
rhs: (<= ((_ tuple.select 0) tuple_41) (+ ((_ tuple.select 0) tuple_39) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_41 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_39) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_41))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) GiveSuggestion)))
rhs: (not (> ((_ tuple.select 2) tuple_40) 28800))
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (or (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_41 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_39) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_41))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) GiveSuggestion))) (not (> ((_ tuple.select 2) tuple_40) 28800)))
rhs: (= ((_ tuple.select 0) tuple_39) ((_ tuple.select 0) tuple_40))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_44) (+ ((_ tuple.select 0) tuple_42) 0))
rhs: (<= ((_ tuple.select 0) tuple_44) (+ ((_ tuple.select 0) tuple_42) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_44 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_42) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_44))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) GiveSuggestion))))
rhs: (> ((_ tuple.select 2) tuple_43) 28800)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_44 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_42) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_44))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) GiveSuggestion)))) (> ((_ tuple.select 2) tuple_43) 28800))
rhs: (= ((_ tuple.select 0) tuple_42) ((_ tuple.select 0) tuple_43))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (> ((_ tuple.select 3) tuple_45) 28800)
rhs: (= ((_ tuple.select 0) tuple_45) ((_ tuple.select 1) tuple_45))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (> ((_ tuple.select 2) tuple_47) 28800)
rhs: (= ((_ tuple.select 0) tuple_47) ((_ tuple.select 0) tuple_46))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (> ((_ tuple.select 2) tuple_49) 28800)
rhs: (= ((_ tuple.select 0) tuple_49) ((_ tuple.select 0) tuple_48))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (> ((_ tuple.select 2) tuple_51) 28800)
rhs: (= ((_ tuple.select 0) tuple_51) ((_ tuple.select 0) tuple_50))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_51 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_51) 28800) (= ((_ tuple.select 0) tuple_51) ((_ tuple.select 0) tuple_50)))) Measure)))
rhs: (>= ((_ tuple.select 0) tuple_48) ((_ tuple.select 0) tuple_50))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_50 (Tuple Int))) (not (=> (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_51 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_51) 28800) (= ((_ tuple.select 0) tuple_51) ((_ tuple.select 0) tuple_50)))) Measure))) (>= ((_ tuple.select 0) tuple_48) ((_ tuple.select 0) tuple_50))))) TrackTime))
rhs: (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_49 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_49) 28800) (= ((_ tuple.select 0) tuple_49) ((_ tuple.select 0) tuple_48)))) Measure)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_46 (Tuple Int))) (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_47 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_47) 28800) (= ((_ tuple.select 0) tuple_47) ((_ tuple.select 0) tuple_46)))) Measure)))) TrackTime)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_48 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_50 (Tuple Int))) (not (=> (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_51 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_51) 28800) (= ((_ tuple.select 0) tuple_51) ((_ tuple.select 0) tuple_50)))) Measure))) (>= ((_ tuple.select 0) tuple_48) ((_ tuple.select 0) tuple_50))))) TrackTime)) (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_49 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_49) 28800) (= ((_ tuple.select 0) tuple_49) ((_ tuple.select 0) tuple_48)))) Measure))))) TrackTime)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_54) (+ ((_ tuple.select 0) tuple_52) 0))
rhs: (<= ((_ tuple.select 0) tuple_54) (+ ((_ tuple.select 0) tuple_52) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_54 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_52) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_54))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskCallHelp)))
rhs: (= ((_ tuple.select 0) tuple_52) ((_ tuple.select 0) tuple_53))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_57) (+ ((_ tuple.select 0) tuple_55) 0))
rhs: (<= ((_ tuple.select 0) tuple_57) (+ ((_ tuple.select 0) tuple_55) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_57 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_55) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_57))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskCallHelp))))
rhs: (= ((_ tuple.select 0) tuple_55) ((_ tuple.select 0) tuple_56))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_60) ((_ tuple.select 0) tuple_61))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_61 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_60) ((_ tuple.select 0) tuple_61))))) HumanOnFloor))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_59 (Tuple Int))) true) HumanOnFloor)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_60 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_61 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_60) ((_ tuple.select 0) tuple_61))))) HumanOnFloor)) true)) HumanOnFloor)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_64) (+ ((_ tuple.select 0) tuple_62) 0))
rhs: (<= ((_ tuple.select 0) tuple_64) (+ ((_ tuple.select 0) tuple_62) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_64 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_62) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_64))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CallEmergencyServices)))
rhs: (not (not ((_ tuple.select 10) tuple_63)))
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (or (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_64 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_62) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_64))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CallEmergencyServices))) (not (not ((_ tuple.select 10) tuple_63))))
rhs: (= ((_ tuple.select 0) tuple_62) ((_ tuple.select 0) tuple_63))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_67) (+ ((_ tuple.select 0) tuple_65) 0))
rhs: (<= ((_ tuple.select 0) tuple_67) (+ ((_ tuple.select 0) tuple_65) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_67 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_65) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_67))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CallEmergencyServices))))
rhs: (not ((_ tuple.select 10) tuple_66))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_67 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_65) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_67))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CallEmergencyServices)))) (not ((_ tuple.select 10) tuple_66)))
rhs: (= ((_ tuple.select 0) tuple_65) ((_ tuple.select 0) tuple_66))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not ((_ tuple.select 11) tuple_68))
rhs: (= ((_ tuple.select 0) tuple_68) ((_ tuple.select 1) tuple_68))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not ((_ tuple.select 10) tuple_70))
rhs: (= ((_ tuple.select 0) tuple_70) ((_ tuple.select 0) tuple_69))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not ((_ tuple.select 10) tuple_72))
rhs: (= ((_ tuple.select 0) tuple_72) ((_ tuple.select 0) tuple_71))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not ((_ tuple.select 10) tuple_74))
rhs: (= ((_ tuple.select 0) tuple_74) ((_ tuple.select 0) tuple_73))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_74 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_74)) (= ((_ tuple.select 0) tuple_74) ((_ tuple.select 0) tuple_73)))) Measure)))
rhs: (>= ((_ tuple.select 0) tuple_71) ((_ tuple.select 0) tuple_73))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_73 (Tuple Int))) (not (=> (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_74 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_74)) (= ((_ tuple.select 0) tuple_74) ((_ tuple.select 0) tuple_73)))) Measure))) (>= ((_ tuple.select 0) tuple_71) ((_ tuple.select 0) tuple_73))))) AskCallHelp))
rhs: (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_72 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_72)) (= ((_ tuple.select 0) tuple_72) ((_ tuple.select 0) tuple_71)))) Measure)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_69 (Tuple Int))) (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_70 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_70)) (= ((_ tuple.select 0) tuple_70) ((_ tuple.select 0) tuple_69)))) Measure)))) AskCallHelp)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_71 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_73 (Tuple Int))) (not (=> (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_74 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_74)) (= ((_ tuple.select 0) tuple_74) ((_ tuple.select 0) tuple_73)))) Measure))) (>= ((_ tuple.select 0) tuple_71) ((_ tuple.select 0) tuple_73))))) AskCallHelp)) (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_72 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_72)) (= ((_ tuple.select 0) tuple_72) ((_ tuple.select 0) tuple_71)))) Measure))))) AskCallHelp)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_77) (+ ((_ tuple.select 0) tuple_75) 0))
rhs: (<= ((_ tuple.select 0) tuple_77) (+ ((_ tuple.select 0) tuple_75) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_77 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_75) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_77))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver)))
rhs: (not (not ((_ tuple.select 10) tuple_76)))
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (or (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_77 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_75) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_77))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver))) (not (not ((_ tuple.select 10) tuple_76))))
rhs: (= ((_ tuple.select 0) tuple_75) ((_ tuple.select 0) tuple_76))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_80) (+ ((_ tuple.select 0) tuple_78) 0))
rhs: (<= ((_ tuple.select 0) tuple_80) (+ ((_ tuple.select 0) tuple_78) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_80 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_78) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_80))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver))))
rhs: (not ((_ tuple.select 10) tuple_79))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_80 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_78) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_80))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver)))) (not ((_ tuple.select 10) tuple_79)))
rhs: (= ((_ tuple.select 0) tuple_78) ((_ tuple.select 0) tuple_79))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not ((_ tuple.select 11) tuple_81))
rhs: (= ((_ tuple.select 0) tuple_81) ((_ tuple.select 1) tuple_81))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not ((_ tuple.select 10) tuple_83))
rhs: (= ((_ tuple.select 0) tuple_83) ((_ tuple.select 0) tuple_82))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not ((_ tuple.select 10) tuple_85))
rhs: (= ((_ tuple.select 0) tuple_85) ((_ tuple.select 0) tuple_84))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not ((_ tuple.select 10) tuple_87))
rhs: (= ((_ tuple.select 0) tuple_87) ((_ tuple.select 0) tuple_86))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_87 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_87)) (= ((_ tuple.select 0) tuple_87) ((_ tuple.select 0) tuple_86)))) Measure)))
rhs: (>= ((_ tuple.select 0) tuple_84) ((_ tuple.select 0) tuple_86))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_86 (Tuple Int))) (not (=> (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_87 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_87)) (= ((_ tuple.select 0) tuple_87) ((_ tuple.select 0) tuple_86)))) Measure))) (>= ((_ tuple.select 0) tuple_84) ((_ tuple.select 0) tuple_86))))) AskCallHelp))
rhs: (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_85 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_85)) (= ((_ tuple.select 0) tuple_85) ((_ tuple.select 0) tuple_84)))) Measure)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_82 (Tuple Int))) (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_83 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_83)) (= ((_ tuple.select 0) tuple_83) ((_ tuple.select 0) tuple_82)))) Measure)))) AskCallHelp)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_84 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_86 (Tuple Int))) (not (=> (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_87 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_87)) (= ((_ tuple.select 0) tuple_87) ((_ tuple.select 0) tuple_86)))) Measure))) (>= ((_ tuple.select 0) tuple_84) ((_ tuple.select 0) tuple_86))))) AskCallHelp)) (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_85 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_85)) (= ((_ tuple.select 0) tuple_85) ((_ tuple.select 0) tuple_84)))) Measure))))) AskCallHelp)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_90) (+ ((_ tuple.select 0) tuple_88) 0))
rhs: (<= ((_ tuple.select 0) tuple_90) (+ ((_ tuple.select 0) tuple_88) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: ((_ tuple.select 1) tuple_89)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and ((_ tuple.select 1) tuple_89) true)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not ((_ tuple.select 1) tuple_89))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (and (not ((_ tuple.select 1) tuple_89)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and true (and (not ((_ tuple.select 1) tuple_89)) true))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_90 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_88) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_90))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not ((_ tuple.select 1) tuple_89)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not ((_ tuple.select 1) tuple_89)) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_90 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_88) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_90))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser))))
rhs: (=> (and ((_ tuple.select 1) tuple_89) true) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 ((_ tuple.select 1) tuple_89))) (and (=> (and true (and (not _let_1) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_90 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_88) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_90))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)))) (=> (and _let_1 true) true)))
rhs: (not (not ((_ tuple.select 11) tuple_89)))
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (let ((_let_1 ((_ tuple.select 1) tuple_89))) (or (and (=> (and true (and (not _let_1) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_90 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_88) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_90))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)))) (=> (and _let_1 true) true)) (not (not ((_ tuple.select 11) tuple_89)))))
rhs: (= ((_ tuple.select 0) tuple_88) ((_ tuple.select 0) tuple_89))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_93) (+ ((_ tuple.select 0) tuple_91) 0))
rhs: (<= ((_ tuple.select 0) tuple_93) (+ ((_ tuple.select 0) tuple_91) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: ((_ tuple.select 1) tuple_92)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and ((_ tuple.select 1) tuple_92) true)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not ((_ tuple.select 1) tuple_92))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (and (not ((_ tuple.select 1) tuple_92)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and true (and (not ((_ tuple.select 1) tuple_92)) true))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_93 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_91) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_93))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not ((_ tuple.select 1) tuple_92)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not ((_ tuple.select 1) tuple_92)) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_93 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_91) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_93))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser))))
rhs: (=> (and ((_ tuple.select 1) tuple_92) true) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 ((_ tuple.select 1) tuple_92))) (not (and (=> (and true (and (not _let_1) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_93 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_91) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_93))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)))) (=> (and _let_1 true) true))))
rhs: (not ((_ tuple.select 11) tuple_92))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 ((_ tuple.select 1) tuple_92))) (and (not (and (=> (and true (and (not _let_1) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_93 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_91) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_93))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)))) (=> (and _let_1 true) true))) (not ((_ tuple.select 11) tuple_92))))
rhs: (= ((_ tuple.select 0) tuple_91) ((_ tuple.select 0) tuple_92))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not ((_ tuple.select 12) tuple_94))
rhs: (= ((_ tuple.select 0) tuple_94) ((_ tuple.select 1) tuple_94))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not ((_ tuple.select 11) tuple_96))
rhs: (= ((_ tuple.select 0) tuple_96) ((_ tuple.select 0) tuple_95))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not ((_ tuple.select 11) tuple_98))
rhs: (= ((_ tuple.select 0) tuple_98) ((_ tuple.select 0) tuple_97))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not ((_ tuple.select 11) tuple_100))
rhs: (= ((_ tuple.select 0) tuple_100) ((_ tuple.select 0) tuple_99))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_100 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 11) tuple_100)) (= ((_ tuple.select 0) tuple_100) ((_ tuple.select 0) tuple_99)))) Measure)))
rhs: (>= ((_ tuple.select 0) tuple_97) ((_ tuple.select 0) tuple_99))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_99 (Tuple Int))) (not (=> (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_100 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 11) tuple_100)) (= ((_ tuple.select 0) tuple_100) ((_ tuple.select 0) tuple_99)))) Measure))) (>= ((_ tuple.select 0) tuple_97) ((_ tuple.select 0) tuple_99))))) InterfereSafely))
rhs: (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_98 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 11) tuple_98)) (= ((_ tuple.select 0) tuple_98) ((_ tuple.select 0) tuple_97)))) Measure)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_95 (Tuple Int))) (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_96 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 11) tuple_96)) (= ((_ tuple.select 0) tuple_96) ((_ tuple.select 0) tuple_95)))) Measure)))) InterfereSafely)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_97 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_99 (Tuple Int))) (not (=> (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_100 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 11) tuple_100)) (= ((_ tuple.select 0) tuple_100) ((_ tuple.select 0) tuple_99)))) Measure))) (>= ((_ tuple.select 0) tuple_97) ((_ tuple.select 0) tuple_99))))) InterfereSafely)) (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_98 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 11) tuple_98)) (= ((_ tuple.select 0) tuple_98) ((_ tuple.select 0) tuple_97)))) Measure))))) InterfereSafely)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_103) (+ ((_ tuple.select 0) tuple_101) 0))
rhs: (<= ((_ tuple.select 0) tuple_103) (+ ((_ tuple.select 0) tuple_101) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_103 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_101) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_103))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AllowUserToCook)))
rhs: (= ((_ tuple.select 0) tuple_101) ((_ tuple.select 0) tuple_102))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_106) (+ ((_ tuple.select 0) tuple_104) 0))
rhs: (<= ((_ tuple.select 0) tuple_106) (+ ((_ tuple.select 0) tuple_104) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_106 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_104) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_106))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AllowUserToCook))))
rhs: (= ((_ tuple.select 0) tuple_104) ((_ tuple.select 0) tuple_105))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_109) ((_ tuple.select 0) tuple_110))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_110 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_109) ((_ tuple.select 0) tuple_110))))) UserWantsToCook))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_108 (Tuple Int))) true) UserWantsToCook)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_109 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_110 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_109) ((_ tuple.select 0) tuple_110))))) UserWantsToCook)) true)) UserWantsToCook)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= ((_ tuple.select 14) tuple_112) 2)
rhs: ((_ tuple.select 12) tuple_112)
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (>= ((_ tuple.select 0) tuple_113) (+ ((_ tuple.select 0) tuple_111) 0))
rhs: (<= ((_ tuple.select 0) tuple_113) (+ ((_ tuple.select 0) tuple_111) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_113 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_111) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_113))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely)))
rhs: (not (or (= ((_ tuple.select 14) tuple_112) 2) ((_ tuple.select 12) tuple_112)))
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (or (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_113 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_111) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_113))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely))) (not (or (= ((_ tuple.select 14) tuple_112) 2) ((_ tuple.select 12) tuple_112))))
rhs: (= ((_ tuple.select 0) tuple_111) ((_ tuple.select 0) tuple_112))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 14) tuple_115) 2)
rhs: ((_ tuple.select 12) tuple_115)
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (>= ((_ tuple.select 0) tuple_116) (+ ((_ tuple.select 0) tuple_114) 0))
rhs: (<= ((_ tuple.select 0) tuple_116) (+ ((_ tuple.select 0) tuple_114) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_116 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_114) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_116))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely))))
rhs: (or (= ((_ tuple.select 14) tuple_115) 2) ((_ tuple.select 12) tuple_115))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_116 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_114) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_116))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely)))) (or (= ((_ tuple.select 14) tuple_115) 2) ((_ tuple.select 12) tuple_115)))
rhs: (= ((_ tuple.select 0) tuple_114) ((_ tuple.select 0) tuple_115))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 15) tuple_117) 2)
rhs: ((_ tuple.select 13) tuple_117)
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (or (= ((_ tuple.select 15) tuple_117) 2) ((_ tuple.select 13) tuple_117))
rhs: (= ((_ tuple.select 0) tuple_117) ((_ tuple.select 1) tuple_117))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 14) tuple_119) 2)
rhs: ((_ tuple.select 12) tuple_119)
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (or (= ((_ tuple.select 14) tuple_119) 2) ((_ tuple.select 12) tuple_119))
rhs: (= ((_ tuple.select 0) tuple_119) ((_ tuple.select 0) tuple_118))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 14) tuple_121) 2)
rhs: ((_ tuple.select 12) tuple_121)
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (or (= ((_ tuple.select 14) tuple_121) 2) ((_ tuple.select 12) tuple_121))
rhs: (= ((_ tuple.select 0) tuple_121) ((_ tuple.select 0) tuple_120))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 14) tuple_123) 2)
rhs: ((_ tuple.select 12) tuple_123)
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (or (= ((_ tuple.select 14) tuple_123) 2) ((_ tuple.select 12) tuple_123))
rhs: (= ((_ tuple.select 0) tuple_123) ((_ tuple.select 0) tuple_122))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_123 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (= ((_ tuple.select 14) tuple_123) 2) ((_ tuple.select 12) tuple_123)) (= ((_ tuple.select 0) tuple_123) ((_ tuple.select 0) tuple_122)))) Measure)))
rhs: (>= ((_ tuple.select 0) tuple_120) ((_ tuple.select 0) tuple_122))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_122 (Tuple Int))) (not (=> (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_123 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (= ((_ tuple.select 14) tuple_123) 2) ((_ tuple.select 12) tuple_123)) (= ((_ tuple.select 0) tuple_123) ((_ tuple.select 0) tuple_122)))) Measure))) (>= ((_ tuple.select 0) tuple_120) ((_ tuple.select 0) tuple_122))))) AllowUserToCook))
rhs: (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_121 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (= ((_ tuple.select 14) tuple_121) 2) ((_ tuple.select 12) tuple_121)) (= ((_ tuple.select 0) tuple_121) ((_ tuple.select 0) tuple_120)))) Measure)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_118 (Tuple Int))) (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_119 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (= ((_ tuple.select 14) tuple_119) 2) ((_ tuple.select 12) tuple_119)) (= ((_ tuple.select 0) tuple_119) ((_ tuple.select 0) tuple_118)))) Measure)))) AllowUserToCook)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_120 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_122 (Tuple Int))) (not (=> (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_123 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (= ((_ tuple.select 14) tuple_123) 2) ((_ tuple.select 12) tuple_123)) (= ((_ tuple.select 0) tuple_123) ((_ tuple.select 0) tuple_122)))) Measure))) (>= ((_ tuple.select 0) tuple_120) ((_ tuple.select 0) tuple_122))))) AllowUserToCook)) (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_121 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (= ((_ tuple.select 14) tuple_121) 2) ((_ tuple.select 12) tuple_121)) (= ((_ tuple.select 0) tuple_121) ((_ tuple.select 0) tuple_120)))) Measure))))) AllowUserToCook)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_126) (+ ((_ tuple.select 0) tuple_124) 0))
rhs: (<= ((_ tuple.select 0) tuple_126) (+ ((_ tuple.select 0) tuple_124) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_126 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_124) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_126))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)))
rhs: (= ((_ tuple.select 0) tuple_124) ((_ tuple.select 0) tuple_125))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_129) (+ ((_ tuple.select 0) tuple_127) 0))
rhs: (<= ((_ tuple.select 0) tuple_129) (+ ((_ tuple.select 0) tuple_127) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_129 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_127) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_129))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser))))
rhs: (= ((_ tuple.select 0) tuple_127) ((_ tuple.select 0) tuple_128))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_132) ((_ tuple.select 0) tuple_133))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_133 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_132) ((_ tuple.select 0) tuple_133))))) UserHasLimitation))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_131 (Tuple Int))) true) UserHasLimitation)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_132 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_133 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_132) ((_ tuple.select 0) tuple_133))))) UserHasLimitation)) true)) UserHasLimitation)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_136) (+ ((_ tuple.select 0) tuple_134) 0))
rhs: (<= ((_ tuple.select 0) tuple_136) (+ ((_ tuple.select 0) tuple_134) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_136 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_134) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_136))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CheckTemperature)))
rhs: (= ((_ tuple.select 0) tuple_134) ((_ tuple.select 0) tuple_135))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_139) (+ ((_ tuple.select 0) tuple_137) 0))
rhs: (<= ((_ tuple.select 0) tuple_139) (+ ((_ tuple.select 0) tuple_137) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_139 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_137) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_139))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CheckTemperature))))
rhs: (= ((_ tuple.select 0) tuple_137) ((_ tuple.select 0) tuple_138))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_142) ((_ tuple.select 0) tuple_143))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_143 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_142) ((_ tuple.select 0) tuple_143))))) UserWantsToCook))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_141 (Tuple Int))) true) UserWantsToCook)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_142 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_143 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_142) ((_ tuple.select 0) tuple_143))))) UserWantsToCook)) true)) UserWantsToCook)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_146) (+ ((_ tuple.select 0) tuple_144) 0))
rhs: (<= ((_ tuple.select 0) tuple_146) (+ ((_ tuple.select 0) tuple_144) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_146 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_144) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_146))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)))
rhs: (not ((_ tuple.select 12) tuple_145))
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (or (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_146 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_144) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_146))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser))) (not ((_ tuple.select 12) tuple_145)))
rhs: (= ((_ tuple.select 0) tuple_144) ((_ tuple.select 0) tuple_145))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_149) (+ ((_ tuple.select 0) tuple_147) 0))
rhs: (<= ((_ tuple.select 0) tuple_149) (+ ((_ tuple.select 0) tuple_147) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_149 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_147) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_149))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser))))
rhs: ((_ tuple.select 12) tuple_148)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_149 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_147) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_149))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)))) ((_ tuple.select 12) tuple_148))
rhs: (= ((_ tuple.select 0) tuple_147) ((_ tuple.select 0) tuple_148))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: ((_ tuple.select 13) tuple_150)
rhs: (= ((_ tuple.select 0) tuple_150) ((_ tuple.select 1) tuple_150))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: ((_ tuple.select 12) tuple_152)
rhs: (= ((_ tuple.select 0) tuple_152) ((_ tuple.select 0) tuple_151))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: ((_ tuple.select 12) tuple_154)
rhs: (= ((_ tuple.select 0) tuple_154) ((_ tuple.select 0) tuple_153))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: ((_ tuple.select 12) tuple_156)
rhs: (= ((_ tuple.select 0) tuple_156) ((_ tuple.select 0) tuple_155))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_156 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 12) tuple_156) (= ((_ tuple.select 0) tuple_156) ((_ tuple.select 0) tuple_155)))) Measure)))
rhs: (>= ((_ tuple.select 0) tuple_153) ((_ tuple.select 0) tuple_155))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_155 (Tuple Int))) (not (=> (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_156 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 12) tuple_156) (= ((_ tuple.select 0) tuple_156) ((_ tuple.select 0) tuple_155)))) Measure))) (>= ((_ tuple.select 0) tuple_153) ((_ tuple.select 0) tuple_155))))) CheckTemperature))
rhs: (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_154 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 12) tuple_154) (= ((_ tuple.select 0) tuple_154) ((_ tuple.select 0) tuple_153)))) Measure)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_151 (Tuple Int))) (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_152 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 12) tuple_152) (= ((_ tuple.select 0) tuple_152) ((_ tuple.select 0) tuple_151)))) Measure)))) CheckTemperature)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_153 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_155 (Tuple Int))) (not (=> (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_156 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 12) tuple_156) (= ((_ tuple.select 0) tuple_156) ((_ tuple.select 0) tuple_155)))) Measure))) (>= ((_ tuple.select 0) tuple_153) ((_ tuple.select 0) tuple_155))))) CheckTemperature)) (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_154 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 12) tuple_154) (= ((_ tuple.select 0) tuple_154) ((_ tuple.select 0) tuple_153)))) Measure))))) CheckTemperature)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_159) (+ ((_ tuple.select 0) tuple_157) 0))
rhs: (<= ((_ tuple.select 0) tuple_159) (+ ((_ tuple.select 0) tuple_157) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_159 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_157) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_159))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) TrackTime)))
rhs: (= ((_ tuple.select 0) tuple_157) ((_ tuple.select 0) tuple_158))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_162) (+ ((_ tuple.select 0) tuple_160) 0))
rhs: (<= ((_ tuple.select 0) tuple_162) (+ ((_ tuple.select 0) tuple_160) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_162 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_160) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_162))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) TrackTime))))
rhs: (= ((_ tuple.select 0) tuple_160) ((_ tuple.select 0) tuple_161))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_165) ((_ tuple.select 0) tuple_166))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_166 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_165) ((_ tuple.select 0) tuple_166))))) FoodPreparation))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_164 (Tuple Int))) true) FoodPreparation)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_165 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_166 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_165) ((_ tuple.select 0) tuple_166))))) FoodPreparation)) true)) FoodPreparation)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_169) (+ ((_ tuple.select 0) tuple_167) 0))
rhs: (<= ((_ tuple.select 0) tuple_169) (+ ((_ tuple.select 0) tuple_167) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_169 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_167) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_169))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)))
rhs: (= ((_ tuple.select 0) tuple_167) ((_ tuple.select 0) tuple_168))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_172) (+ ((_ tuple.select 0) tuple_170) 0))
rhs: (<= ((_ tuple.select 0) tuple_172) (+ ((_ tuple.select 0) tuple_170) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_172 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_170) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_172))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser))))
rhs: (= ((_ tuple.select 0) tuple_170) ((_ tuple.select 0) tuple_171))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_175) ((_ tuple.select 0) tuple_176))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_176 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_175) ((_ tuple.select 0) tuple_176))))) TrackTime))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_174 (Tuple Int))) true) TrackTime)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_175 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_176 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_175) ((_ tuple.select 0) tuple_176))))) TrackTime)) true)) TrackTime)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_179) (+ ((_ tuple.select 0) tuple_177) 0))
rhs: (<= ((_ tuple.select 0) tuple_179) (+ ((_ tuple.select 0) tuple_177) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_179 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_177) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_179))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CollectandRecordInformation)))
rhs: (= ((_ tuple.select 0) tuple_177) ((_ tuple.select 0) tuple_178))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_182) (+ ((_ tuple.select 0) tuple_180) 0))
rhs: (<= ((_ tuple.select 0) tuple_182) (+ ((_ tuple.select 0) tuple_180) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_182 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_180) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_182))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CollectandRecordInformation))))
rhs: (= ((_ tuple.select 0) tuple_180) ((_ tuple.select 0) tuple_181))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_185) ((_ tuple.select 0) tuple_186))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_186 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_185) ((_ tuple.select 0) tuple_186))))) MeetingUser))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_184 (Tuple Int))) true) MeetingUser)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_185 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_186 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_185) ((_ tuple.select 0) tuple_186))))) MeetingUser)) true)) MeetingUser)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_189) (+ ((_ tuple.select 0) tuple_187) 0))
rhs: (<= ((_ tuple.select 0) tuple_189) (+ ((_ tuple.select 0) tuple_187) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_189 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_187) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_189))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateInformation)))
rhs: (= ((_ tuple.select 0) tuple_187) ((_ tuple.select 0) tuple_188))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_192) (+ ((_ tuple.select 0) tuple_190) 0))
rhs: (<= ((_ tuple.select 0) tuple_192) (+ ((_ tuple.select 0) tuple_190) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_192 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_190) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_192))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateInformation))))
rhs: (= ((_ tuple.select 0) tuple_190) ((_ tuple.select 0) tuple_191))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_195) ((_ tuple.select 0) tuple_196))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_196 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_195) ((_ tuple.select 0) tuple_196))))) AgentDeployed))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_194 (Tuple Int))) true) AgentDeployed)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_195 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_196 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_195) ((_ tuple.select 0) tuple_196))))) AgentDeployed)) true)) AgentDeployed)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_199) (+ ((_ tuple.select 0) tuple_197) 0))
rhs: (<= ((_ tuple.select 0) tuple_199) (+ ((_ tuple.select 0) tuple_197) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_199 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_197) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_199))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ConsiderUserPractices)))
rhs: (= ((_ tuple.select 0) tuple_197) ((_ tuple.select 0) tuple_198))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_202) (+ ((_ tuple.select 0) tuple_200) 0))
rhs: (<= ((_ tuple.select 0) tuple_202) (+ ((_ tuple.select 0) tuple_200) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_202 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_200) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_202))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ConsiderUserPractices))))
rhs: (= ((_ tuple.select 0) tuple_200) ((_ tuple.select 0) tuple_201))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_205) ((_ tuple.select 0) tuple_206))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_206 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_205) ((_ tuple.select 0) tuple_206))))) GiveSuggestion))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_204 (Tuple Int))) true) GiveSuggestion)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_205 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_206 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_205) ((_ tuple.select 0) tuple_206))))) GiveSuggestion)) true)) GiveSuggestion)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_209) (+ ((_ tuple.select 0) tuple_207) 0))
rhs: (<= ((_ tuple.select 0) tuple_209) (+ ((_ tuple.select 0) tuple_207) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_209 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_207) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_209))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskForEmergencyContact)))
rhs: (= ((_ tuple.select 0) tuple_207) ((_ tuple.select 0) tuple_208))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_212) (+ ((_ tuple.select 0) tuple_210) 0))
rhs: (<= ((_ tuple.select 0) tuple_212) (+ ((_ tuple.select 0) tuple_210) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_212 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_210) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_212))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskForEmergencyContact))))
rhs: (= ((_ tuple.select 0) tuple_210) ((_ tuple.select 0) tuple_211))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_215) ((_ tuple.select 0) tuple_216))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_216 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_215) ((_ tuple.select 0) tuple_216))))) MeetingUser))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_214 (Tuple Int))) true) MeetingUser)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_215 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_216 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_215) ((_ tuple.select 0) tuple_216))))) MeetingUser)) true)) MeetingUser)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_219) (+ ((_ tuple.select 0) tuple_217) 0))
rhs: (<= ((_ tuple.select 0) tuple_219) (+ ((_ tuple.select 0) tuple_217) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_219 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_217) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_219))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)))
rhs: (= ((_ tuple.select 0) tuple_217) ((_ tuple.select 0) tuple_218))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_222) (+ ((_ tuple.select 0) tuple_220) 0))
rhs: (<= ((_ tuple.select 0) tuple_222) (+ ((_ tuple.select 0) tuple_220) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_222 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_220) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_222))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser))))
rhs: (= ((_ tuple.select 0) tuple_220) ((_ tuple.select 0) tuple_221))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_225) ((_ tuple.select 0) tuple_226))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_226 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_225) ((_ tuple.select 0) tuple_226))))) AskForEmergencyContact))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_224 (Tuple Int))) true) AskForEmergencyContact)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_225 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_226 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_225) ((_ tuple.select 0) tuple_226))))) AskForEmergencyContact)) true)) AskForEmergencyContact)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_229) (+ ((_ tuple.select 0) tuple_227) 0))
rhs: (<= ((_ tuple.select 0) tuple_229) (+ ((_ tuple.select 0) tuple_227) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_229 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_227) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_229))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ShowDataHistory))))
rhs: (not (not ((_ tuple.select 3) tuple_228)))
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (or (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_229 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_227) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_229))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ShowDataHistory)))) (not (not ((_ tuple.select 3) tuple_228))))
rhs: (= ((_ tuple.select 0) tuple_227) ((_ tuple.select 0) tuple_228))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_232) (+ ((_ tuple.select 0) tuple_230) 0))
rhs: (<= ((_ tuple.select 0) tuple_232) (+ ((_ tuple.select 0) tuple_230) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_232 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_230) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_232))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ShowDataHistory)))))
rhs: (not ((_ tuple.select 3) tuple_231))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_232 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_230) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_232))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ShowDataHistory))))) (not ((_ tuple.select 3) tuple_231)))
rhs: (= ((_ tuple.select 0) tuple_230) ((_ tuple.select 0) tuple_231))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not ((_ tuple.select 4) tuple_233))
rhs: (= ((_ tuple.select 0) tuple_233) ((_ tuple.select 1) tuple_233))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not ((_ tuple.select 3) tuple_235))
rhs: (= ((_ tuple.select 0) tuple_235) ((_ tuple.select 0) tuple_234))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not ((_ tuple.select 3) tuple_237))
rhs: (= ((_ tuple.select 0) tuple_237) ((_ tuple.select 0) tuple_236))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not ((_ tuple.select 3) tuple_239))
rhs: (= ((_ tuple.select 0) tuple_239) ((_ tuple.select 0) tuple_238))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_239 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 3) tuple_239)) (= ((_ tuple.select 0) tuple_239) ((_ tuple.select 0) tuple_238)))) Measure)))
rhs: (>= ((_ tuple.select 0) tuple_236) ((_ tuple.select 0) tuple_238))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_238 (Tuple Int))) (not (=> (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_239 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 3) tuple_239)) (= ((_ tuple.select 0) tuple_239) ((_ tuple.select 0) tuple_238)))) Measure))) (>= ((_ tuple.select 0) tuple_236) ((_ tuple.select 0) tuple_238))))) AgentDeployed))
rhs: (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_237 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 3) tuple_237)) (= ((_ tuple.select 0) tuple_237) ((_ tuple.select 0) tuple_236)))) Measure)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_234 (Tuple Int))) (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_235 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 3) tuple_235)) (= ((_ tuple.select 0) tuple_235) ((_ tuple.select 0) tuple_234)))) Measure)))) AgentDeployed)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_236 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_238 (Tuple Int))) (not (=> (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_239 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 3) tuple_239)) (= ((_ tuple.select 0) tuple_239) ((_ tuple.select 0) tuple_238)))) Measure))) (>= ((_ tuple.select 0) tuple_236) ((_ tuple.select 0) tuple_238))))) AgentDeployed)) (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_237 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 3) tuple_237)) (= ((_ tuple.select 0) tuple_237) ((_ tuple.select 0) tuple_236)))) Measure))))) AgentDeployed)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_242) (+ ((_ tuple.select 0) tuple_240) 0))
rhs: (<= ((_ tuple.select 0) tuple_242) (+ ((_ tuple.select 0) tuple_240) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_242 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_240) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_242))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ProvideDataSummaries)))
rhs: (not ((_ tuple.select 4) tuple_241))
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (or (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_242 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_240) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_242))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ProvideDataSummaries))) (not ((_ tuple.select 4) tuple_241)))
rhs: (= ((_ tuple.select 0) tuple_240) ((_ tuple.select 0) tuple_241))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_245) (+ ((_ tuple.select 0) tuple_243) 0))
rhs: (<= ((_ tuple.select 0) tuple_245) (+ ((_ tuple.select 0) tuple_243) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_245 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_243) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_245))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ProvideDataSummaries))))
rhs: ((_ tuple.select 4) tuple_244)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_245 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_243) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_245))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ProvideDataSummaries)))) ((_ tuple.select 4) tuple_244))
rhs: (= ((_ tuple.select 0) tuple_243) ((_ tuple.select 0) tuple_244))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: ((_ tuple.select 5) tuple_246)
rhs: (= ((_ tuple.select 0) tuple_246) ((_ tuple.select 1) tuple_246))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: ((_ tuple.select 4) tuple_248)
rhs: (= ((_ tuple.select 0) tuple_248) ((_ tuple.select 0) tuple_247))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: ((_ tuple.select 4) tuple_250)
rhs: (= ((_ tuple.select 0) tuple_250) ((_ tuple.select 0) tuple_249))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: ((_ tuple.select 4) tuple_252)
rhs: (= ((_ tuple.select 0) tuple_252) ((_ tuple.select 0) tuple_251))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_252 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 4) tuple_252) (= ((_ tuple.select 0) tuple_252) ((_ tuple.select 0) tuple_251)))) Measure)))
rhs: (>= ((_ tuple.select 0) tuple_249) ((_ tuple.select 0) tuple_251))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_251 (Tuple Int))) (not (=> (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_252 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 4) tuple_252) (= ((_ tuple.select 0) tuple_252) ((_ tuple.select 0) tuple_251)))) Measure))) (>= ((_ tuple.select 0) tuple_249) ((_ tuple.select 0) tuple_251))))) ShowDataHistory))
rhs: (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_250 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 4) tuple_250) (= ((_ tuple.select 0) tuple_250) ((_ tuple.select 0) tuple_249)))) Measure)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_247 (Tuple Int))) (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_248 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 4) tuple_248) (= ((_ tuple.select 0) tuple_248) ((_ tuple.select 0) tuple_247)))) Measure)))) ShowDataHistory)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_249 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_251 (Tuple Int))) (not (=> (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_252 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 4) tuple_252) (= ((_ tuple.select 0) tuple_252) ((_ tuple.select 0) tuple_251)))) Measure))) (>= ((_ tuple.select 0) tuple_249) ((_ tuple.select 0) tuple_251))))) ShowDataHistory)) (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_250 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 4) tuple_250) (= ((_ tuple.select 0) tuple_250) ((_ tuple.select 0) tuple_249)))) Measure))))) ShowDataHistory)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_255) (+ ((_ tuple.select 0) tuple_253) 0))
rhs: (<= ((_ tuple.select 0) tuple_255) (+ ((_ tuple.select 0) tuple_253) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_255 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_253) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_255))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) GiveUserDangerousObjects))))
rhs: (= ((_ tuple.select 0) tuple_253) ((_ tuple.select 0) tuple_254))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_258) (+ ((_ tuple.select 0) tuple_256) 0))
rhs: (<= ((_ tuple.select 0) tuple_258) (+ ((_ tuple.select 0) tuple_256) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_258 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_256) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_258))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) GiveUserDangerousObjects)))))
rhs: (= ((_ tuple.select 0) tuple_256) ((_ tuple.select 0) tuple_257))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_261) ((_ tuple.select 0) tuple_262))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_262 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_261) ((_ tuple.select 0) tuple_262))))) UserUnpredictable))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_260 (Tuple Int))) true) UserUnpredictable)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_261 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_262 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_261) ((_ tuple.select 0) tuple_262))))) UserUnpredictable)) true)) UserUnpredictable)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_265) (+ ((_ tuple.select 0) tuple_263) 0))
rhs: (<= ((_ tuple.select 0) tuple_265) (+ ((_ tuple.select 0) tuple_263) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (> ((_ tuple.select 9) tuple_264) 1)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (> ((_ tuple.select 9) tuple_264) 1) true)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (> ((_ tuple.select 9) tuple_264) 1))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (and (not (> ((_ tuple.select 9) tuple_264) 1)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and true (and (not (> ((_ tuple.select 9) tuple_264) 1)) true))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_265 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_263) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_265))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindUserOfLimitations)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not (> ((_ tuple.select 9) tuple_264) 1)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not (> ((_ tuple.select 9) tuple_264) 1)) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_265 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_263) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_265))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindUserOfLimitations))))
rhs: (=> (and (> ((_ tuple.select 9) tuple_264) 1) true) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 (> ((_ tuple.select 9) tuple_264) 1))) (and (=> (and true (and (not _let_1) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_265 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_263) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_265))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindUserOfLimitations)))) (=> (and _let_1 true) true)))
rhs: (not (not ((_ tuple.select 5) tuple_264)))
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (let ((_let_1 (> ((_ tuple.select 9) tuple_264) 1))) (or (and (=> (and true (and (not _let_1) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_265 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_263) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_265))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindUserOfLimitations)))) (=> (and _let_1 true) true)) (not (not ((_ tuple.select 5) tuple_264)))))
rhs: (= ((_ tuple.select 0) tuple_263) ((_ tuple.select 0) tuple_264))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_268) (+ ((_ tuple.select 0) tuple_266) 0))
rhs: (<= ((_ tuple.select 0) tuple_268) (+ ((_ tuple.select 0) tuple_266) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (> ((_ tuple.select 9) tuple_267) 1)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (> ((_ tuple.select 9) tuple_267) 1) true)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (> ((_ tuple.select 9) tuple_267) 1))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (and (not (> ((_ tuple.select 9) tuple_267) 1)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and true (and (not (> ((_ tuple.select 9) tuple_267) 1)) true))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_268 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_266) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_268))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindUserOfLimitations)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not (> ((_ tuple.select 9) tuple_267) 1)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not (> ((_ tuple.select 9) tuple_267) 1)) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_268 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_266) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_268))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindUserOfLimitations))))
rhs: (=> (and (> ((_ tuple.select 9) tuple_267) 1) true) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 (> ((_ tuple.select 9) tuple_267) 1))) (not (and (=> (and true (and (not _let_1) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_268 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_266) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_268))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindUserOfLimitations)))) (=> (and _let_1 true) true))))
rhs: (not ((_ tuple.select 5) tuple_267))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 (> ((_ tuple.select 9) tuple_267) 1))) (and (not (and (=> (and true (and (not _let_1) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_268 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_266) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_268))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindUserOfLimitations)))) (=> (and _let_1 true) true))) (not ((_ tuple.select 5) tuple_267))))
rhs: (= ((_ tuple.select 0) tuple_266) ((_ tuple.select 0) tuple_267))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not ((_ tuple.select 6) tuple_269))
rhs: (= ((_ tuple.select 0) tuple_269) ((_ tuple.select 1) tuple_269))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not ((_ tuple.select 5) tuple_271))
rhs: (= ((_ tuple.select 0) tuple_271) ((_ tuple.select 0) tuple_270))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not ((_ tuple.select 5) tuple_273))
rhs: (= ((_ tuple.select 0) tuple_273) ((_ tuple.select 0) tuple_272))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not ((_ tuple.select 5) tuple_275))
rhs: (= ((_ tuple.select 0) tuple_275) ((_ tuple.select 0) tuple_274))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_275 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 5) tuple_275)) (= ((_ tuple.select 0) tuple_275) ((_ tuple.select 0) tuple_274)))) Measure)))
rhs: (>= ((_ tuple.select 0) tuple_272) ((_ tuple.select 0) tuple_274))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_274 (Tuple Int))) (not (=> (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_275 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 5) tuple_275)) (= ((_ tuple.select 0) tuple_275) ((_ tuple.select 0) tuple_274)))) Measure))) (>= ((_ tuple.select 0) tuple_272) ((_ tuple.select 0) tuple_274))))) AgentDeployed))
rhs: (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_273 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 5) tuple_273)) (= ((_ tuple.select 0) tuple_273) ((_ tuple.select 0) tuple_272)))) Measure)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_270 (Tuple Int))) (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_271 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 5) tuple_271)) (= ((_ tuple.select 0) tuple_271) ((_ tuple.select 0) tuple_270)))) Measure)))) AgentDeployed)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_272 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_274 (Tuple Int))) (not (=> (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_275 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 5) tuple_275)) (= ((_ tuple.select 0) tuple_275) ((_ tuple.select 0) tuple_274)))) Measure))) (>= ((_ tuple.select 0) tuple_272) ((_ tuple.select 0) tuple_274))))) AgentDeployed)) (not (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_273 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 5) tuple_273)) (= ((_ tuple.select 0) tuple_273) ((_ tuple.select 0) tuple_272)))) Measure))))) AgentDeployed)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_278) (+ ((_ tuple.select 0) tuple_276) 0))
rhs: (<= ((_ tuple.select 0) tuple_278) (+ ((_ tuple.select 0) tuple_276) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: ((_ tuple.select 6) tuple_277)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and ((_ tuple.select 6) tuple_277) true)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not ((_ tuple.select 6) tuple_277))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (and (not ((_ tuple.select 6) tuple_277)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and true (and (not ((_ tuple.select 6) tuple_277)) true))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_278 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_276) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_278))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AgentHasAppropriateAppearance)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not ((_ tuple.select 6) tuple_277)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not ((_ tuple.select 6) tuple_277)) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_278 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_276) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_278))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AgentHasAppropriateAppearance))))
rhs: (=> (and ((_ tuple.select 6) tuple_277) true) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 ((_ tuple.select 6) tuple_277))) (and (=> (and true (and (not _let_1) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_278 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_276) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_278))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AgentHasAppropriateAppearance)))) (=> (and _let_1 true) true)))
rhs: (= ((_ tuple.select 0) tuple_276) ((_ tuple.select 0) tuple_277))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_281) (+ ((_ tuple.select 0) tuple_279) 0))
rhs: (<= ((_ tuple.select 0) tuple_281) (+ ((_ tuple.select 0) tuple_279) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: ((_ tuple.select 6) tuple_280)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and ((_ tuple.select 6) tuple_280) true)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not ((_ tuple.select 6) tuple_280))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (and (not ((_ tuple.select 6) tuple_280)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and true (and (not ((_ tuple.select 6) tuple_280)) true))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_281 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_279) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_281))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AgentHasAppropriateAppearance)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not ((_ tuple.select 6) tuple_280)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not ((_ tuple.select 6) tuple_280)) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_281 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_279) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_281))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AgentHasAppropriateAppearance))))
rhs: (=> (and ((_ tuple.select 6) tuple_280) true) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 ((_ tuple.select 6) tuple_280))) (not (and (=> (and true (and (not _let_1) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_281 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_279) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_281))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AgentHasAppropriateAppearance)))) (=> (and _let_1 true) true))))
rhs: (= ((_ tuple.select 0) tuple_279) ((_ tuple.select 0) tuple_280))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_284) ((_ tuple.select 0) tuple_285))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_285 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_284) ((_ tuple.select 0) tuple_285))))) PreparingDeployment))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_283 (Tuple Int))) true) PreparingDeployment)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_284 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_285 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_284) ((_ tuple.select 0) tuple_285))))) PreparingDeployment)) true)) PreparingDeployment)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_288) (+ ((_ tuple.select 0) tuple_286) 0))
rhs: (<= ((_ tuple.select 0) tuple_288) (+ ((_ tuple.select 0) tuple_286) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_288 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_286) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_288))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CalibrateSpeech)))
rhs: (= ((_ tuple.select 0) tuple_286) ((_ tuple.select 0) tuple_287))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_291) (+ ((_ tuple.select 0) tuple_289) 0))
rhs: (<= ((_ tuple.select 0) tuple_291) (+ ((_ tuple.select 0) tuple_289) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_291 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_289) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_291))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CalibrateSpeech))))
rhs: (= ((_ tuple.select 0) tuple_289) ((_ tuple.select 0) tuple_290))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_294) ((_ tuple.select 0) tuple_295))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_295 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_294) ((_ tuple.select 0) tuple_295))))) PreparingDeployment))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_293 (Tuple Int))) true) PreparingDeployment)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_294 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_295 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_294) ((_ tuple.select 0) tuple_295))))) PreparingDeployment)) true)) PreparingDeployment)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_298) (+ ((_ tuple.select 0) tuple_296) 0))
rhs: (<= ((_ tuple.select 0) tuple_298) (+ ((_ tuple.select 0) tuple_296) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_298 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_296) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_298))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UseFirstPersonPluralLanguage)))
rhs: (= ((_ tuple.select 0) tuple_296) ((_ tuple.select 0) tuple_297))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_301) (+ ((_ tuple.select 0) tuple_299) 0))
rhs: (<= ((_ tuple.select 0) tuple_301) (+ ((_ tuple.select 0) tuple_299) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_301 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_299) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_301))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UseFirstPersonPluralLanguage))))
rhs: (= ((_ tuple.select 0) tuple_299) ((_ tuple.select 0) tuple_300))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_304) ((_ tuple.select 0) tuple_305))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_305 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_304) ((_ tuple.select 0) tuple_305))))) GivingCookingInstructions))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_303 (Tuple Int))) true) GivingCookingInstructions)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_304 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_305 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_304) ((_ tuple.select 0) tuple_305))))) GivingCookingInstructions)) true)) GivingCookingInstructions)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_308) (+ ((_ tuple.select 0) tuple_306) 0))
rhs: (<= ((_ tuple.select 0) tuple_308) (+ ((_ tuple.select 0) tuple_306) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_308 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_306) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_308))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)))
rhs: (= ((_ tuple.select 0) tuple_306) ((_ tuple.select 0) tuple_307))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_311) (+ ((_ tuple.select 0) tuple_309) 0))
rhs: (<= ((_ tuple.select 0) tuple_311) (+ ((_ tuple.select 0) tuple_309) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_311 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_309) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_311))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser))))
rhs: (= ((_ tuple.select 0) tuple_309) ((_ tuple.select 0) tuple_310))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_314) ((_ tuple.select 0) tuple_315))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_315 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_314) ((_ tuple.select 0) tuple_315))))) GivingCookingInstructions))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_313 (Tuple Int))) true) GivingCookingInstructions)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_314 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_315 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_314) ((_ tuple.select 0) tuple_315))))) GivingCookingInstructions)) true)) GivingCookingInstructions)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_318) (+ ((_ tuple.select 0) tuple_316) 0))
rhs: (<= ((_ tuple.select 0) tuple_318) (+ ((_ tuple.select 0) tuple_316) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_318 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_316) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_318))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskForDetailLevelOfInstructions)))
rhs: (= ((_ tuple.select 0) tuple_316) ((_ tuple.select 0) tuple_317))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_321) (+ ((_ tuple.select 0) tuple_319) 0))
rhs: (<= ((_ tuple.select 0) tuple_321) (+ ((_ tuple.select 0) tuple_319) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_321 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_319) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_321))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskForDetailLevelOfInstructions))))
rhs: (= ((_ tuple.select 0) tuple_319) ((_ tuple.select 0) tuple_320))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_324) ((_ tuple.select 0) tuple_325))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_325 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_324) ((_ tuple.select 0) tuple_325))))) BeforeCookingBegins))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_323 (Tuple Int))) true) BeforeCookingBegins)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_324 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_325 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_324) ((_ tuple.select 0) tuple_325))))) BeforeCookingBegins)) true)) BeforeCookingBegins)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_328) (+ ((_ tuple.select 0) tuple_326) 0))
rhs: (<= ((_ tuple.select 0) tuple_328) (+ ((_ tuple.select 0) tuple_326) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 14) tuple_327) 2)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (= ((_ tuple.select 14) tuple_327) 2) true)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= ((_ tuple.select 14) tuple_327) 2))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (and (not (= ((_ tuple.select 14) tuple_327) 2)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and true (and (not (= ((_ tuple.select 14) tuple_327) 2)) true))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_328 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_326) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_328))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RecalculateApproach)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not (= ((_ tuple.select 14) tuple_327) 2)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not (= ((_ tuple.select 14) tuple_327) 2)) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_328 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_326) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_328))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RecalculateApproach))))
rhs: (=> (and (= ((_ tuple.select 14) tuple_327) 2) true) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 (= ((_ tuple.select 14) tuple_327) 2))) (and (=> (and true (and (not _let_1) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_328 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_326) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_328))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RecalculateApproach)))) (=> (and _let_1 true) true)))
rhs: (= ((_ tuple.select 0) tuple_326) ((_ tuple.select 0) tuple_327))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_331) (+ ((_ tuple.select 0) tuple_329) 0))
rhs: (<= ((_ tuple.select 0) tuple_331) (+ ((_ tuple.select 0) tuple_329) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 14) tuple_330) 2)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (= ((_ tuple.select 14) tuple_330) 2) true)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= ((_ tuple.select 14) tuple_330) 2))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (and (not (= ((_ tuple.select 14) tuple_330) 2)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and true (and (not (= ((_ tuple.select 14) tuple_330) 2)) true))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_331 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_329) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_331))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RecalculateApproach)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not (= ((_ tuple.select 14) tuple_330) 2)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not (= ((_ tuple.select 14) tuple_330) 2)) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_331 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_329) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_331))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RecalculateApproach))))
rhs: (=> (and (= ((_ tuple.select 14) tuple_330) 2) true) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 (= ((_ tuple.select 14) tuple_330) 2))) (not (and (=> (and true (and (not _let_1) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_331 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_329) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_331))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RecalculateApproach)))) (=> (and _let_1 true) true))))
rhs: (= ((_ tuple.select 0) tuple_329) ((_ tuple.select 0) tuple_330))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_334) ((_ tuple.select 0) tuple_335))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_335 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_334) ((_ tuple.select 0) tuple_335))))) UserChangeMind))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_333 (Tuple Int))) true) UserChangeMind)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_334 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_335 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_334) ((_ tuple.select 0) tuple_335))))) UserChangeMind)) true)) UserChangeMind)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_338) (+ ((_ tuple.select 0) tuple_336) 0))
rhs: (<= ((_ tuple.select 0) tuple_338) (+ ((_ tuple.select 0) tuple_336) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_339) (+ ((_ tuple.select 0) tuple_336) 0))
rhs: (<= ((_ tuple.select 0) tuple_339) (+ ((_ tuple.select 0) tuple_336) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 14) tuple_337) 2)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (= ((_ tuple.select 14) tuple_337) 2) true)
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_339 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_336) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_339))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= ((_ tuple.select 14) tuple_337) 2))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (and (not (= ((_ tuple.select 14) tuple_337) 2)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and true (and (not (= ((_ tuple.select 14) tuple_337) 2)) true))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_338 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_336) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_338))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateMap)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not (= ((_ tuple.select 14) tuple_337) 2)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not (= ((_ tuple.select 14) tuple_337) 2)) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_338 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_336) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_338))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateMap))))
rhs: (=> (and (= ((_ tuple.select 14) tuple_337) 2) true) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_339 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_336) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_339))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely))))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 (= ((_ tuple.select 14) tuple_337) 2))) (and (=> (and true (and (not _let_1) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_338 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_336) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_338))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateMap)))) (=> (and _let_1 true) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_339 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_336) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_339))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely))))))
rhs: (= ((_ tuple.select 0) tuple_336) ((_ tuple.select 0) tuple_337))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_342) (+ ((_ tuple.select 0) tuple_340) 0))
rhs: (<= ((_ tuple.select 0) tuple_342) (+ ((_ tuple.select 0) tuple_340) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_343) (+ ((_ tuple.select 0) tuple_340) 0))
rhs: (<= ((_ tuple.select 0) tuple_343) (+ ((_ tuple.select 0) tuple_340) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 14) tuple_341) 2)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (= ((_ tuple.select 14) tuple_341) 2) true)
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_343 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_340) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_343))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= ((_ tuple.select 14) tuple_341) 2))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (and (not (= ((_ tuple.select 14) tuple_341) 2)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and true (and (not (= ((_ tuple.select 14) tuple_341) 2)) true))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_342 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_340) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_342))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateMap)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not (= ((_ tuple.select 14) tuple_341) 2)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not (= ((_ tuple.select 14) tuple_341) 2)) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_342 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_340) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_342))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateMap))))
rhs: (=> (and (= ((_ tuple.select 14) tuple_341) 2) true) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_343 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_340) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_343))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely))))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 (= ((_ tuple.select 14) tuple_341) 2))) (not (and (=> (and true (and (not _let_1) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_342 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_340) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_342))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateMap)))) (=> (and _let_1 true) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_343 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_340) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_343))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely)))))))
rhs: (= ((_ tuple.select 0) tuple_340) ((_ tuple.select 0) tuple_341))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_346) ((_ tuple.select 0) tuple_347))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_347 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_346) ((_ tuple.select 0) tuple_347))))) UserChangeItemLocation))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_345 (Tuple Int))) true) UserChangeItemLocation)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_346 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_347 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_346) ((_ tuple.select 0) tuple_347))))) UserChangeItemLocation)) true)) UserChangeItemLocation)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_350) (+ ((_ tuple.select 0) tuple_348) 0))
rhs: (<= ((_ tuple.select 0) tuple_350) (+ ((_ tuple.select 0) tuple_348) 300))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not ((_ tuple.select 8) tuple_349))
rhs: ((_ tuple.select 7) tuple_349)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_351) (+ ((_ tuple.select 0) tuple_348) 0))
rhs: (<= ((_ tuple.select 0) tuple_351) (+ ((_ tuple.select 0) tuple_348) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not ((_ tuple.select 8) tuple_349)) ((_ tuple.select 7) tuple_349))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (and (not ((_ tuple.select 8) tuple_349)) ((_ tuple.select 7) tuple_349)) true)
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_351 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_348) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_351))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (and (not ((_ tuple.select 8) tuple_349)) ((_ tuple.select 7) tuple_349)))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (and (not (and (not ((_ tuple.select 8) tuple_349)) ((_ tuple.select 7) tuple_349))) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and true (and (not (and (not ((_ tuple.select 8) tuple_349)) ((_ tuple.select 7) tuple_349))) true))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_350 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_348))) (let ((_let_2 ((_ tuple.select 0) tuple_350))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 300)))))) CallEmergencyServices)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not (and (not ((_ tuple.select 8) tuple_349)) ((_ tuple.select 7) tuple_349))) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not (and (not ((_ tuple.select 8) tuple_349)) ((_ tuple.select 7) tuple_349))) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_350 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_348))) (let ((_let_2 ((_ tuple.select 0) tuple_350))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 300)))))) CallEmergencyServices))))
rhs: (=> (and (and (not ((_ tuple.select 8) tuple_349)) ((_ tuple.select 7) tuple_349)) true) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_351 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_348) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_351))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures))))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 (and (not ((_ tuple.select 8) tuple_349)) ((_ tuple.select 7) tuple_349)))) (and (=> (and true (and (not _let_1) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_350 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_348))) (let ((_let_2 ((_ tuple.select 0) tuple_350))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 300)))))) CallEmergencyServices)))) (=> (and _let_1 true) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_351 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_348) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_351))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures))))))
rhs: (= ((_ tuple.select 0) tuple_348) ((_ tuple.select 0) tuple_349))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_354) (+ ((_ tuple.select 0) tuple_352) 0))
rhs: (<= ((_ tuple.select 0) tuple_354) (+ ((_ tuple.select 0) tuple_352) 300))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not ((_ tuple.select 8) tuple_353))
rhs: ((_ tuple.select 7) tuple_353)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_355) (+ ((_ tuple.select 0) tuple_352) 0))
rhs: (<= ((_ tuple.select 0) tuple_355) (+ ((_ tuple.select 0) tuple_352) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not ((_ tuple.select 8) tuple_353)) ((_ tuple.select 7) tuple_353))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (and (not ((_ tuple.select 8) tuple_353)) ((_ tuple.select 7) tuple_353)) true)
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_355 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_352) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_355))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (and (not ((_ tuple.select 8) tuple_353)) ((_ tuple.select 7) tuple_353)))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (and (not (and (not ((_ tuple.select 8) tuple_353)) ((_ tuple.select 7) tuple_353))) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and true (and (not (and (not ((_ tuple.select 8) tuple_353)) ((_ tuple.select 7) tuple_353))) true))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_354 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_352))) (let ((_let_2 ((_ tuple.select 0) tuple_354))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 300)))))) CallEmergencyServices)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not (and (not ((_ tuple.select 8) tuple_353)) ((_ tuple.select 7) tuple_353))) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not (and (not ((_ tuple.select 8) tuple_353)) ((_ tuple.select 7) tuple_353))) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_354 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_352))) (let ((_let_2 ((_ tuple.select 0) tuple_354))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 300)))))) CallEmergencyServices))))
rhs: (=> (and (and (not ((_ tuple.select 8) tuple_353)) ((_ tuple.select 7) tuple_353)) true) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_355 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_352) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_355))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures))))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 (and (not ((_ tuple.select 8) tuple_353)) ((_ tuple.select 7) tuple_353)))) (not (and (=> (and true (and (not _let_1) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_354 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_352))) (let ((_let_2 ((_ tuple.select 0) tuple_354))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 300)))))) CallEmergencyServices)))) (=> (and _let_1 true) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_355 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_352) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_355))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures)))))))
rhs: (= ((_ tuple.select 0) tuple_352) ((_ tuple.select 0) tuple_353))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_358) ((_ tuple.select 0) tuple_359))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_359 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_358) ((_ tuple.select 0) tuple_359))))) SmokeDetectorAlarm))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_357 (Tuple Int))) true) SmokeDetectorAlarm)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_358 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_359 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_358) ((_ tuple.select 0) tuple_359))))) SmokeDetectorAlarm)) true)) SmokeDetectorAlarm)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_362) (+ ((_ tuple.select 0) tuple_360) 0))
rhs: (<= ((_ tuple.select 0) tuple_362) (+ ((_ tuple.select 0) tuple_360) 120))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not ((_ tuple.select 8) tuple_361))
rhs: ((_ tuple.select 7) tuple_361)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_363) (+ ((_ tuple.select 0) tuple_360) 0))
rhs: (<= ((_ tuple.select 0) tuple_363) (+ ((_ tuple.select 0) tuple_360) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not ((_ tuple.select 8) tuple_361)) ((_ tuple.select 7) tuple_361))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (and (not ((_ tuple.select 8) tuple_361)) ((_ tuple.select 7) tuple_361)) true)
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_363 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_360) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_363))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (and (not ((_ tuple.select 8) tuple_361)) ((_ tuple.select 7) tuple_361)))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (and (not (and (not ((_ tuple.select 8) tuple_361)) ((_ tuple.select 7) tuple_361))) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and true (and (not (and (not ((_ tuple.select 8) tuple_361)) ((_ tuple.select 7) tuple_361))) true))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_362 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_360))) (let ((_let_2 ((_ tuple.select 0) tuple_362))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 120)))))) CallEmergencyServices)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not (and (not ((_ tuple.select 8) tuple_361)) ((_ tuple.select 7) tuple_361))) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not (and (not ((_ tuple.select 8) tuple_361)) ((_ tuple.select 7) tuple_361))) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_362 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_360))) (let ((_let_2 ((_ tuple.select 0) tuple_362))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 120)))))) CallEmergencyServices))))
rhs: (=> (and (and (not ((_ tuple.select 8) tuple_361)) ((_ tuple.select 7) tuple_361)) true) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_363 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_360) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_363))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures))))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 (and (not ((_ tuple.select 8) tuple_361)) ((_ tuple.select 7) tuple_361)))) (and (=> (and true (and (not _let_1) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_362 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_360))) (let ((_let_2 ((_ tuple.select 0) tuple_362))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 120)))))) CallEmergencyServices)))) (=> (and _let_1 true) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_363 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_360) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_363))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures))))))
rhs: (= ((_ tuple.select 0) tuple_360) ((_ tuple.select 0) tuple_361))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_366) (+ ((_ tuple.select 0) tuple_364) 0))
rhs: (<= ((_ tuple.select 0) tuple_366) (+ ((_ tuple.select 0) tuple_364) 120))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not ((_ tuple.select 8) tuple_365))
rhs: ((_ tuple.select 7) tuple_365)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_367) (+ ((_ tuple.select 0) tuple_364) 0))
rhs: (<= ((_ tuple.select 0) tuple_367) (+ ((_ tuple.select 0) tuple_364) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not ((_ tuple.select 8) tuple_365)) ((_ tuple.select 7) tuple_365))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (and (not ((_ tuple.select 8) tuple_365)) ((_ tuple.select 7) tuple_365)) true)
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_367 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_364) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_367))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (and (not ((_ tuple.select 8) tuple_365)) ((_ tuple.select 7) tuple_365)))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (and (not (and (not ((_ tuple.select 8) tuple_365)) ((_ tuple.select 7) tuple_365))) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and true (and (not (and (not ((_ tuple.select 8) tuple_365)) ((_ tuple.select 7) tuple_365))) true))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_366 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_364))) (let ((_let_2 ((_ tuple.select 0) tuple_366))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 120)))))) CallEmergencyServices)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not (and (not ((_ tuple.select 8) tuple_365)) ((_ tuple.select 7) tuple_365))) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not (and (not ((_ tuple.select 8) tuple_365)) ((_ tuple.select 7) tuple_365))) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_366 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_364))) (let ((_let_2 ((_ tuple.select 0) tuple_366))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 120)))))) CallEmergencyServices))))
rhs: (=> (and (and (not ((_ tuple.select 8) tuple_365)) ((_ tuple.select 7) tuple_365)) true) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_367 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_364) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_367))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures))))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 (and (not ((_ tuple.select 8) tuple_365)) ((_ tuple.select 7) tuple_365)))) (not (and (=> (and true (and (not _let_1) true)) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_366 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_364))) (let ((_let_2 ((_ tuple.select 0) tuple_366))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 120)))))) CallEmergencyServices)))) (=> (and _let_1 true) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_367 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_364) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_367))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures)))))))
rhs: (= ((_ tuple.select 0) tuple_364) ((_ tuple.select 0) tuple_365))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_370) ((_ tuple.select 0) tuple_371))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_371 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_370) ((_ tuple.select 0) tuple_371))))) SmokeDetectorAlarm))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_369 (Tuple Int))) true) SmokeDetectorAlarm)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_370 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_371 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_370) ((_ tuple.select 0) tuple_371))))) SmokeDetectorAlarm)) true)) SmokeDetectorAlarm)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_374) (+ ((_ tuple.select 0) tuple_372) 0))
rhs: (<= ((_ tuple.select 0) tuple_374) (+ ((_ tuple.select 0) tuple_372) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_374 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_372) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_374))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) OpenWindows)))
rhs: (= ((_ tuple.select 0) tuple_372) ((_ tuple.select 0) tuple_373))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_377) (+ ((_ tuple.select 0) tuple_375) 0))
rhs: (<= ((_ tuple.select 0) tuple_377) (+ ((_ tuple.select 0) tuple_375) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_377 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_375) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_377))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) OpenWindows))))
rhs: (= ((_ tuple.select 0) tuple_375) ((_ tuple.select 0) tuple_376))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_380) ((_ tuple.select 0) tuple_381))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_381 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_380) ((_ tuple.select 0) tuple_381))))) FireSafetyMeasures))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_379 (Tuple Int))) true) FireSafetyMeasures)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_380 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_381 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_380) ((_ tuple.select 0) tuple_381))))) FireSafetyMeasures)) true)) FireSafetyMeasures)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_384) (+ ((_ tuple.select 0) tuple_382) 0))
rhs: (<= ((_ tuple.select 0) tuple_384) (+ ((_ tuple.select 0) tuple_382) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_384 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_382) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_384))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskUserIfOK)))
rhs: (= ((_ tuple.select 0) tuple_382) ((_ tuple.select 0) tuple_383))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_387) (+ ((_ tuple.select 0) tuple_385) 0))
rhs: (<= ((_ tuple.select 0) tuple_387) (+ ((_ tuple.select 0) tuple_385) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_387 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_385) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_387))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskUserIfOK))))
rhs: (= ((_ tuple.select 0) tuple_385) ((_ tuple.select 0) tuple_386))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_390) ((_ tuple.select 0) tuple_391))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_391 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_390) ((_ tuple.select 0) tuple_391))))) FireSafetyMeasures))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_389 (Tuple Int))) true) FireSafetyMeasures)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_390 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_391 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_390) ((_ tuple.select 0) tuple_391))))) FireSafetyMeasures)) true)) FireSafetyMeasures)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_394) (+ ((_ tuple.select 0) tuple_392) 0))
rhs: (<= ((_ tuple.select 0) tuple_394) (+ ((_ tuple.select 0) tuple_392) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_394 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_392) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_394))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver)))
rhs: (= ((_ tuple.select 0) tuple_392) ((_ tuple.select 0) tuple_393))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_397) (+ ((_ tuple.select 0) tuple_395) 0))
rhs: (<= ((_ tuple.select 0) tuple_397) (+ ((_ tuple.select 0) tuple_395) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_397 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_395) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_397))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver))))
rhs: (= ((_ tuple.select 0) tuple_395) ((_ tuple.select 0) tuple_396))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_400) ((_ tuple.select 0) tuple_401))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_401 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_400) ((_ tuple.select 0) tuple_401))))) FireSafetyMeasures))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_399 (Tuple Int))) true) FireSafetyMeasures)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_400 (Tuple Int))) (and (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_401 (Tuple Int))) (not (=> true (>= ((_ tuple.select 0) tuple_400) ((_ tuple.select 0) tuple_401))))) FireSafetyMeasures)) true)) FireSafetyMeasures)))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (= ((_ tuple.select 14) tuple_403) 2)
rhs: ((_ tuple.select 12) tuple_403)
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (>= ((_ tuple.select 0) tuple_404) (+ ((_ tuple.select 0) tuple_402) 0))
rhs: (<= ((_ tuple.select 0) tuple_404) (+ ((_ tuple.select 0) tuple_402) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_404 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_402) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_404))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely))))
rhs: (or (= ((_ tuple.select 14) tuple_403) 2) ((_ tuple.select 12) tuple_403))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_404 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_402) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_404))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely)))) (or (= ((_ tuple.select 14) tuple_403) 2) ((_ tuple.select 12) tuple_403)))
rhs: (= ((_ tuple.select 0) tuple_402) ((_ tuple.select 0) tuple_403))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_407) (+ ((_ tuple.select 0) tuple_405) 0))
rhs: (<= ((_ tuple.select 0) tuple_407) (+ ((_ tuple.select 0) tuple_405) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_407 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_405) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_407))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser))))
rhs: ((_ tuple.select 12) tuple_406)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_407 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_405) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_407))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)))) ((_ tuple.select 12) tuple_406))
rhs: (= ((_ tuple.select 0) tuple_405) ((_ tuple.select 0) tuple_406))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: ((_ tuple.select 8) tuple_409)
rhs: (not ((_ tuple.select 7) tuple_409))
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (>= ((_ tuple.select 0) tuple_410) (+ ((_ tuple.select 0) tuple_408) 0))
rhs: (<= ((_ tuple.select 0) tuple_410) (+ ((_ tuple.select 0) tuple_408) 120))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_410 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_408))) (let ((_let_2 ((_ tuple.select 0) tuple_410))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 120)))))) CallEmergencyServices))))
rhs: (or ((_ tuple.select 8) tuple_409) (not ((_ tuple.select 7) tuple_409)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_410 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_408))) (let ((_let_2 ((_ tuple.select 0) tuple_410))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 120)))))) CallEmergencyServices)))) (or ((_ tuple.select 8) tuple_409) (not ((_ tuple.select 7) tuple_409))))
rhs: (= ((_ tuple.select 0) tuple_408) ((_ tuple.select 0) tuple_409))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_413) (+ ((_ tuple.select 0) tuple_411) 0))
rhs: (<= ((_ tuple.select 0) tuple_413) (+ ((_ tuple.select 0) tuple_411) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_413 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_411) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_413))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) OpenWindows))))
rhs: (= ((_ tuple.select 0) tuple_411) ((_ tuple.select 0) tuple_412))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_416) (+ ((_ tuple.select 0) tuple_414) 0))
rhs: (<= ((_ tuple.select 0) tuple_416) (+ ((_ tuple.select 0) tuple_414) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_416 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_414) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_416))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AllowUserToCook))))
rhs: (= ((_ tuple.select 0) tuple_414) ((_ tuple.select 0) tuple_415))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_419) (+ ((_ tuple.select 0) tuple_417) 0))
rhs: (<= ((_ tuple.select 0) tuple_419) (+ ((_ tuple.select 0) tuple_417) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_419 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_417) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_419))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UseFirstPersonPluralLanguage))))
rhs: (= ((_ tuple.select 0) tuple_417) ((_ tuple.select 0) tuple_418))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_422) (+ ((_ tuple.select 0) tuple_420) 0))
rhs: (<= ((_ tuple.select 0) tuple_422) (+ ((_ tuple.select 0) tuple_420) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_422 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_420) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_422))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RecalculateApproach))))
rhs: (< ((_ tuple.select 14) tuple_421) 2)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_422 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_420) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_422))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RecalculateApproach)))) (< ((_ tuple.select 14) tuple_421) 2))
rhs: (= ((_ tuple.select 0) tuple_420) ((_ tuple.select 0) tuple_421))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_425) (+ ((_ tuple.select 0) tuple_423) 0))
rhs: (<= ((_ tuple.select 0) tuple_425) (+ ((_ tuple.select 0) tuple_423) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_425 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_423) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_425))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ConsiderUserPractices))))
rhs: (= ((_ tuple.select 0) tuple_423) ((_ tuple.select 0) tuple_424))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_428) (+ ((_ tuple.select 0) tuple_426) 0))
rhs: (<= ((_ tuple.select 0) tuple_428) (+ ((_ tuple.select 0) tuple_426) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_428 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_426) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_428))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ShowDataHistory)))
rhs: (not ((_ tuple.select 3) tuple_427))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_428 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_426) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_428))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ShowDataHistory))) (not ((_ tuple.select 3) tuple_427)))
rhs: (= ((_ tuple.select 0) tuple_426) ((_ tuple.select 0) tuple_427))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_431) (+ ((_ tuple.select 0) tuple_429) 0))
rhs: (<= ((_ tuple.select 0) tuple_431) (+ ((_ tuple.select 0) tuple_429) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_431 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_429) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_431))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ProvideDataSummaries))))
rhs: ((_ tuple.select 4) tuple_430)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_431 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_429) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_431))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ProvideDataSummaries)))) ((_ tuple.select 4) tuple_430))
rhs: (= ((_ tuple.select 0) tuple_429) ((_ tuple.select 0) tuple_430))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (= ((_ tuple.select 0) tuple_432) ((_ tuple.select 0) tuple_433))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (= ((_ tuple.select 0) tuple_434) ((_ tuple.select 0) tuple_435))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (= ((_ tuple.select 0) tuple_436) ((_ tuple.select 0) tuple_437))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: ((_ tuple.select 8) tuple_439)
rhs: ((_ tuple.select 7) tuple_439)
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (>= ((_ tuple.select 0) tuple_440) (+ ((_ tuple.select 0) tuple_438) 0))
rhs: (<= ((_ tuple.select 0) tuple_440) (+ ((_ tuple.select 0) tuple_438) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_440 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_438) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_440))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)))
rhs: (or ((_ tuple.select 8) tuple_439) ((_ tuple.select 7) tuple_439))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_440 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_438) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_440))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser))) (or ((_ tuple.select 8) tuple_439) ((_ tuple.select 7) tuple_439)))
rhs: (= ((_ tuple.select 0) tuple_438) ((_ tuple.select 0) tuple_439))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 14) tuple_442) 2)
rhs: ((_ tuple.select 1) tuple_442)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (and (= ((_ tuple.select 14) tuple_442) 2) ((_ tuple.select 1) tuple_442))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and true (and (= ((_ tuple.select 14) tuple_442) 2) ((_ tuple.select 1) tuple_442)))
rhs: (= ((_ tuple.select 0) tuple_441) ((_ tuple.select 0) tuple_442))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_445) (+ ((_ tuple.select 0) tuple_443) 0))
rhs: (<= ((_ tuple.select 0) tuple_445) (+ ((_ tuple.select 0) tuple_443) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_445 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_443) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_445))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskUserIfOK)))
rhs: ((_ tuple.select 10) tuple_444)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_445 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_443) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_445))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskUserIfOK))) ((_ tuple.select 10) tuple_444))
rhs: (= ((_ tuple.select 0) tuple_443) ((_ tuple.select 0) tuple_444))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_448) (+ ((_ tuple.select 0) tuple_446) 0))
rhs: (<= ((_ tuple.select 0) tuple_448) (+ ((_ tuple.select 0) tuple_446) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_448 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_446) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_448))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CallEmergencyServices)))
rhs: (= ((_ tuple.select 14) tuple_447) 2)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_448 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_446) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_448))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CallEmergencyServices))) (= ((_ tuple.select 14) tuple_447) 2))
rhs: (= ((_ tuple.select 0) tuple_446) ((_ tuple.select 0) tuple_447))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_451) (+ ((_ tuple.select 0) tuple_449) 0))
rhs: (<= ((_ tuple.select 0) tuple_451) (+ ((_ tuple.select 0) tuple_449) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_451 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_449) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_451))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskUserIfOK)))
rhs: (= ((_ tuple.select 0) tuple_449) ((_ tuple.select 0) tuple_450))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: ((_ tuple.select 3) tuple_453)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and true ((_ tuple.select 3) tuple_453))
rhs: (= ((_ tuple.select 0) tuple_452) ((_ tuple.select 0) tuple_453))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_456) (+ ((_ tuple.select 0) tuple_454) 0))
rhs: (<= ((_ tuple.select 0) tuple_456) (+ ((_ tuple.select 0) tuple_454) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_456 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_454) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_456))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) MonitorMealTime)))
rhs: (not ((_ tuple.select 1) tuple_455))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_456 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_454) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_456))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) MonitorMealTime))) (not ((_ tuple.select 1) tuple_455)))
rhs: (= ((_ tuple.select 0) tuple_454) ((_ tuple.select 0) tuple_455))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: ((_ tuple.select 12) tuple_458)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and true ((_ tuple.select 12) tuple_458))
rhs: (= ((_ tuple.select 0) tuple_457) ((_ tuple.select 0) tuple_458))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 14) tuple_460) 2)
rhs: ((_ tuple.select 12) tuple_460)
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: true
rhs: (or (= ((_ tuple.select 14) tuple_460) 2) ((_ tuple.select 12) tuple_460))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and true (or (= ((_ tuple.select 14) tuple_460) 2) ((_ tuple.select 12) tuple_460)))
rhs: (= ((_ tuple.select 0) tuple_459) ((_ tuple.select 0) tuple_460))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: true
rhs: (< ((_ tuple.select 14) tuple_462) 2)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and true (< ((_ tuple.select 14) tuple_462) 2))
rhs: (= ((_ tuple.select 0) tuple_461) ((_ tuple.select 0) tuple_462))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_465) (+ ((_ tuple.select 0) tuple_463) 0))
rhs: (<= ((_ tuple.select 0) tuple_465) (+ ((_ tuple.select 0) tuple_463) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_465 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_463) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_465))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) HumanOnFloor)))
rhs: (= ((_ tuple.select 0) tuple_463) ((_ tuple.select 0) tuple_464))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (>= ((_ tuple.select 0) tuple_468) (+ ((_ tuple.select 0) tuple_466) 0))
rhs: (<= ((_ tuple.select 0) tuple_468) (+ ((_ tuple.select 0) tuple_466) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_468 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_466) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_468))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) SmokeDetectorAlarm)))
rhs: (= ((_ tuple.select 0) tuple_466) ((_ tuple.select 0) tuple_467))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: ((_ tuple.select 1) tuple_469)
rhs: ((_ tuple.select 17) tuple_469)
lhs: Bool
rhs: Bool
compare: Kind.EQUAL
lhs: ((_ tuple.select 3) tuple_469)
rhs: ((_ tuple.select 19) tuple_469)
lhs: Bool
rhs: Bool
compare: Kind.EQUAL
lhs: ((_ tuple.select 4) tuple_469)
rhs: ((_ tuple.select 20) tuple_469)
lhs: Bool
rhs: Bool
compare: Kind.EQUAL
lhs: ((_ tuple.select 5) tuple_469)
rhs: ((_ tuple.select 21) tuple_469)
lhs: Bool
rhs: Bool
compare: Kind.EQUAL
lhs: ((_ tuple.select 6) tuple_469)
rhs: ((_ tuple.select 22) tuple_469)
lhs: Bool
rhs: Bool
compare: Kind.EQUAL
lhs: ((_ tuple.select 7) tuple_469)
rhs: ((_ tuple.select 23) tuple_469)
lhs: Bool
rhs: Bool
compare: Kind.EQUAL
lhs: ((_ tuple.select 8) tuple_469)
rhs: ((_ tuple.select 24) tuple_469)
lhs: Bool
rhs: Bool
compare: Kind.EQUAL
lhs: ((_ tuple.select 10) tuple_469)
rhs: ((_ tuple.select 26) tuple_469)
lhs: Bool
rhs: Bool
compare: Kind.EQUAL
lhs: ((_ tuple.select 11) tuple_469)
rhs: ((_ tuple.select 27) tuple_469)
lhs: Bool
rhs: Bool
compare: Kind.EQUAL
lhs: ((_ tuple.select 12) tuple_469)
rhs: ((_ tuple.select 28) tuple_469)
lhs: Bool
rhs: Bool
compare: Kind.EQUAL
lhs: ((_ tuple.select 13) tuple_469)
rhs: ((_ tuple.select 29) tuple_469)
lhs: Bool
rhs: Bool
compare: Kind.EQUAL
lhs: ((_ tuple.select 15) tuple_469)
rhs: ((_ tuple.select 31) tuple_469)
lhs: Bool
rhs: Bool
compare: Kind.EQUAL
lhs: (= ((_ tuple.select 1) tuple_469) ((_ tuple.select 17) tuple_469))
rhs: (= ((_ tuple.select 0) tuple_469) ((_ tuple.select 16) tuple_469))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 2) tuple_469) ((_ tuple.select 18) tuple_469))
rhs: (and (= ((_ tuple.select 1) tuple_469) ((_ tuple.select 17) tuple_469)) (= ((_ tuple.select 0) tuple_469) ((_ tuple.select 16) tuple_469)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 3) tuple_469) ((_ tuple.select 19) tuple_469))
rhs: (and (= ((_ tuple.select 2) tuple_469) ((_ tuple.select 18) tuple_469)) (and (= ((_ tuple.select 1) tuple_469) ((_ tuple.select 17) tuple_469)) (= ((_ tuple.select 0) tuple_469) ((_ tuple.select 16) tuple_469))))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 4) tuple_469) ((_ tuple.select 20) tuple_469))
rhs: (and (= ((_ tuple.select 3) tuple_469) ((_ tuple.select 19) tuple_469)) (and (= ((_ tuple.select 2) tuple_469) ((_ tuple.select 18) tuple_469)) (and (= ((_ tuple.select 1) tuple_469) ((_ tuple.select 17) tuple_469)) (= ((_ tuple.select 0) tuple_469) ((_ tuple.select 16) tuple_469)))))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 5) tuple_469) ((_ tuple.select 21) tuple_469))
rhs: (and (= ((_ tuple.select 4) tuple_469) ((_ tuple.select 20) tuple_469)) (and (= ((_ tuple.select 3) tuple_469) ((_ tuple.select 19) tuple_469)) (and (= ((_ tuple.select 2) tuple_469) ((_ tuple.select 18) tuple_469)) (and (= ((_ tuple.select 1) tuple_469) ((_ tuple.select 17) tuple_469)) (= ((_ tuple.select 0) tuple_469) ((_ tuple.select 16) tuple_469))))))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 6) tuple_469) ((_ tuple.select 22) tuple_469))
rhs: (and (= ((_ tuple.select 5) tuple_469) ((_ tuple.select 21) tuple_469)) (and (= ((_ tuple.select 4) tuple_469) ((_ tuple.select 20) tuple_469)) (and (= ((_ tuple.select 3) tuple_469) ((_ tuple.select 19) tuple_469)) (and (= ((_ tuple.select 2) tuple_469) ((_ tuple.select 18) tuple_469)) (and (= ((_ tuple.select 1) tuple_469) ((_ tuple.select 17) tuple_469)) (= ((_ tuple.select 0) tuple_469) ((_ tuple.select 16) tuple_469)))))))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 7) tuple_469) ((_ tuple.select 23) tuple_469))
rhs: (and (= ((_ tuple.select 6) tuple_469) ((_ tuple.select 22) tuple_469)) (and (= ((_ tuple.select 5) tuple_469) ((_ tuple.select 21) tuple_469)) (and (= ((_ tuple.select 4) tuple_469) ((_ tuple.select 20) tuple_469)) (and (= ((_ tuple.select 3) tuple_469) ((_ tuple.select 19) tuple_469)) (and (= ((_ tuple.select 2) tuple_469) ((_ tuple.select 18) tuple_469)) (and (= ((_ tuple.select 1) tuple_469) ((_ tuple.select 17) tuple_469)) (= ((_ tuple.select 0) tuple_469) ((_ tuple.select 16) tuple_469))))))))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 8) tuple_469) ((_ tuple.select 24) tuple_469))
rhs: (and (= ((_ tuple.select 7) tuple_469) ((_ tuple.select 23) tuple_469)) (and (= ((_ tuple.select 6) tuple_469) ((_ tuple.select 22) tuple_469)) (and (= ((_ tuple.select 5) tuple_469) ((_ tuple.select 21) tuple_469)) (and (= ((_ tuple.select 4) tuple_469) ((_ tuple.select 20) tuple_469)) (and (= ((_ tuple.select 3) tuple_469) ((_ tuple.select 19) tuple_469)) (and (= ((_ tuple.select 2) tuple_469) ((_ tuple.select 18) tuple_469)) (and (= ((_ tuple.select 1) tuple_469) ((_ tuple.select 17) tuple_469)) (= ((_ tuple.select 0) tuple_469) ((_ tuple.select 16) tuple_469)))))))))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 9) tuple_469) ((_ tuple.select 25) tuple_469))
rhs: (and (= ((_ tuple.select 8) tuple_469) ((_ tuple.select 24) tuple_469)) (and (= ((_ tuple.select 7) tuple_469) ((_ tuple.select 23) tuple_469)) (and (= ((_ tuple.select 6) tuple_469) ((_ tuple.select 22) tuple_469)) (and (= ((_ tuple.select 5) tuple_469) ((_ tuple.select 21) tuple_469)) (and (= ((_ tuple.select 4) tuple_469) ((_ tuple.select 20) tuple_469)) (and (= ((_ tuple.select 3) tuple_469) ((_ tuple.select 19) tuple_469)) (and (= ((_ tuple.select 2) tuple_469) ((_ tuple.select 18) tuple_469)) (and (= ((_ tuple.select 1) tuple_469) ((_ tuple.select 17) tuple_469)) (= ((_ tuple.select 0) tuple_469) ((_ tuple.select 16) tuple_469))))))))))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 10) tuple_469) ((_ tuple.select 26) tuple_469))
rhs: (and (= ((_ tuple.select 9) tuple_469) ((_ tuple.select 25) tuple_469)) (and (= ((_ tuple.select 8) tuple_469) ((_ tuple.select 24) tuple_469)) (and (= ((_ tuple.select 7) tuple_469) ((_ tuple.select 23) tuple_469)) (and (= ((_ tuple.select 6) tuple_469) ((_ tuple.select 22) tuple_469)) (and (= ((_ tuple.select 5) tuple_469) ((_ tuple.select 21) tuple_469)) (and (= ((_ tuple.select 4) tuple_469) ((_ tuple.select 20) tuple_469)) (and (= ((_ tuple.select 3) tuple_469) ((_ tuple.select 19) tuple_469)) (and (= ((_ tuple.select 2) tuple_469) ((_ tuple.select 18) tuple_469)) (and (= ((_ tuple.select 1) tuple_469) ((_ tuple.select 17) tuple_469)) (= ((_ tuple.select 0) tuple_469) ((_ tuple.select 16) tuple_469)))))))))))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 11) tuple_469) ((_ tuple.select 27) tuple_469))
rhs: (and (= ((_ tuple.select 10) tuple_469) ((_ tuple.select 26) tuple_469)) (and (= ((_ tuple.select 9) tuple_469) ((_ tuple.select 25) tuple_469)) (and (= ((_ tuple.select 8) tuple_469) ((_ tuple.select 24) tuple_469)) (and (= ((_ tuple.select 7) tuple_469) ((_ tuple.select 23) tuple_469)) (and (= ((_ tuple.select 6) tuple_469) ((_ tuple.select 22) tuple_469)) (and (= ((_ tuple.select 5) tuple_469) ((_ tuple.select 21) tuple_469)) (and (= ((_ tuple.select 4) tuple_469) ((_ tuple.select 20) tuple_469)) (and (= ((_ tuple.select 3) tuple_469) ((_ tuple.select 19) tuple_469)) (and (= ((_ tuple.select 2) tuple_469) ((_ tuple.select 18) tuple_469)) (and (= ((_ tuple.select 1) tuple_469) ((_ tuple.select 17) tuple_469)) (= ((_ tuple.select 0) tuple_469) ((_ tuple.select 16) tuple_469))))))))))))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 12) tuple_469) ((_ tuple.select 28) tuple_469))
rhs: (and (= ((_ tuple.select 11) tuple_469) ((_ tuple.select 27) tuple_469)) (and (= ((_ tuple.select 10) tuple_469) ((_ tuple.select 26) tuple_469)) (and (= ((_ tuple.select 9) tuple_469) ((_ tuple.select 25) tuple_469)) (and (= ((_ tuple.select 8) tuple_469) ((_ tuple.select 24) tuple_469)) (and (= ((_ tuple.select 7) tuple_469) ((_ tuple.select 23) tuple_469)) (and (= ((_ tuple.select 6) tuple_469) ((_ tuple.select 22) tuple_469)) (and (= ((_ tuple.select 5) tuple_469) ((_ tuple.select 21) tuple_469)) (and (= ((_ tuple.select 4) tuple_469) ((_ tuple.select 20) tuple_469)) (and (= ((_ tuple.select 3) tuple_469) ((_ tuple.select 19) tuple_469)) (and (= ((_ tuple.select 2) tuple_469) ((_ tuple.select 18) tuple_469)) (and (= ((_ tuple.select 1) tuple_469) ((_ tuple.select 17) tuple_469)) (= ((_ tuple.select 0) tuple_469) ((_ tuple.select 16) tuple_469)))))))))))))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 13) tuple_469) ((_ tuple.select 29) tuple_469))
rhs: (and (= ((_ tuple.select 12) tuple_469) ((_ tuple.select 28) tuple_469)) (and (= ((_ tuple.select 11) tuple_469) ((_ tuple.select 27) tuple_469)) (and (= ((_ tuple.select 10) tuple_469) ((_ tuple.select 26) tuple_469)) (and (= ((_ tuple.select 9) tuple_469) ((_ tuple.select 25) tuple_469)) (and (= ((_ tuple.select 8) tuple_469) ((_ tuple.select 24) tuple_469)) (and (= ((_ tuple.select 7) tuple_469) ((_ tuple.select 23) tuple_469)) (and (= ((_ tuple.select 6) tuple_469) ((_ tuple.select 22) tuple_469)) (and (= ((_ tuple.select 5) tuple_469) ((_ tuple.select 21) tuple_469)) (and (= ((_ tuple.select 4) tuple_469) ((_ tuple.select 20) tuple_469)) (and (= ((_ tuple.select 3) tuple_469) ((_ tuple.select 19) tuple_469)) (and (= ((_ tuple.select 2) tuple_469) ((_ tuple.select 18) tuple_469)) (and (= ((_ tuple.select 1) tuple_469) ((_ tuple.select 17) tuple_469)) (= ((_ tuple.select 0) tuple_469) ((_ tuple.select 16) tuple_469))))))))))))))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 14) tuple_469) ((_ tuple.select 30) tuple_469))
rhs: (and (= ((_ tuple.select 13) tuple_469) ((_ tuple.select 29) tuple_469)) (and (= ((_ tuple.select 12) tuple_469) ((_ tuple.select 28) tuple_469)) (and (= ((_ tuple.select 11) tuple_469) ((_ tuple.select 27) tuple_469)) (and (= ((_ tuple.select 10) tuple_469) ((_ tuple.select 26) tuple_469)) (and (= ((_ tuple.select 9) tuple_469) ((_ tuple.select 25) tuple_469)) (and (= ((_ tuple.select 8) tuple_469) ((_ tuple.select 24) tuple_469)) (and (= ((_ tuple.select 7) tuple_469) ((_ tuple.select 23) tuple_469)) (and (= ((_ tuple.select 6) tuple_469) ((_ tuple.select 22) tuple_469)) (and (= ((_ tuple.select 5) tuple_469) ((_ tuple.select 21) tuple_469)) (and (= ((_ tuple.select 4) tuple_469) ((_ tuple.select 20) tuple_469)) (and (= ((_ tuple.select 3) tuple_469) ((_ tuple.select 19) tuple_469)) (and (= ((_ tuple.select 2) tuple_469) ((_ tuple.select 18) tuple_469)) (and (= ((_ tuple.select 1) tuple_469) ((_ tuple.select 17) tuple_469)) (= ((_ tuple.select 0) tuple_469) ((_ tuple.select 16) tuple_469)))))))))))))))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 15) tuple_469) ((_ tuple.select 31) tuple_469))
rhs: (and (= ((_ tuple.select 14) tuple_469) ((_ tuple.select 30) tuple_469)) (and (= ((_ tuple.select 13) tuple_469) ((_ tuple.select 29) tuple_469)) (and (= ((_ tuple.select 12) tuple_469) ((_ tuple.select 28) tuple_469)) (and (= ((_ tuple.select 11) tuple_469) ((_ tuple.select 27) tuple_469)) (and (= ((_ tuple.select 10) tuple_469) ((_ tuple.select 26) tuple_469)) (and (= ((_ tuple.select 9) tuple_469) ((_ tuple.select 25) tuple_469)) (and (= ((_ tuple.select 8) tuple_469) ((_ tuple.select 24) tuple_469)) (and (= ((_ tuple.select 7) tuple_469) ((_ tuple.select 23) tuple_469)) (and (= ((_ tuple.select 6) tuple_469) ((_ tuple.select 22) tuple_469)) (and (= ((_ tuple.select 5) tuple_469) ((_ tuple.select 21) tuple_469)) (and (= ((_ tuple.select 4) tuple_469) ((_ tuple.select 20) tuple_469)) (and (= ((_ tuple.select 3) tuple_469) ((_ tuple.select 19) tuple_469)) (and (= ((_ tuple.select 2) tuple_469) ((_ tuple.select 18) tuple_469)) (and (= ((_ tuple.select 1) tuple_469) ((_ tuple.select 17) tuple_469)) (= ((_ tuple.select 0) tuple_469) ((_ tuple.select 16) tuple_469))))))))))))))))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= ((_ tuple.select 0) tuple_469) ((_ tuple.select 16) tuple_469))
rhs: (and (= ((_ tuple.select 15) tuple_469) ((_ tuple.select 31) tuple_469)) (and (= ((_ tuple.select 14) tuple_469) ((_ tuple.select 30) tuple_469)) (and (= ((_ tuple.select 13) tuple_469) ((_ tuple.select 29) tuple_469)) (and (= ((_ tuple.select 12) tuple_469) ((_ tuple.select 28) tuple_469)) (and (= ((_ tuple.select 11) tuple_469) ((_ tuple.select 27) tuple_469)) (and (= ((_ tuple.select 10) tuple_469) ((_ tuple.select 26) tuple_469)) (and (= ((_ tuple.select 9) tuple_469) ((_ tuple.select 25) tuple_469)) (and (= ((_ tuple.select 8) tuple_469) ((_ tuple.select 24) tuple_469)) (and (= ((_ tuple.select 7) tuple_469) ((_ tuple.select 23) tuple_469)) (and (= ((_ tuple.select 6) tuple_469) ((_ tuple.select 22) tuple_469)) (and (= ((_ tuple.select 5) tuple_469) ((_ tuple.select 21) tuple_469)) (and (= ((_ tuple.select 4) tuple_469) ((_ tuple.select 20) tuple_469)) (and (= ((_ tuple.select 3) tuple_469) ((_ tuple.select 19) tuple_469)) (and (= ((_ tuple.select 2) tuple_469) ((_ tuple.select 18) tuple_469)) (and (= ((_ tuple.select 1) tuple_469) ((_ tuple.select 17) tuple_469)) (= ((_ tuple.select 0) tuple_469) ((_ tuple.select 16) tuple_469)))))))))))))))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_473 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_474 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_474) ((_ tuple.select 0) tuple_473)))) PreparingDeployment))) PreparingDeployment)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_471 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_472 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_472) ((_ tuple.select 0) tuple_471)))) PreparingDeployment))) PreparingDeployment)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_470 (Tuple Int))) true) PreparingDeployment)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_473 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_474 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_474) ((_ tuple.select 0) tuple_473)))) PreparingDeployment))) PreparingDeployment))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_471 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_472 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_472) ((_ tuple.select 0) tuple_471)))) PreparingDeployment))) PreparingDeployment))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_478 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_479 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_479) ((_ tuple.select 0) tuple_478)))) AgentDeployed))) AgentDeployed)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_476 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_477 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_477) ((_ tuple.select 0) tuple_476)))) AgentDeployed))) AgentDeployed)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_475 (Tuple Int))) true) AgentDeployed)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_478 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_479 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_479) ((_ tuple.select 0) tuple_478)))) AgentDeployed))) AgentDeployed))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_476 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_477 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_477) ((_ tuple.select 0) tuple_476)))) AgentDeployed))) AgentDeployed))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_483 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_484 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_484) ((_ tuple.select 0) tuple_483)))) AskCallHelp))) AskCallHelp)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_481 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_482 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_482) ((_ tuple.select 0) tuple_481)))) AskCallHelp))) AskCallHelp)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_480 (Tuple Int))) true) AskCallHelp)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_483 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_484 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_484) ((_ tuple.select 0) tuple_483)))) AskCallHelp))) AskCallHelp))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_481 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_482 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_482) ((_ tuple.select 0) tuple_481)))) AskCallHelp))) AskCallHelp))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_488 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_489 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_489) ((_ tuple.select 0) tuple_488)))) MeetingUser))) MeetingUser)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_486 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_487 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_487) ((_ tuple.select 0) tuple_486)))) MeetingUser))) MeetingUser)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_485 (Tuple Int))) true) MeetingUser)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_488 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_489 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_489) ((_ tuple.select 0) tuple_488)))) MeetingUser))) MeetingUser))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_486 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_487 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_487) ((_ tuple.select 0) tuple_486)))) MeetingUser))) MeetingUser))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_493 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_494 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_494) ((_ tuple.select 0) tuple_493)))) InformUser))) InformUser)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_491 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_492 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_492) ((_ tuple.select 0) tuple_491)))) InformUser))) InformUser)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_490 (Tuple Int))) true) InformUser)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_493 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_494 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_494) ((_ tuple.select 0) tuple_493)))) InformUser))) InformUser))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_491 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_492 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_492) ((_ tuple.select 0) tuple_491)))) InformUser))) InformUser))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_498 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_499 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_499) ((_ tuple.select 0) tuple_498)))) InformCaregiver))) InformCaregiver)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_496 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_497 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_497) ((_ tuple.select 0) tuple_496)))) InformCaregiver))) InformCaregiver)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_495 (Tuple Int))) true) InformCaregiver)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_498 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_499 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_499) ((_ tuple.select 0) tuple_498)))) InformCaregiver))) InformCaregiver))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_496 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_497 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_497) ((_ tuple.select 0) tuple_496)))) InformCaregiver))) InformCaregiver))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_503 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_504 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_504) ((_ tuple.select 0) tuple_503)))) CallEmergencyServices))) CallEmergencyServices)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_501 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_502 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_502) ((_ tuple.select 0) tuple_501)))) CallEmergencyServices))) CallEmergencyServices)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_500 (Tuple Int))) true) CallEmergencyServices)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_503 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_504 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_504) ((_ tuple.select 0) tuple_503)))) CallEmergencyServices))) CallEmergencyServices))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_501 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_502 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_502) ((_ tuple.select 0) tuple_501)))) CallEmergencyServices))) CallEmergencyServices))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_508 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_509 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_509) ((_ tuple.select 0) tuple_508)))) RemindLater))) RemindLater)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_506 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_507 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_507) ((_ tuple.select 0) tuple_506)))) RemindLater))) RemindLater)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_505 (Tuple Int))) true) RemindLater)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_508 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_509 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_509) ((_ tuple.select 0) tuple_508)))) RemindLater))) RemindLater))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_506 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_507 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_507) ((_ tuple.select 0) tuple_506)))) RemindLater))) RemindLater))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_513 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_514 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_514) ((_ tuple.select 0) tuple_513)))) AgentHasAppropriateAppearance))) AgentHasAppropriateAppearance)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_511 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_512 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_512) ((_ tuple.select 0) tuple_511)))) AgentHasAppropriateAppearance))) AgentHasAppropriateAppearance)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_510 (Tuple Int))) true) AgentHasAppropriateAppearance)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_513 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_514 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_514) ((_ tuple.select 0) tuple_513)))) AgentHasAppropriateAppearance))) AgentHasAppropriateAppearance))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_511 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_512 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_512) ((_ tuple.select 0) tuple_511)))) AgentHasAppropriateAppearance))) AgentHasAppropriateAppearance))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_518 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_519 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_519) ((_ tuple.select 0) tuple_518)))) AskForDetailLevelOfInstructions))) AskForDetailLevelOfInstructions)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_516 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_517 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_517) ((_ tuple.select 0) tuple_516)))) AskForDetailLevelOfInstructions))) AskForDetailLevelOfInstructions)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_515 (Tuple Int))) true) AskForDetailLevelOfInstructions)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_518 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_519 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_519) ((_ tuple.select 0) tuple_518)))) AskForDetailLevelOfInstructions))) AskForDetailLevelOfInstructions))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_516 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_517 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_517) ((_ tuple.select 0) tuple_516)))) AskForDetailLevelOfInstructions))) AskForDetailLevelOfInstructions))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_523 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_524 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_524) ((_ tuple.select 0) tuple_523)))) UseFirstPersonPluralLanguage))) UseFirstPersonPluralLanguage)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_521 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_522 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_522) ((_ tuple.select 0) tuple_521)))) UseFirstPersonPluralLanguage))) UseFirstPersonPluralLanguage)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_520 (Tuple Int))) true) UseFirstPersonPluralLanguage)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_523 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_524 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_524) ((_ tuple.select 0) tuple_523)))) UseFirstPersonPluralLanguage))) UseFirstPersonPluralLanguage))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_521 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_522 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_522) ((_ tuple.select 0) tuple_521)))) UseFirstPersonPluralLanguage))) UseFirstPersonPluralLanguage))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_528 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_529 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_529) ((_ tuple.select 0) tuple_528)))) CalibrateSpeech))) CalibrateSpeech)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_526 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_527 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_527) ((_ tuple.select 0) tuple_526)))) CalibrateSpeech))) CalibrateSpeech)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_525 (Tuple Int))) true) CalibrateSpeech)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_528 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_529 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_529) ((_ tuple.select 0) tuple_528)))) CalibrateSpeech))) CalibrateSpeech))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_526 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_527 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_527) ((_ tuple.select 0) tuple_526)))) CalibrateSpeech))) CalibrateSpeech))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_533 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_534 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_534) ((_ tuple.select 0) tuple_533)))) RemindUserOfLimitations))) RemindUserOfLimitations)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_531 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_532 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_532) ((_ tuple.select 0) tuple_531)))) RemindUserOfLimitations))) RemindUserOfLimitations)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_530 (Tuple Int))) true) RemindUserOfLimitations)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_533 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_534 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_534) ((_ tuple.select 0) tuple_533)))) RemindUserOfLimitations))) RemindUserOfLimitations))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_531 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_532 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_532) ((_ tuple.select 0) tuple_531)))) RemindUserOfLimitations))) RemindUserOfLimitations))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_538 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_539 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_539) ((_ tuple.select 0) tuple_538)))) AskForEmergencyContact))) AskForEmergencyContact)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_536 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_537 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_537) ((_ tuple.select 0) tuple_536)))) AskForEmergencyContact))) AskForEmergencyContact)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_535 (Tuple Int))) true) AskForEmergencyContact)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_538 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_539 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_539) ((_ tuple.select 0) tuple_538)))) AskForEmergencyContact))) AskForEmergencyContact))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_536 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_537 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_537) ((_ tuple.select 0) tuple_536)))) AskForEmergencyContact))) AskForEmergencyContact))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_543 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_544 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_544) ((_ tuple.select 0) tuple_543)))) HumanOnFloor))) HumanOnFloor)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_541 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_542 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_542) ((_ tuple.select 0) tuple_541)))) HumanOnFloor))) HumanOnFloor)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_540 (Tuple Int))) true) HumanOnFloor)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_543 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_544 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_544) ((_ tuple.select 0) tuple_543)))) HumanOnFloor))) HumanOnFloor))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_541 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_542 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_542) ((_ tuple.select 0) tuple_541)))) HumanOnFloor))) HumanOnFloor))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_548 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_549 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_549) ((_ tuple.select 0) tuple_548)))) SmokeDetectorAlarm))) SmokeDetectorAlarm)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_546 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_547 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_547) ((_ tuple.select 0) tuple_546)))) SmokeDetectorAlarm))) SmokeDetectorAlarm)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_545 (Tuple Int))) true) SmokeDetectorAlarm)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_548 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_549 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_549) ((_ tuple.select 0) tuple_548)))) SmokeDetectorAlarm))) SmokeDetectorAlarm))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_546 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_547 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_547) ((_ tuple.select 0) tuple_546)))) SmokeDetectorAlarm))) SmokeDetectorAlarm))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_553 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_554 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_554) ((_ tuple.select 0) tuple_553)))) OpenWindows))) OpenWindows)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_551 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_552 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_552) ((_ tuple.select 0) tuple_551)))) OpenWindows))) OpenWindows)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_550 (Tuple Int))) true) OpenWindows)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_553 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_554 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_554) ((_ tuple.select 0) tuple_553)))) OpenWindows))) OpenWindows))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_551 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_552 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_552) ((_ tuple.select 0) tuple_551)))) OpenWindows))) OpenWindows))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_558 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_559 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_559) ((_ tuple.select 0) tuple_558)))) FireSafetyMeasures))) FireSafetyMeasures)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_556 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_557 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_557) ((_ tuple.select 0) tuple_556)))) FireSafetyMeasures))) FireSafetyMeasures)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_555 (Tuple Int))) true) FireSafetyMeasures)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_558 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_559 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_559) ((_ tuple.select 0) tuple_558)))) FireSafetyMeasures))) FireSafetyMeasures))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_556 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_557 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_557) ((_ tuple.select 0) tuple_556)))) FireSafetyMeasures))) FireSafetyMeasures))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_563 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_564 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_564) ((_ tuple.select 0) tuple_563)))) AskUserIfOK))) AskUserIfOK)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_561 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_562 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_562) ((_ tuple.select 0) tuple_561)))) AskUserIfOK))) AskUserIfOK)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_560 (Tuple Int))) true) AskUserIfOK)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_563 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_564 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_564) ((_ tuple.select 0) tuple_563)))) AskUserIfOK))) AskUserIfOK))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_561 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_562 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_562) ((_ tuple.select 0) tuple_561)))) AskUserIfOK))) AskUserIfOK))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_568 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_569 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_569) ((_ tuple.select 0) tuple_568)))) InterfereSafely))) InterfereSafely)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_566 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_567 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_567) ((_ tuple.select 0) tuple_566)))) InterfereSafely))) InterfereSafely)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_565 (Tuple Int))) true) InterfereSafely)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_568 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_569 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_569) ((_ tuple.select 0) tuple_568)))) InterfereSafely))) InterfereSafely))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_566 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_567 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_567) ((_ tuple.select 0) tuple_566)))) InterfereSafely))) InterfereSafely))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_573 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_574 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_574) ((_ tuple.select 0) tuple_573)))) UserHasLimitation))) UserHasLimitation)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_571 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_572 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_572) ((_ tuple.select 0) tuple_571)))) UserHasLimitation))) UserHasLimitation)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_570 (Tuple Int))) true) UserHasLimitation)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_573 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_574 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_574) ((_ tuple.select 0) tuple_573)))) UserHasLimitation))) UserHasLimitation))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_571 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_572 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_572) ((_ tuple.select 0) tuple_571)))) UserHasLimitation))) UserHasLimitation))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_578 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_579 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_579) ((_ tuple.select 0) tuple_578)))) CheckTemperature))) CheckTemperature)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_576 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_577 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_577) ((_ tuple.select 0) tuple_576)))) CheckTemperature))) CheckTemperature)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_575 (Tuple Int))) true) CheckTemperature)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_578 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_579 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_579) ((_ tuple.select 0) tuple_578)))) CheckTemperature))) CheckTemperature))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_576 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_577 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_577) ((_ tuple.select 0) tuple_576)))) CheckTemperature))) CheckTemperature))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_583 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_584 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_584) ((_ tuple.select 0) tuple_583)))) FoodPreparation))) FoodPreparation)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_581 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_582 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_582) ((_ tuple.select 0) tuple_581)))) FoodPreparation))) FoodPreparation)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_580 (Tuple Int))) true) FoodPreparation)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_583 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_584 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_584) ((_ tuple.select 0) tuple_583)))) FoodPreparation))) FoodPreparation))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_581 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_582 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_582) ((_ tuple.select 0) tuple_581)))) FoodPreparation))) FoodPreparation))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_588 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_589 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_589) ((_ tuple.select 0) tuple_588)))) TrackTime))) TrackTime)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_586 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_587 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_587) ((_ tuple.select 0) tuple_586)))) TrackTime))) TrackTime)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_585 (Tuple Int))) true) TrackTime)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_588 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_589 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_589) ((_ tuple.select 0) tuple_588)))) TrackTime))) TrackTime))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_586 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_587 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_587) ((_ tuple.select 0) tuple_586)))) TrackTime))) TrackTime))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_593 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_594 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_594) ((_ tuple.select 0) tuple_593)))) UserUnpredictable))) UserUnpredictable)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_591 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_592 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_592) ((_ tuple.select 0) tuple_591)))) UserUnpredictable))) UserUnpredictable)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_590 (Tuple Int))) true) UserUnpredictable)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_593 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_594 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_594) ((_ tuple.select 0) tuple_593)))) UserUnpredictable))) UserUnpredictable))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_591 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_592 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_592) ((_ tuple.select 0) tuple_591)))) UserUnpredictable))) UserUnpredictable))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_598 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_599 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_599) ((_ tuple.select 0) tuple_598)))) GiveUserDangerousObjects))) GiveUserDangerousObjects)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_596 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_597 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_597) ((_ tuple.select 0) tuple_596)))) GiveUserDangerousObjects))) GiveUserDangerousObjects)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_595 (Tuple Int))) true) GiveUserDangerousObjects)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_598 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_599 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_599) ((_ tuple.select 0) tuple_598)))) GiveUserDangerousObjects))) GiveUserDangerousObjects))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_596 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_597 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_597) ((_ tuple.select 0) tuple_596)))) GiveUserDangerousObjects))) GiveUserDangerousObjects))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_603 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_604 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_604) ((_ tuple.select 0) tuple_603)))) MonitorMealTime))) MonitorMealTime)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_601 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_602 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_602) ((_ tuple.select 0) tuple_601)))) MonitorMealTime))) MonitorMealTime)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_600 (Tuple Int))) true) MonitorMealTime)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_603 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_604 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_604) ((_ tuple.select 0) tuple_603)))) MonitorMealTime))) MonitorMealTime))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_601 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_602 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_602) ((_ tuple.select 0) tuple_601)))) MonitorMealTime))) MonitorMealTime))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_608 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_609 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_609) ((_ tuple.select 0) tuple_608)))) BeforeCookingBegins))) BeforeCookingBegins)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_606 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_607 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_607) ((_ tuple.select 0) tuple_606)))) BeforeCookingBegins))) BeforeCookingBegins)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_605 (Tuple Int))) true) BeforeCookingBegins)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_608 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_609 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_609) ((_ tuple.select 0) tuple_608)))) BeforeCookingBegins))) BeforeCookingBegins))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_606 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_607 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_607) ((_ tuple.select 0) tuple_606)))) BeforeCookingBegins))) BeforeCookingBegins))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_613 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_614 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_614) ((_ tuple.select 0) tuple_613)))) UserWantsToCook))) UserWantsToCook)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_611 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_612 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_612) ((_ tuple.select 0) tuple_611)))) UserWantsToCook))) UserWantsToCook)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_610 (Tuple Int))) true) UserWantsToCook)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_613 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_614 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_614) ((_ tuple.select 0) tuple_613)))) UserWantsToCook))) UserWantsToCook))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_611 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_612 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_612) ((_ tuple.select 0) tuple_611)))) UserWantsToCook))) UserWantsToCook))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_618 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_619 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_619) ((_ tuple.select 0) tuple_618)))) AllowUserToCook))) AllowUserToCook)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_616 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_617 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_617) ((_ tuple.select 0) tuple_616)))) AllowUserToCook))) AllowUserToCook)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_615 (Tuple Int))) true) AllowUserToCook)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_618 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_619 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_619) ((_ tuple.select 0) tuple_618)))) AllowUserToCook))) AllowUserToCook))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_616 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_617 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_617) ((_ tuple.select 0) tuple_616)))) AllowUserToCook))) AllowUserToCook))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_623 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_624 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_624) ((_ tuple.select 0) tuple_623)))) GiveSuggestion))) GiveSuggestion)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_621 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_622 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_622) ((_ tuple.select 0) tuple_621)))) GiveSuggestion))) GiveSuggestion)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_620 (Tuple Int))) true) GiveSuggestion)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_623 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_624 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_624) ((_ tuple.select 0) tuple_623)))) GiveSuggestion))) GiveSuggestion))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_621 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_622 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_622) ((_ tuple.select 0) tuple_621)))) GiveSuggestion))) GiveSuggestion))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_628 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_629 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_629) ((_ tuple.select 0) tuple_628)))) GivingCookingInstructions))) GivingCookingInstructions)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_626 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_627 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_627) ((_ tuple.select 0) tuple_626)))) GivingCookingInstructions))) GivingCookingInstructions)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_625 (Tuple Int))) true) GivingCookingInstructions)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_628 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_629 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_629) ((_ tuple.select 0) tuple_628)))) GivingCookingInstructions))) GivingCookingInstructions))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_626 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_627 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_627) ((_ tuple.select 0) tuple_626)))) GivingCookingInstructions))) GivingCookingInstructions))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_633 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_634 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_634) ((_ tuple.select 0) tuple_633)))) ConsiderUserPractices))) ConsiderUserPractices)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_631 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_632 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_632) ((_ tuple.select 0) tuple_631)))) ConsiderUserPractices))) ConsiderUserPractices)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_630 (Tuple Int))) true) ConsiderUserPractices)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_633 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_634 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_634) ((_ tuple.select 0) tuple_633)))) ConsiderUserPractices))) ConsiderUserPractices))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_631 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_632 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_632) ((_ tuple.select 0) tuple_631)))) ConsiderUserPractices))) ConsiderUserPractices))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_638 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_639 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_639) ((_ tuple.select 0) tuple_638)))) UserChangeItemLocation))) UserChangeItemLocation)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_636 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_637 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_637) ((_ tuple.select 0) tuple_636)))) UserChangeItemLocation))) UserChangeItemLocation)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_635 (Tuple Int))) true) UserChangeItemLocation)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_638 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_639 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_639) ((_ tuple.select 0) tuple_638)))) UserChangeItemLocation))) UserChangeItemLocation))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_636 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_637 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_637) ((_ tuple.select 0) tuple_636)))) UserChangeItemLocation))) UserChangeItemLocation))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_643 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_644 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_644) ((_ tuple.select 0) tuple_643)))) UserChangeMind))) UserChangeMind)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_641 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_642 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_642) ((_ tuple.select 0) tuple_641)))) UserChangeMind))) UserChangeMind)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_640 (Tuple Int))) true) UserChangeMind)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_643 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_644 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_644) ((_ tuple.select 0) tuple_643)))) UserChangeMind))) UserChangeMind))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_641 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_642 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_642) ((_ tuple.select 0) tuple_641)))) UserChangeMind))) UserChangeMind))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_648 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_649 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_649) ((_ tuple.select 0) tuple_648)))) RecalculateApproach))) RecalculateApproach)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_646 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_647 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_647) ((_ tuple.select 0) tuple_646)))) RecalculateApproach))) RecalculateApproach)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_645 (Tuple Int))) true) RecalculateApproach)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_648 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_649 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_649) ((_ tuple.select 0) tuple_648)))) RecalculateApproach))) RecalculateApproach))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_646 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_647 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_647) ((_ tuple.select 0) tuple_646)))) RecalculateApproach))) RecalculateApproach))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_653 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_654 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_654) ((_ tuple.select 0) tuple_653)))) ProvideDataSummaries))) ProvideDataSummaries)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_651 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_652 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_652) ((_ tuple.select 0) tuple_651)))) ProvideDataSummaries))) ProvideDataSummaries)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_650 (Tuple Int))) true) ProvideDataSummaries)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_653 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_654 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_654) ((_ tuple.select 0) tuple_653)))) ProvideDataSummaries))) ProvideDataSummaries))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_651 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_652 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_652) ((_ tuple.select 0) tuple_651)))) ProvideDataSummaries))) ProvideDataSummaries))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_658 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_659 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_659) ((_ tuple.select 0) tuple_658)))) CollectandRecordInformation))) CollectandRecordInformation)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_656 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_657 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_657) ((_ tuple.select 0) tuple_656)))) CollectandRecordInformation))) CollectandRecordInformation)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_655 (Tuple Int))) true) CollectandRecordInformation)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_658 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_659 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_659) ((_ tuple.select 0) tuple_658)))) CollectandRecordInformation))) CollectandRecordInformation))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_656 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_657 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_657) ((_ tuple.select 0) tuple_656)))) CollectandRecordInformation))) CollectandRecordInformation))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_663 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_664 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_664) ((_ tuple.select 0) tuple_663)))) UpdateInformation))) UpdateInformation)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_661 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_662 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_662) ((_ tuple.select 0) tuple_661)))) UpdateInformation))) UpdateInformation)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_660 (Tuple Int))) true) UpdateInformation)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_663 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_664 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_664) ((_ tuple.select 0) tuple_663)))) UpdateInformation))) UpdateInformation))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_661 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_662 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_662) ((_ tuple.select 0) tuple_661)))) UpdateInformation))) UpdateInformation))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_668 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_669 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_669) ((_ tuple.select 0) tuple_668)))) ShowDataHistory))) ShowDataHistory)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_666 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_667 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_667) ((_ tuple.select 0) tuple_666)))) ShowDataHistory))) ShowDataHistory)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_665 (Tuple Int))) true) ShowDataHistory)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_668 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_669 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_669) ((_ tuple.select 0) tuple_668)))) ShowDataHistory))) ShowDataHistory))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_666 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_667 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_667) ((_ tuple.select 0) tuple_666)))) ShowDataHistory))) ShowDataHistory))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_673 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_674 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_674) ((_ tuple.select 0) tuple_673)))) UpdateMap))) UpdateMap)))
rhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_671 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_672 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_672) ((_ tuple.select 0) tuple_671)))) UpdateMap))) UpdateMap)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_670 (Tuple Int))) true) UpdateMap)))
rhs: (and (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_673 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_674 (Tuple Int))) (not (<= ((_ tuple.select 0) tuple_674) ((_ tuple.select 0) tuple_673)))) UpdateMap))) UpdateMap))) (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_671 (Tuple Int))) (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_672 (Tuple Int))) (not (>= ((_ tuple.select 0) tuple_672) ((_ tuple.select 0) tuple_671)))) UpdateMap))) UpdateMap))))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
check rule_1
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/00.smt2
lhs: (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_677 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_678 (Tuple Int))) (= ((_ tuple.select 0) tuple_678) ((_ tuple.select 9) tuple_677))) needLevel))))) Measure))
rhs: (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_675 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_676 (Tuple Int))) (= ((_ tuple.select 0) tuple_676) ((_ tuple.select 0) tuple_675))) time))))) Measure))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_679 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_680 (Tuple Int))) (= ((_ tuple.select 0) tuple_680) ((_ tuple.select 14) tuple_679))) riskLevel))))) Measure))
rhs: (and (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_677 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_678 (Tuple Int))) (= ((_ tuple.select 0) tuple_678) ((_ tuple.select 9) tuple_677))) needLevel))))) Measure)) (= (as set.empty (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (set.filter (lambda ((tuple_675 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (not (not (= (as set.empty (Set (Tuple Int))) (set.filter (lambda ((tuple_676 (Tuple Int))) (= ((_ tuple.select 0) tuple_676) ((_ tuple.select 0) tuple_675))) time))))) Measure)))
lhs: Bool
rhs: Bool
compare: Kind.AND
trail 0.05152559280395508
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (set.singleton (tuple 0))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_2
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/01.smt2
trail 0.05251455307006836
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (set.singleton (tuple 0))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (set.singleton (tuple 0))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_3
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/02.smt2
trail 0.14501333236694336
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (set.singleton (tuple 0))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (set.singleton (tuple 0))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (set.singleton (tuple 0))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (set.singleton (tuple 0))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 28801 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_4
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/03.smt2
trail 0.08207845687866211
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (set.singleton (tuple 0))
InformCaregiver     = (set.singleton (tuple 0))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (set.singleton (tuple 0))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 28801 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_5
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/04.smt2
trail 0.034162282943725586
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (set.singleton (tuple 0))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_6
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/05.smt2
trail 0.06604623794555664
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (set.singleton (tuple 0))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (set.singleton (tuple 0))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 false true true true 0 true))
****************************************************************************************************
check rule_7
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/06.smt2
trail 0.0587007999420166
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (set.singleton (tuple 0))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (set.singleton (tuple 0))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 false true true true 0 true))
****************************************************************************************************
check rule_8
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/07.smt2
trail 0.03863096237182617
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (set.singleton (tuple 0))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 false 0 true true true true true true 0 true false true true 0 true))
****************************************************************************************************
check rule_9
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/08.smt2
trail 0.07482719421386719
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (set.singleton (tuple 0))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (set.singleton (tuple 0))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (set.singleton (tuple 0))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_10
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/09.smt2
trail 0.03653860092163086
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (set.singleton (tuple 0))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_11
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/10.smt2
trail 0.03823590278625488
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (set.singleton (tuple 0))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_12
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/11.smt2
trail 0.07667160034179688
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (set.singleton (tuple 0))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (set.singleton (tuple 0))
AllowUserToCook     = (set.singleton (tuple 0))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_13
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/12.smt2
trail 0.03336977958679199
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (set.singleton (tuple 0))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_14
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/13.smt2
trail 0.046739816665649414
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (set.singleton (tuple 0))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_15
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/14.smt2
trail 0.04377150535583496
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (set.singleton (tuple 0))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_16
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/15.smt2
trail 0.08113479614257812
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (set.singleton (tuple 0))
InformUser     = (set.singleton (tuple 0))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (set.singleton (tuple 0))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_17
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/16.smt2
trail 0.09223580360412598
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (set.singleton (tuple 0))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (set.singleton (tuple 0))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (set.singleton (tuple 0))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_18
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/17.smt2
trail 0.03652501106262207
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (set.singleton (tuple 0))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_19
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/18.smt2
trail 0.05235147476196289
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (set.singleton (tuple 0))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (set.singleton (tuple 0))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_20
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/19.smt2
trail 0.03280305862426758
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (set.singleton (tuple 0))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_21
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/20.smt2
trail 0.19446229934692383
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (set.singleton (tuple 0))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (set.singleton (tuple 0))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (set.singleton (tuple 0))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (set.singleton (tuple 0))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (set.singleton (tuple 0))
ShowDataHistory     = (set.singleton (tuple 0))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 false true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_22
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/21.smt2
trail 0.03819632530212402
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (set.singleton (tuple 0))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_23
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/22.smt2
trail 0.04793858528137207
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (set.singleton (tuple 0))
GiveUserDangerousObjects     = (set.singleton (tuple 0))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_24
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/23.smt2
trail 0.12484073638916016
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (set.singleton (tuple 0))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (set.singleton (tuple 0))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (set.singleton (tuple 0))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (set.singleton (tuple 0))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true false true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_25
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/24.smt2
trail 0.06331419944763184
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (set.singleton (tuple 0))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (set.singleton (tuple 0))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true false true true 0 true true true true 0 true))
****************************************************************************************************
check rule_26
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/25.smt2
trail 0.06371164321899414
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (set.singleton (tuple 0))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_27
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/26.smt2
trail 0.06019091606140137
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (set.singleton (tuple 0))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (set.singleton (tuple 0))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_28
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/27.smt2
trail 0.05939483642578125
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (set.singleton (tuple 0))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (set.singleton (tuple 0))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_29
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/28.smt2
trail 0.04569816589355469
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (set.singleton (tuple 0))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_30
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/29.smt2
trail 0.0397031307220459
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (set.singleton (tuple 0))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_31
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/30.smt2
trail 0.03567624092102051
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (set.singleton (tuple 0))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_32
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/31.smt2
trail 0.1182565689086914
Result     = unsat
****************************************************************************************************
check rule_33
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/32.smt2
trail 0.08114361763000488
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (set.singleton (tuple 121))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (set.singleton (tuple 0))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (as set.empty (Set (Tuple Int)))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_34
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/33.smt2
trail 0.08872246742248535
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (set.singleton (tuple 0))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (as set.empty (Set (Tuple Int)))
FireSafetyMeasures     = (set.singleton (tuple 0))
AskUserIfOK     = (set.singleton (tuple 0))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_35
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/34.smt2
trail 0.08142995834350586
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (set.singleton (tuple 0))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (set.singleton (tuple 0))
FireSafetyMeasures     = (set.singleton (tuple 0))
AskUserIfOK     = (as set.empty (Set (Tuple Int)))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
check rule_36
outputfile: /home/mudathir/Desktop/SLEEC-CVC/test_files_filters/ALMI/ALMI-Corrected/redundancy/35.smt2
trail 0.09184384346008301
Result     = sat
time     = (set.singleton (tuple 0))
PreparingDeployment     = (as set.empty (Set (Tuple Int)))
AgentDeployed     = (as set.empty (Set (Tuple Int)))
AskCallHelp     = (as set.empty (Set (Tuple Int)))
MeetingUser     = (as set.empty (Set (Tuple Int)))
InformUser     = (as set.empty (Set (Tuple Int)))
InformCaregiver     = (as set.empty (Set (Tuple Int)))
CallEmergencyServices     = (as set.empty (Set (Tuple Int)))
RemindLater     = (as set.empty (Set (Tuple Int)))
AgentHasAppropriateAppearance     = (as set.empty (Set (Tuple Int)))
AskForDetailLevelOfInstructions     = (as set.empty (Set (Tuple Int)))
UseFirstPersonPluralLanguage     = (as set.empty (Set (Tuple Int)))
CalibrateSpeech     = (as set.empty (Set (Tuple Int)))
RemindUserOfLimitations     = (as set.empty (Set (Tuple Int)))
AskForEmergencyContact     = (as set.empty (Set (Tuple Int)))
HumanOnFloor     = (as set.empty (Set (Tuple Int)))
SmokeDetectorAlarm     = (as set.empty (Set (Tuple Int)))
OpenWindows     = (set.singleton (tuple 0))
FireSafetyMeasures     = (set.singleton (tuple 0))
AskUserIfOK     = (set.singleton (tuple 0))
InterfereSafely     = (as set.empty (Set (Tuple Int)))
UserHasLimitation     = (as set.empty (Set (Tuple Int)))
CheckTemperature     = (as set.empty (Set (Tuple Int)))
FoodPreparation     = (as set.empty (Set (Tuple Int)))
TrackTime     = (as set.empty (Set (Tuple Int)))
UserUnpredictable     = (as set.empty (Set (Tuple Int)))
GiveUserDangerousObjects     = (as set.empty (Set (Tuple Int)))
MonitorMealTime     = (as set.empty (Set (Tuple Int)))
BeforeCookingBegins     = (as set.empty (Set (Tuple Int)))
UserWantsToCook     = (as set.empty (Set (Tuple Int)))
AllowUserToCook     = (as set.empty (Set (Tuple Int)))
GiveSuggestion     = (as set.empty (Set (Tuple Int)))
GivingCookingInstructions     = (as set.empty (Set (Tuple Int)))
ConsiderUserPractices     = (as set.empty (Set (Tuple Int)))
UserChangeItemLocation     = (as set.empty (Set (Tuple Int)))
UserChangeMind     = (as set.empty (Set (Tuple Int)))
RecalculateApproach     = (as set.empty (Set (Tuple Int)))
ProvideDataSummaries     = (as set.empty (Set (Tuple Int)))
CollectandRecordInformation     = (as set.empty (Set (Tuple Int)))
UpdateInformation     = (as set.empty (Set (Tuple Int)))
ShowDataHistory     = (as set.empty (Set (Tuple Int)))
UpdateMap     = (as set.empty (Set (Tuple Int)))
needLevel     = (set.singleton (tuple 0))
riskLevel     = (set.singleton (tuple 0))
Measure     = (set.singleton (tuple 0 true 0 true true true true true true 0 true true true true 0 true))
****************************************************************************************************
