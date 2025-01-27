Formula A: (set.all (lambda ((tuple_1 (Tuple Int))) (>= ((_ tuple.select 0) tuple_1) 0)) time)
Formula A: Bool
lhs: (<= ((_ tuple.select 0) tuple_2) 2)
rhs: (>= ((_ tuple.select 0) tuple_2) 0)
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.all (lambda ((tuple_2 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_2))) (and (<= _let_1 2) (>= _let_1 0)))) needLevel)
Formula A: Bool
lhs: (<= ((_ tuple.select 0) tuple_3) 2)
rhs: (>= ((_ tuple.select 0) tuple_3) 0)
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.all (lambda ((tuple_3 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_3))) (and (<= _let_1 2) (>= _let_1 0)))) riskLevel)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_6) (+ ((_ tuple.select 0) tuple_4) 0))
rhs: (<= ((_ tuple.select 0) tuple_6) (+ ((_ tuple.select 0) tuple_4) 600))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_6 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_4))) (let ((_let_2 ((_ tuple.select 0) tuple_6))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 600)))))) InformUser)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_7) (+ ((_ tuple.select 0) tuple_4) 0))
rhs: (<= ((_ tuple.select 0) tuple_7) (+ ((_ tuple.select 0) tuple_4) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_7 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_4) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_7))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindLater)
Formula A: Bool
lhs: ((_ tuple.select 1) tuple_5)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and ((_ tuple.select 1) tuple_5) true)
rhs: (set.some (lambda ((tuple_7 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_4) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_7))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindLater)
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
rhs: (set.some (lambda ((tuple_6 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_4))) (let ((_let_2 ((_ tuple.select 0) tuple_6))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 600)))))) InformUser)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not ((_ tuple.select 1) tuple_5)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not ((_ tuple.select 1) tuple_5)) true)) (set.some (lambda ((tuple_6 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_4))) (let ((_let_2 ((_ tuple.select 0) tuple_6))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 600)))))) InformUser))
rhs: (=> (and ((_ tuple.select 1) tuple_5) true) (set.some (lambda ((tuple_7 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_4) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_7))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindLater))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 ((_ tuple.select 1) tuple_5))) (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_6 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_4))) (let ((_let_2 ((_ tuple.select 0) tuple_6))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 600)))))) InformUser)) (=> (and _let_1 true) (set.some (lambda ((tuple_7 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_4) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_7))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindLater))))
rhs: (= ((_ tuple.select 0) tuple_4) ((_ tuple.select 0) tuple_5))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_5 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 ((_ tuple.select 1) tuple_5))) (and (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_6 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_4))) (let ((_let_2 ((_ tuple.select 0) tuple_6))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 600)))))) InformUser)) (=> (and _let_1 true) (set.some (lambda ((tuple_7 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_4) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_7))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindLater))) (= ((_ tuple.select 0) tuple_4) ((_ tuple.select 0) tuple_5))))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_4 (Tuple Int))) (set.some (lambda ((tuple_5 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 ((_ tuple.select 1) tuple_5))) (and (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_6 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_4))) (let ((_let_2 ((_ tuple.select 0) tuple_6))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 600)))))) InformUser)) (=> (and _let_1 true) (set.some (lambda ((tuple_7 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_4) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_7))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindLater))) (= ((_ tuple.select 0) tuple_4) ((_ tuple.select 0) tuple_5))))) Measure)) MonitorMealTime)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_10) (+ ((_ tuple.select 0) tuple_8) 0))
rhs: (<= ((_ tuple.select 0) tuple_10) (+ ((_ tuple.select 0) tuple_8) 600))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_10 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_8))) (let ((_let_2 ((_ tuple.select 0) tuple_10))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 600)))))) InformUser)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_11) (+ ((_ tuple.select 0) tuple_8) 0))
rhs: (<= ((_ tuple.select 0) tuple_11) (+ ((_ tuple.select 0) tuple_8) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_11 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_8) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_11))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindLater)
Formula A: Bool
lhs: ((_ tuple.select 1) tuple_9)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and ((_ tuple.select 1) tuple_9) true)
rhs: (set.some (lambda ((tuple_11 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_8) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_11))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindLater)
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
rhs: (set.some (lambda ((tuple_10 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_8))) (let ((_let_2 ((_ tuple.select 0) tuple_10))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 600)))))) InformUser)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not ((_ tuple.select 1) tuple_9)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not ((_ tuple.select 1) tuple_9)) true)) (set.some (lambda ((tuple_10 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_8))) (let ((_let_2 ((_ tuple.select 0) tuple_10))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 600)))))) InformUser))
rhs: (=> (and ((_ tuple.select 1) tuple_9) true) (set.some (lambda ((tuple_11 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_8) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_11))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindLater))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 ((_ tuple.select 1) tuple_9))) (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_10 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_8))) (let ((_let_2 ((_ tuple.select 0) tuple_10))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 600)))))) InformUser)) (=> (and _let_1 true) (set.some (lambda ((tuple_11 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_8) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_11))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindLater)))))
rhs: (= ((_ tuple.select 0) tuple_8) ((_ tuple.select 0) tuple_9))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_9 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 ((_ tuple.select 1) tuple_9))) (and (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_10 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_8))) (let ((_let_2 ((_ tuple.select 0) tuple_10))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 600)))))) InformUser)) (=> (and _let_1 true) (set.some (lambda ((tuple_11 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_8) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_11))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindLater)))) (= ((_ tuple.select 0) tuple_8) ((_ tuple.select 0) tuple_9))))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_8 (Tuple Int))) (set.some (lambda ((tuple_9 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 ((_ tuple.select 1) tuple_9))) (and (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_10 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_8))) (let ((_let_2 ((_ tuple.select 0) tuple_10))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 600)))))) InformUser)) (=> (and _let_1 true) (set.some (lambda ((tuple_11 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_8) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_11))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindLater)))) (= ((_ tuple.select 0) tuple_8) ((_ tuple.select 0) tuple_9))))) Measure)) MonitorMealTime)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_12 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_12) ((_ tuple.select 1) tuple_12))) (rel.product MonitorMealTime Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_13 (Tuple Int))) true) MonitorMealTime)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_14) ((_ tuple.select 0) tuple_15))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_15 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_14) ((_ tuple.select 0) tuple_15)))) MonitorMealTime)
Formula A: Bool
lhs: (set.all (lambda ((tuple_15 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_14) ((_ tuple.select 0) tuple_15)))) MonitorMealTime)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_14 (Tuple Int))) (and (set.all (lambda ((tuple_15 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_14) ((_ tuple.select 0) tuple_15)))) MonitorMealTime) true)) MonitorMealTime)
Formula A: Bool
lhs: (set.some (lambda ((tuple_13 (Tuple Int))) true) MonitorMealTime)
rhs: (set.some (lambda ((tuple_14 (Tuple Int))) (and (set.all (lambda ((tuple_15 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_14) ((_ tuple.select 0) tuple_15)))) MonitorMealTime) true)) MonitorMealTime)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_18) (+ ((_ tuple.select 0) tuple_16) 0))
rhs: (<= ((_ tuple.select 0) tuple_18) (+ ((_ tuple.select 0) tuple_16) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_18 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_16) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_18))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) TrackTime)
Formula A: Bool
lhs: (set.some (lambda ((tuple_18 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_16) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_18))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) TrackTime)
rhs: (= ((_ tuple.select 0) tuple_16) ((_ tuple.select 0) tuple_17))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_17 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_18 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_16) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_18))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) TrackTime) (= ((_ tuple.select 0) tuple_16) ((_ tuple.select 0) tuple_17)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_16 (Tuple Int))) (set.some (lambda ((tuple_17 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_18 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_16) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_18))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) TrackTime) (= ((_ tuple.select 0) tuple_16) ((_ tuple.select 0) tuple_17)))) Measure)) AgentDeployed)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_21) (+ ((_ tuple.select 0) tuple_19) 0))
rhs: (<= ((_ tuple.select 0) tuple_21) (+ ((_ tuple.select 0) tuple_19) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_21 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_19) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_21))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) TrackTime)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_21 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_19) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_21))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) TrackTime))
rhs: (= ((_ tuple.select 0) tuple_19) ((_ tuple.select 0) tuple_20))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_20 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_21 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_19) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_21))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) TrackTime)) (= ((_ tuple.select 0) tuple_19) ((_ tuple.select 0) tuple_20)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_19 (Tuple Int))) (set.some (lambda ((tuple_20 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_21 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_19) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_21))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) TrackTime)) (= ((_ tuple.select 0) tuple_19) ((_ tuple.select 0) tuple_20)))) Measure)) AgentDeployed)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_22 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_22) ((_ tuple.select 1) tuple_22))) (rel.product AgentDeployed Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_23 (Tuple Int))) true) AgentDeployed)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_24) ((_ tuple.select 0) tuple_25))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_25 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_24) ((_ tuple.select 0) tuple_25)))) AgentDeployed)
Formula A: Bool
lhs: (set.all (lambda ((tuple_25 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_24) ((_ tuple.select 0) tuple_25)))) AgentDeployed)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_24 (Tuple Int))) (and (set.all (lambda ((tuple_25 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_24) ((_ tuple.select 0) tuple_25)))) AgentDeployed) true)) AgentDeployed)
Formula A: Bool
lhs: (set.some (lambda ((tuple_23 (Tuple Int))) true) AgentDeployed)
rhs: (set.some (lambda ((tuple_24 (Tuple Int))) (and (set.all (lambda ((tuple_25 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_24) ((_ tuple.select 0) tuple_25)))) AgentDeployed) true)) AgentDeployed)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_28) (+ ((_ tuple.select 0) tuple_26) 0))
rhs: (<= ((_ tuple.select 0) tuple_28) (+ ((_ tuple.select 0) tuple_26) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_28 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_26) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_28))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver)
Formula A: Bool
lhs: (set.some (lambda ((tuple_28 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_26) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_28))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver)
rhs: (not (> ((_ tuple.select 2) tuple_27) 28800))
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (or (set.some (lambda ((tuple_28 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_26) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_28))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver) (not (> ((_ tuple.select 2) tuple_27) 28800)))
rhs: (= ((_ tuple.select 0) tuple_26) ((_ tuple.select 0) tuple_27))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_27 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (set.some (lambda ((tuple_28 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_26) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_28))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver) (not (> ((_ tuple.select 2) tuple_27) 28800))) (= ((_ tuple.select 0) tuple_26) ((_ tuple.select 0) tuple_27)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_26 (Tuple Int))) (set.some (lambda ((tuple_27 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (set.some (lambda ((tuple_28 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_26) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_28))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver) (not (> ((_ tuple.select 2) tuple_27) 28800))) (= ((_ tuple.select 0) tuple_26) ((_ tuple.select 0) tuple_27)))) Measure)) TrackTime)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_31) (+ ((_ tuple.select 0) tuple_29) 0))
rhs: (<= ((_ tuple.select 0) tuple_31) (+ ((_ tuple.select 0) tuple_29) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_31 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_29) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_31))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_31 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_29) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_31))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver))
rhs: (> ((_ tuple.select 2) tuple_30) 28800)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (set.some (lambda ((tuple_31 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_29) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_31))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver)) (> ((_ tuple.select 2) tuple_30) 28800))
rhs: (= ((_ tuple.select 0) tuple_29) ((_ tuple.select 0) tuple_30))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_30 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (set.some (lambda ((tuple_31 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_29) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_31))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver)) (> ((_ tuple.select 2) tuple_30) 28800)) (= ((_ tuple.select 0) tuple_29) ((_ tuple.select 0) tuple_30)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_29 (Tuple Int))) (set.some (lambda ((tuple_30 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (set.some (lambda ((tuple_31 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_29) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_31))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver)) (> ((_ tuple.select 2) tuple_30) 28800)) (= ((_ tuple.select 0) tuple_29) ((_ tuple.select 0) tuple_30)))) Measure)) TrackTime)
Formula A: Bool
lhs: (> ((_ tuple.select 3) tuple_32) 28800)
rhs: (= ((_ tuple.select 0) tuple_32) ((_ tuple.select 1) tuple_32))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula B: (set.some (lambda ((tuple_32 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 3) tuple_32) 28800) (= ((_ tuple.select 0) tuple_32) ((_ tuple.select 1) tuple_32)))) (rel.product TrackTime Measure))
Formula B: Bool
lhs: (> ((_ tuple.select 2) tuple_34) 28800)
rhs: (= ((_ tuple.select 0) tuple_34) ((_ tuple.select 0) tuple_33))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_34 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_34) 28800) (= ((_ tuple.select 0) tuple_34) ((_ tuple.select 0) tuple_33)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_33 (Tuple Int))) (set.some (lambda ((tuple_34 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_34) 28800) (= ((_ tuple.select 0) tuple_34) ((_ tuple.select 0) tuple_33)))) Measure)) TrackTime)
Formula A: Bool
lhs: (> ((_ tuple.select 2) tuple_36) 28800)
rhs: (= ((_ tuple.select 0) tuple_36) ((_ tuple.select 0) tuple_35))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_36 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_36) 28800) (= ((_ tuple.select 0) tuple_36) ((_ tuple.select 0) tuple_35)))) Measure)
Formula A: Bool
lhs: (> ((_ tuple.select 2) tuple_38) 28800)
rhs: (= ((_ tuple.select 0) tuple_38) ((_ tuple.select 0) tuple_37))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_38 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_38) 28800) (= ((_ tuple.select 0) tuple_38) ((_ tuple.select 0) tuple_37)))) Measure)
Formula A: Bool
lhs: (set.some (lambda ((tuple_38 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_38) 28800) (= ((_ tuple.select 0) tuple_38) ((_ tuple.select 0) tuple_37)))) Measure)
rhs: (>= ((_ tuple.select 0) tuple_35) ((_ tuple.select 0) tuple_37))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_37 (Tuple Int))) (=> (set.some (lambda ((tuple_38 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_38) 28800) (= ((_ tuple.select 0) tuple_38) ((_ tuple.select 0) tuple_37)))) Measure) (>= ((_ tuple.select 0) tuple_35) ((_ tuple.select 0) tuple_37)))) TrackTime)
Formula A: Bool
lhs: (set.all (lambda ((tuple_37 (Tuple Int))) (=> (set.some (lambda ((tuple_38 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_38) 28800) (= ((_ tuple.select 0) tuple_38) ((_ tuple.select 0) tuple_37)))) Measure) (>= ((_ tuple.select 0) tuple_35) ((_ tuple.select 0) tuple_37)))) TrackTime)
rhs: (set.some (lambda ((tuple_36 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_36) 28800) (= ((_ tuple.select 0) tuple_36) ((_ tuple.select 0) tuple_35)))) Measure)
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_35 (Tuple Int))) (and (set.all (lambda ((tuple_37 (Tuple Int))) (=> (set.some (lambda ((tuple_38 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_38) 28800) (= ((_ tuple.select 0) tuple_38) ((_ tuple.select 0) tuple_37)))) Measure) (>= ((_ tuple.select 0) tuple_35) ((_ tuple.select 0) tuple_37)))) TrackTime) (set.some (lambda ((tuple_36 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_36) 28800) (= ((_ tuple.select 0) tuple_36) ((_ tuple.select 0) tuple_35)))) Measure))) TrackTime)
Formula A: Bool
lhs: (set.some (lambda ((tuple_33 (Tuple Int))) (set.some (lambda ((tuple_34 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_34) 28800) (= ((_ tuple.select 0) tuple_34) ((_ tuple.select 0) tuple_33)))) Measure)) TrackTime)
rhs: (set.some (lambda ((tuple_35 (Tuple Int))) (and (set.all (lambda ((tuple_37 (Tuple Int))) (=> (set.some (lambda ((tuple_38 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_38) 28800) (= ((_ tuple.select 0) tuple_38) ((_ tuple.select 0) tuple_37)))) Measure) (>= ((_ tuple.select 0) tuple_35) ((_ tuple.select 0) tuple_37)))) TrackTime) (set.some (lambda ((tuple_36 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_36) 28800) (= ((_ tuple.select 0) tuple_36) ((_ tuple.select 0) tuple_35)))) Measure))) TrackTime)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_41) (+ ((_ tuple.select 0) tuple_39) 0))
rhs: (<= ((_ tuple.select 0) tuple_41) (+ ((_ tuple.select 0) tuple_39) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_41 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_39) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_41))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) GiveSuggestion)
Formula A: Bool
lhs: (set.some (lambda ((tuple_41 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_39) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_41))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) GiveSuggestion)
rhs: (not (> ((_ tuple.select 2) tuple_40) 28800))
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (or (set.some (lambda ((tuple_41 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_39) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_41))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) GiveSuggestion) (not (> ((_ tuple.select 2) tuple_40) 28800)))
rhs: (= ((_ tuple.select 0) tuple_39) ((_ tuple.select 0) tuple_40))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_40 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (set.some (lambda ((tuple_41 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_39) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_41))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) GiveSuggestion) (not (> ((_ tuple.select 2) tuple_40) 28800))) (= ((_ tuple.select 0) tuple_39) ((_ tuple.select 0) tuple_40)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_39 (Tuple Int))) (set.some (lambda ((tuple_40 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (set.some (lambda ((tuple_41 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_39) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_41))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) GiveSuggestion) (not (> ((_ tuple.select 2) tuple_40) 28800))) (= ((_ tuple.select 0) tuple_39) ((_ tuple.select 0) tuple_40)))) Measure)) TrackTime)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_44) (+ ((_ tuple.select 0) tuple_42) 0))
rhs: (<= ((_ tuple.select 0) tuple_44) (+ ((_ tuple.select 0) tuple_42) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_44 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_42) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_44))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) GiveSuggestion)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_44 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_42) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_44))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) GiveSuggestion))
rhs: (> ((_ tuple.select 2) tuple_43) 28800)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (set.some (lambda ((tuple_44 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_42) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_44))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) GiveSuggestion)) (> ((_ tuple.select 2) tuple_43) 28800))
rhs: (= ((_ tuple.select 0) tuple_42) ((_ tuple.select 0) tuple_43))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_43 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (set.some (lambda ((tuple_44 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_42) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_44))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) GiveSuggestion)) (> ((_ tuple.select 2) tuple_43) 28800)) (= ((_ tuple.select 0) tuple_42) ((_ tuple.select 0) tuple_43)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_42 (Tuple Int))) (set.some (lambda ((tuple_43 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (set.some (lambda ((tuple_44 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_42) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_44))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) GiveSuggestion)) (> ((_ tuple.select 2) tuple_43) 28800)) (= ((_ tuple.select 0) tuple_42) ((_ tuple.select 0) tuple_43)))) Measure)) TrackTime)
Formula A: Bool
lhs: (> ((_ tuple.select 3) tuple_45) 28800)
rhs: (= ((_ tuple.select 0) tuple_45) ((_ tuple.select 1) tuple_45))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula B: (set.some (lambda ((tuple_45 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 3) tuple_45) 28800) (= ((_ tuple.select 0) tuple_45) ((_ tuple.select 1) tuple_45)))) (rel.product TrackTime Measure))
Formula B: Bool
lhs: (> ((_ tuple.select 2) tuple_47) 28800)
rhs: (= ((_ tuple.select 0) tuple_47) ((_ tuple.select 0) tuple_46))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_47 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_47) 28800) (= ((_ tuple.select 0) tuple_47) ((_ tuple.select 0) tuple_46)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_46 (Tuple Int))) (set.some (lambda ((tuple_47 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_47) 28800) (= ((_ tuple.select 0) tuple_47) ((_ tuple.select 0) tuple_46)))) Measure)) TrackTime)
Formula A: Bool
lhs: (> ((_ tuple.select 2) tuple_49) 28800)
rhs: (= ((_ tuple.select 0) tuple_49) ((_ tuple.select 0) tuple_48))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_49 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_49) 28800) (= ((_ tuple.select 0) tuple_49) ((_ tuple.select 0) tuple_48)))) Measure)
Formula A: Bool
lhs: (> ((_ tuple.select 2) tuple_51) 28800)
rhs: (= ((_ tuple.select 0) tuple_51) ((_ tuple.select 0) tuple_50))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_51 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_51) 28800) (= ((_ tuple.select 0) tuple_51) ((_ tuple.select 0) tuple_50)))) Measure)
Formula A: Bool
lhs: (set.some (lambda ((tuple_51 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_51) 28800) (= ((_ tuple.select 0) tuple_51) ((_ tuple.select 0) tuple_50)))) Measure)
rhs: (>= ((_ tuple.select 0) tuple_48) ((_ tuple.select 0) tuple_50))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_50 (Tuple Int))) (=> (set.some (lambda ((tuple_51 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_51) 28800) (= ((_ tuple.select 0) tuple_51) ((_ tuple.select 0) tuple_50)))) Measure) (>= ((_ tuple.select 0) tuple_48) ((_ tuple.select 0) tuple_50)))) TrackTime)
Formula A: Bool
lhs: (set.all (lambda ((tuple_50 (Tuple Int))) (=> (set.some (lambda ((tuple_51 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_51) 28800) (= ((_ tuple.select 0) tuple_51) ((_ tuple.select 0) tuple_50)))) Measure) (>= ((_ tuple.select 0) tuple_48) ((_ tuple.select 0) tuple_50)))) TrackTime)
rhs: (set.some (lambda ((tuple_49 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_49) 28800) (= ((_ tuple.select 0) tuple_49) ((_ tuple.select 0) tuple_48)))) Measure)
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_48 (Tuple Int))) (and (set.all (lambda ((tuple_50 (Tuple Int))) (=> (set.some (lambda ((tuple_51 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_51) 28800) (= ((_ tuple.select 0) tuple_51) ((_ tuple.select 0) tuple_50)))) Measure) (>= ((_ tuple.select 0) tuple_48) ((_ tuple.select 0) tuple_50)))) TrackTime) (set.some (lambda ((tuple_49 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_49) 28800) (= ((_ tuple.select 0) tuple_49) ((_ tuple.select 0) tuple_48)))) Measure))) TrackTime)
Formula A: Bool
lhs: (set.some (lambda ((tuple_46 (Tuple Int))) (set.some (lambda ((tuple_47 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_47) 28800) (= ((_ tuple.select 0) tuple_47) ((_ tuple.select 0) tuple_46)))) Measure)) TrackTime)
rhs: (set.some (lambda ((tuple_48 (Tuple Int))) (and (set.all (lambda ((tuple_50 (Tuple Int))) (=> (set.some (lambda ((tuple_51 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_51) 28800) (= ((_ tuple.select 0) tuple_51) ((_ tuple.select 0) tuple_50)))) Measure) (>= ((_ tuple.select 0) tuple_48) ((_ tuple.select 0) tuple_50)))) TrackTime) (set.some (lambda ((tuple_49 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (> ((_ tuple.select 2) tuple_49) 28800) (= ((_ tuple.select 0) tuple_49) ((_ tuple.select 0) tuple_48)))) Measure))) TrackTime)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_54) (+ ((_ tuple.select 0) tuple_52) 0))
rhs: (<= ((_ tuple.select 0) tuple_54) (+ ((_ tuple.select 0) tuple_52) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_54 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_52) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_54))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskCallHelp)
Formula A: Bool
lhs: (set.some (lambda ((tuple_54 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_52) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_54))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskCallHelp)
rhs: (= ((_ tuple.select 0) tuple_52) ((_ tuple.select 0) tuple_53))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_53 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_54 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_52) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_54))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskCallHelp) (= ((_ tuple.select 0) tuple_52) ((_ tuple.select 0) tuple_53)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_52 (Tuple Int))) (set.some (lambda ((tuple_53 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_54 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_52) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_54))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskCallHelp) (= ((_ tuple.select 0) tuple_52) ((_ tuple.select 0) tuple_53)))) Measure)) HumanOnFloor)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_57) (+ ((_ tuple.select 0) tuple_55) 0))
rhs: (<= ((_ tuple.select 0) tuple_57) (+ ((_ tuple.select 0) tuple_55) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_57 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_55) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_57))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskCallHelp)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_57 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_55) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_57))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskCallHelp))
rhs: (= ((_ tuple.select 0) tuple_55) ((_ tuple.select 0) tuple_56))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_56 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_57 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_55) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_57))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskCallHelp)) (= ((_ tuple.select 0) tuple_55) ((_ tuple.select 0) tuple_56)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_55 (Tuple Int))) (set.some (lambda ((tuple_56 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_57 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_55) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_57))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskCallHelp)) (= ((_ tuple.select 0) tuple_55) ((_ tuple.select 0) tuple_56)))) Measure)) HumanOnFloor)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_58 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_58) ((_ tuple.select 1) tuple_58))) (rel.product HumanOnFloor Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_59 (Tuple Int))) true) HumanOnFloor)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_60) ((_ tuple.select 0) tuple_61))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_61 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_60) ((_ tuple.select 0) tuple_61)))) HumanOnFloor)
Formula A: Bool
lhs: (set.all (lambda ((tuple_61 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_60) ((_ tuple.select 0) tuple_61)))) HumanOnFloor)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_60 (Tuple Int))) (and (set.all (lambda ((tuple_61 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_60) ((_ tuple.select 0) tuple_61)))) HumanOnFloor) true)) HumanOnFloor)
Formula A: Bool
lhs: (set.some (lambda ((tuple_59 (Tuple Int))) true) HumanOnFloor)
rhs: (set.some (lambda ((tuple_60 (Tuple Int))) (and (set.all (lambda ((tuple_61 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_60) ((_ tuple.select 0) tuple_61)))) HumanOnFloor) true)) HumanOnFloor)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_64) (+ ((_ tuple.select 0) tuple_62) 0))
rhs: (<= ((_ tuple.select 0) tuple_64) (+ ((_ tuple.select 0) tuple_62) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_64 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_62) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_64))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CallEmergencyServices)
Formula A: Bool
lhs: (set.some (lambda ((tuple_64 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_62) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_64))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CallEmergencyServices)
rhs: (not (not ((_ tuple.select 10) tuple_63)))
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (or (set.some (lambda ((tuple_64 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_62) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_64))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CallEmergencyServices) (not (not ((_ tuple.select 10) tuple_63))))
rhs: (= ((_ tuple.select 0) tuple_62) ((_ tuple.select 0) tuple_63))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_63 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (set.some (lambda ((tuple_64 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_62) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_64))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CallEmergencyServices) (not (not ((_ tuple.select 10) tuple_63)))) (= ((_ tuple.select 0) tuple_62) ((_ tuple.select 0) tuple_63)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_62 (Tuple Int))) (set.some (lambda ((tuple_63 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (set.some (lambda ((tuple_64 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_62) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_64))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CallEmergencyServices) (not (not ((_ tuple.select 10) tuple_63)))) (= ((_ tuple.select 0) tuple_62) ((_ tuple.select 0) tuple_63)))) Measure)) AskCallHelp)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_67) (+ ((_ tuple.select 0) tuple_65) 0))
rhs: (<= ((_ tuple.select 0) tuple_67) (+ ((_ tuple.select 0) tuple_65) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_67 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_65) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_67))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CallEmergencyServices)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_67 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_65) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_67))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CallEmergencyServices))
rhs: (not ((_ tuple.select 10) tuple_66))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (set.some (lambda ((tuple_67 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_65) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_67))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CallEmergencyServices)) (not ((_ tuple.select 10) tuple_66)))
rhs: (= ((_ tuple.select 0) tuple_65) ((_ tuple.select 0) tuple_66))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_66 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (set.some (lambda ((tuple_67 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_65) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_67))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CallEmergencyServices)) (not ((_ tuple.select 10) tuple_66))) (= ((_ tuple.select 0) tuple_65) ((_ tuple.select 0) tuple_66)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_65 (Tuple Int))) (set.some (lambda ((tuple_66 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (set.some (lambda ((tuple_67 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_65) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_67))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CallEmergencyServices)) (not ((_ tuple.select 10) tuple_66))) (= ((_ tuple.select 0) tuple_65) ((_ tuple.select 0) tuple_66)))) Measure)) AskCallHelp)
Formula A: Bool
lhs: (not ((_ tuple.select 11) tuple_68))
rhs: (= ((_ tuple.select 0) tuple_68) ((_ tuple.select 1) tuple_68))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula B: (set.some (lambda ((tuple_68 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 11) tuple_68)) (= ((_ tuple.select 0) tuple_68) ((_ tuple.select 1) tuple_68)))) (rel.product AskCallHelp Measure))
Formula B: Bool
lhs: (not ((_ tuple.select 10) tuple_70))
rhs: (= ((_ tuple.select 0) tuple_70) ((_ tuple.select 0) tuple_69))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_70 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_70)) (= ((_ tuple.select 0) tuple_70) ((_ tuple.select 0) tuple_69)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_69 (Tuple Int))) (set.some (lambda ((tuple_70 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_70)) (= ((_ tuple.select 0) tuple_70) ((_ tuple.select 0) tuple_69)))) Measure)) AskCallHelp)
Formula A: Bool
lhs: (not ((_ tuple.select 10) tuple_72))
rhs: (= ((_ tuple.select 0) tuple_72) ((_ tuple.select 0) tuple_71))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_72 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_72)) (= ((_ tuple.select 0) tuple_72) ((_ tuple.select 0) tuple_71)))) Measure)
Formula A: Bool
lhs: (not ((_ tuple.select 10) tuple_74))
rhs: (= ((_ tuple.select 0) tuple_74) ((_ tuple.select 0) tuple_73))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_74 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_74)) (= ((_ tuple.select 0) tuple_74) ((_ tuple.select 0) tuple_73)))) Measure)
Formula A: Bool
lhs: (set.some (lambda ((tuple_74 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_74)) (= ((_ tuple.select 0) tuple_74) ((_ tuple.select 0) tuple_73)))) Measure)
rhs: (>= ((_ tuple.select 0) tuple_71) ((_ tuple.select 0) tuple_73))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_73 (Tuple Int))) (=> (set.some (lambda ((tuple_74 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_74)) (= ((_ tuple.select 0) tuple_74) ((_ tuple.select 0) tuple_73)))) Measure) (>= ((_ tuple.select 0) tuple_71) ((_ tuple.select 0) tuple_73)))) AskCallHelp)
Formula A: Bool
lhs: (set.all (lambda ((tuple_73 (Tuple Int))) (=> (set.some (lambda ((tuple_74 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_74)) (= ((_ tuple.select 0) tuple_74) ((_ tuple.select 0) tuple_73)))) Measure) (>= ((_ tuple.select 0) tuple_71) ((_ tuple.select 0) tuple_73)))) AskCallHelp)
rhs: (set.some (lambda ((tuple_72 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_72)) (= ((_ tuple.select 0) tuple_72) ((_ tuple.select 0) tuple_71)))) Measure)
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_71 (Tuple Int))) (and (set.all (lambda ((tuple_73 (Tuple Int))) (=> (set.some (lambda ((tuple_74 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_74)) (= ((_ tuple.select 0) tuple_74) ((_ tuple.select 0) tuple_73)))) Measure) (>= ((_ tuple.select 0) tuple_71) ((_ tuple.select 0) tuple_73)))) AskCallHelp) (set.some (lambda ((tuple_72 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_72)) (= ((_ tuple.select 0) tuple_72) ((_ tuple.select 0) tuple_71)))) Measure))) AskCallHelp)
Formula A: Bool
lhs: (set.some (lambda ((tuple_69 (Tuple Int))) (set.some (lambda ((tuple_70 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_70)) (= ((_ tuple.select 0) tuple_70) ((_ tuple.select 0) tuple_69)))) Measure)) AskCallHelp)
rhs: (set.some (lambda ((tuple_71 (Tuple Int))) (and (set.all (lambda ((tuple_73 (Tuple Int))) (=> (set.some (lambda ((tuple_74 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_74)) (= ((_ tuple.select 0) tuple_74) ((_ tuple.select 0) tuple_73)))) Measure) (>= ((_ tuple.select 0) tuple_71) ((_ tuple.select 0) tuple_73)))) AskCallHelp) (set.some (lambda ((tuple_72 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_72)) (= ((_ tuple.select 0) tuple_72) ((_ tuple.select 0) tuple_71)))) Measure))) AskCallHelp)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_77) (+ ((_ tuple.select 0) tuple_75) 0))
rhs: (<= ((_ tuple.select 0) tuple_77) (+ ((_ tuple.select 0) tuple_75) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_77 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_75) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_77))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver)
Formula A: Bool
lhs: (set.some (lambda ((tuple_77 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_75) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_77))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver)
rhs: (not (not ((_ tuple.select 10) tuple_76)))
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (or (set.some (lambda ((tuple_77 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_75) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_77))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver) (not (not ((_ tuple.select 10) tuple_76))))
rhs: (= ((_ tuple.select 0) tuple_75) ((_ tuple.select 0) tuple_76))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_76 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (set.some (lambda ((tuple_77 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_75) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_77))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver) (not (not ((_ tuple.select 10) tuple_76)))) (= ((_ tuple.select 0) tuple_75) ((_ tuple.select 0) tuple_76)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_75 (Tuple Int))) (set.some (lambda ((tuple_76 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (set.some (lambda ((tuple_77 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_75) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_77))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver) (not (not ((_ tuple.select 10) tuple_76)))) (= ((_ tuple.select 0) tuple_75) ((_ tuple.select 0) tuple_76)))) Measure)) AskCallHelp)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_80) (+ ((_ tuple.select 0) tuple_78) 0))
rhs: (<= ((_ tuple.select 0) tuple_80) (+ ((_ tuple.select 0) tuple_78) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_80 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_78) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_80))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_80 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_78) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_80))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver))
rhs: (not ((_ tuple.select 10) tuple_79))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (set.some (lambda ((tuple_80 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_78) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_80))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver)) (not ((_ tuple.select 10) tuple_79)))
rhs: (= ((_ tuple.select 0) tuple_78) ((_ tuple.select 0) tuple_79))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_79 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (set.some (lambda ((tuple_80 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_78) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_80))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver)) (not ((_ tuple.select 10) tuple_79))) (= ((_ tuple.select 0) tuple_78) ((_ tuple.select 0) tuple_79)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_78 (Tuple Int))) (set.some (lambda ((tuple_79 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (set.some (lambda ((tuple_80 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_78) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_80))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver)) (not ((_ tuple.select 10) tuple_79))) (= ((_ tuple.select 0) tuple_78) ((_ tuple.select 0) tuple_79)))) Measure)) AskCallHelp)
Formula A: Bool
lhs: (not ((_ tuple.select 11) tuple_81))
rhs: (= ((_ tuple.select 0) tuple_81) ((_ tuple.select 1) tuple_81))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula B: (set.some (lambda ((tuple_81 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 11) tuple_81)) (= ((_ tuple.select 0) tuple_81) ((_ tuple.select 1) tuple_81)))) (rel.product AskCallHelp Measure))
Formula B: Bool
lhs: (not ((_ tuple.select 10) tuple_83))
rhs: (= ((_ tuple.select 0) tuple_83) ((_ tuple.select 0) tuple_82))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_83 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_83)) (= ((_ tuple.select 0) tuple_83) ((_ tuple.select 0) tuple_82)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_82 (Tuple Int))) (set.some (lambda ((tuple_83 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_83)) (= ((_ tuple.select 0) tuple_83) ((_ tuple.select 0) tuple_82)))) Measure)) AskCallHelp)
Formula A: Bool
lhs: (not ((_ tuple.select 10) tuple_85))
rhs: (= ((_ tuple.select 0) tuple_85) ((_ tuple.select 0) tuple_84))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_85 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_85)) (= ((_ tuple.select 0) tuple_85) ((_ tuple.select 0) tuple_84)))) Measure)
Formula A: Bool
lhs: (not ((_ tuple.select 10) tuple_87))
rhs: (= ((_ tuple.select 0) tuple_87) ((_ tuple.select 0) tuple_86))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_87 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_87)) (= ((_ tuple.select 0) tuple_87) ((_ tuple.select 0) tuple_86)))) Measure)
Formula A: Bool
lhs: (set.some (lambda ((tuple_87 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_87)) (= ((_ tuple.select 0) tuple_87) ((_ tuple.select 0) tuple_86)))) Measure)
rhs: (>= ((_ tuple.select 0) tuple_84) ((_ tuple.select 0) tuple_86))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_86 (Tuple Int))) (=> (set.some (lambda ((tuple_87 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_87)) (= ((_ tuple.select 0) tuple_87) ((_ tuple.select 0) tuple_86)))) Measure) (>= ((_ tuple.select 0) tuple_84) ((_ tuple.select 0) tuple_86)))) AskCallHelp)
Formula A: Bool
lhs: (set.all (lambda ((tuple_86 (Tuple Int))) (=> (set.some (lambda ((tuple_87 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_87)) (= ((_ tuple.select 0) tuple_87) ((_ tuple.select 0) tuple_86)))) Measure) (>= ((_ tuple.select 0) tuple_84) ((_ tuple.select 0) tuple_86)))) AskCallHelp)
rhs: (set.some (lambda ((tuple_85 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_85)) (= ((_ tuple.select 0) tuple_85) ((_ tuple.select 0) tuple_84)))) Measure)
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_84 (Tuple Int))) (and (set.all (lambda ((tuple_86 (Tuple Int))) (=> (set.some (lambda ((tuple_87 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_87)) (= ((_ tuple.select 0) tuple_87) ((_ tuple.select 0) tuple_86)))) Measure) (>= ((_ tuple.select 0) tuple_84) ((_ tuple.select 0) tuple_86)))) AskCallHelp) (set.some (lambda ((tuple_85 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_85)) (= ((_ tuple.select 0) tuple_85) ((_ tuple.select 0) tuple_84)))) Measure))) AskCallHelp)
Formula A: Bool
lhs: (set.some (lambda ((tuple_82 (Tuple Int))) (set.some (lambda ((tuple_83 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_83)) (= ((_ tuple.select 0) tuple_83) ((_ tuple.select 0) tuple_82)))) Measure)) AskCallHelp)
rhs: (set.some (lambda ((tuple_84 (Tuple Int))) (and (set.all (lambda ((tuple_86 (Tuple Int))) (=> (set.some (lambda ((tuple_87 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_87)) (= ((_ tuple.select 0) tuple_87) ((_ tuple.select 0) tuple_86)))) Measure) (>= ((_ tuple.select 0) tuple_84) ((_ tuple.select 0) tuple_86)))) AskCallHelp) (set.some (lambda ((tuple_85 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 10) tuple_85)) (= ((_ tuple.select 0) tuple_85) ((_ tuple.select 0) tuple_84)))) Measure))) AskCallHelp)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_90) (+ ((_ tuple.select 0) tuple_88) 0))
rhs: (<= ((_ tuple.select 0) tuple_90) (+ ((_ tuple.select 0) tuple_88) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_90 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_88) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_90))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)
Formula A: Bool
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
rhs: (set.some (lambda ((tuple_90 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_88) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_90))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not ((_ tuple.select 1) tuple_89)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not ((_ tuple.select 1) tuple_89)) true)) (set.some (lambda ((tuple_90 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_88) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_90))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser))
rhs: (=> (and ((_ tuple.select 1) tuple_89) true) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 ((_ tuple.select 1) tuple_89))) (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_90 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_88) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_90))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)) (=> (and _let_1 true) true)))
rhs: (not (not ((_ tuple.select 11) tuple_89)))
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (let ((_let_1 ((_ tuple.select 1) tuple_89))) (or (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_90 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_88) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_90))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)) (=> (and _let_1 true) true)) (not (not ((_ tuple.select 11) tuple_89)))))
rhs: (= ((_ tuple.select 0) tuple_88) ((_ tuple.select 0) tuple_89))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_89 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 ((_ tuple.select 1) tuple_89))) (and (or (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_90 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_88) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_90))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)) (=> (and _let_1 true) true)) (not (not ((_ tuple.select 11) tuple_89)))) (= ((_ tuple.select 0) tuple_88) ((_ tuple.select 0) tuple_89))))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_88 (Tuple Int))) (set.some (lambda ((tuple_89 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 ((_ tuple.select 1) tuple_89))) (and (or (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_90 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_88) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_90))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)) (=> (and _let_1 true) true)) (not (not ((_ tuple.select 11) tuple_89)))) (= ((_ tuple.select 0) tuple_88) ((_ tuple.select 0) tuple_89))))) Measure)) InterfereSafely)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_93) (+ ((_ tuple.select 0) tuple_91) 0))
rhs: (<= ((_ tuple.select 0) tuple_93) (+ ((_ tuple.select 0) tuple_91) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_93 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_91) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_93))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)
Formula A: Bool
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
rhs: (set.some (lambda ((tuple_93 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_91) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_93))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not ((_ tuple.select 1) tuple_92)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not ((_ tuple.select 1) tuple_92)) true)) (set.some (lambda ((tuple_93 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_91) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_93))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser))
rhs: (=> (and ((_ tuple.select 1) tuple_92) true) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 ((_ tuple.select 1) tuple_92))) (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_93 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_91) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_93))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)) (=> (and _let_1 true) true))))
rhs: (not ((_ tuple.select 11) tuple_92))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 ((_ tuple.select 1) tuple_92))) (and (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_93 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_91) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_93))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)) (=> (and _let_1 true) true))) (not ((_ tuple.select 11) tuple_92))))
rhs: (= ((_ tuple.select 0) tuple_91) ((_ tuple.select 0) tuple_92))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_92 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 ((_ tuple.select 1) tuple_92))) (and (and (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_93 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_91) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_93))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)) (=> (and _let_1 true) true))) (not ((_ tuple.select 11) tuple_92))) (= ((_ tuple.select 0) tuple_91) ((_ tuple.select 0) tuple_92))))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_91 (Tuple Int))) (set.some (lambda ((tuple_92 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 ((_ tuple.select 1) tuple_92))) (and (and (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_93 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_91) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_93))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)) (=> (and _let_1 true) true))) (not ((_ tuple.select 11) tuple_92))) (= ((_ tuple.select 0) tuple_91) ((_ tuple.select 0) tuple_92))))) Measure)) InterfereSafely)
Formula A: Bool
lhs: (not ((_ tuple.select 12) tuple_94))
rhs: (= ((_ tuple.select 0) tuple_94) ((_ tuple.select 1) tuple_94))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula B: (set.some (lambda ((tuple_94 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 12) tuple_94)) (= ((_ tuple.select 0) tuple_94) ((_ tuple.select 1) tuple_94)))) (rel.product InterfereSafely Measure))
Formula B: Bool
lhs: (not ((_ tuple.select 11) tuple_96))
rhs: (= ((_ tuple.select 0) tuple_96) ((_ tuple.select 0) tuple_95))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_96 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 11) tuple_96)) (= ((_ tuple.select 0) tuple_96) ((_ tuple.select 0) tuple_95)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_95 (Tuple Int))) (set.some (lambda ((tuple_96 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 11) tuple_96)) (= ((_ tuple.select 0) tuple_96) ((_ tuple.select 0) tuple_95)))) Measure)) InterfereSafely)
Formula A: Bool
lhs: (not ((_ tuple.select 11) tuple_98))
rhs: (= ((_ tuple.select 0) tuple_98) ((_ tuple.select 0) tuple_97))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_98 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 11) tuple_98)) (= ((_ tuple.select 0) tuple_98) ((_ tuple.select 0) tuple_97)))) Measure)
Formula A: Bool
lhs: (not ((_ tuple.select 11) tuple_100))
rhs: (= ((_ tuple.select 0) tuple_100) ((_ tuple.select 0) tuple_99))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_100 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 11) tuple_100)) (= ((_ tuple.select 0) tuple_100) ((_ tuple.select 0) tuple_99)))) Measure)
Formula A: Bool
lhs: (set.some (lambda ((tuple_100 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 11) tuple_100)) (= ((_ tuple.select 0) tuple_100) ((_ tuple.select 0) tuple_99)))) Measure)
rhs: (>= ((_ tuple.select 0) tuple_97) ((_ tuple.select 0) tuple_99))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_99 (Tuple Int))) (=> (set.some (lambda ((tuple_100 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 11) tuple_100)) (= ((_ tuple.select 0) tuple_100) ((_ tuple.select 0) tuple_99)))) Measure) (>= ((_ tuple.select 0) tuple_97) ((_ tuple.select 0) tuple_99)))) InterfereSafely)
Formula A: Bool
lhs: (set.all (lambda ((tuple_99 (Tuple Int))) (=> (set.some (lambda ((tuple_100 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 11) tuple_100)) (= ((_ tuple.select 0) tuple_100) ((_ tuple.select 0) tuple_99)))) Measure) (>= ((_ tuple.select 0) tuple_97) ((_ tuple.select 0) tuple_99)))) InterfereSafely)
rhs: (set.some (lambda ((tuple_98 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 11) tuple_98)) (= ((_ tuple.select 0) tuple_98) ((_ tuple.select 0) tuple_97)))) Measure)
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_97 (Tuple Int))) (and (set.all (lambda ((tuple_99 (Tuple Int))) (=> (set.some (lambda ((tuple_100 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 11) tuple_100)) (= ((_ tuple.select 0) tuple_100) ((_ tuple.select 0) tuple_99)))) Measure) (>= ((_ tuple.select 0) tuple_97) ((_ tuple.select 0) tuple_99)))) InterfereSafely) (set.some (lambda ((tuple_98 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 11) tuple_98)) (= ((_ tuple.select 0) tuple_98) ((_ tuple.select 0) tuple_97)))) Measure))) InterfereSafely)
Formula A: Bool
lhs: (set.some (lambda ((tuple_95 (Tuple Int))) (set.some (lambda ((tuple_96 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 11) tuple_96)) (= ((_ tuple.select 0) tuple_96) ((_ tuple.select 0) tuple_95)))) Measure)) InterfereSafely)
rhs: (set.some (lambda ((tuple_97 (Tuple Int))) (and (set.all (lambda ((tuple_99 (Tuple Int))) (=> (set.some (lambda ((tuple_100 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 11) tuple_100)) (= ((_ tuple.select 0) tuple_100) ((_ tuple.select 0) tuple_99)))) Measure) (>= ((_ tuple.select 0) tuple_97) ((_ tuple.select 0) tuple_99)))) InterfereSafely) (set.some (lambda ((tuple_98 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 11) tuple_98)) (= ((_ tuple.select 0) tuple_98) ((_ tuple.select 0) tuple_97)))) Measure))) InterfereSafely)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_103) (+ ((_ tuple.select 0) tuple_101) 0))
rhs: (<= ((_ tuple.select 0) tuple_103) (+ ((_ tuple.select 0) tuple_101) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_103 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_101) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_103))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AllowUserToCook)
Formula A: Bool
lhs: (set.some (lambda ((tuple_103 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_101) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_103))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AllowUserToCook)
rhs: (= ((_ tuple.select 0) tuple_101) ((_ tuple.select 0) tuple_102))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_102 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_103 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_101) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_103))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AllowUserToCook) (= ((_ tuple.select 0) tuple_101) ((_ tuple.select 0) tuple_102)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_101 (Tuple Int))) (set.some (lambda ((tuple_102 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_103 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_101) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_103))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AllowUserToCook) (= ((_ tuple.select 0) tuple_101) ((_ tuple.select 0) tuple_102)))) Measure)) UserWantsToCook)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_106) (+ ((_ tuple.select 0) tuple_104) 0))
rhs: (<= ((_ tuple.select 0) tuple_106) (+ ((_ tuple.select 0) tuple_104) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_106 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_104) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_106))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AllowUserToCook)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_106 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_104) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_106))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AllowUserToCook))
rhs: (= ((_ tuple.select 0) tuple_104) ((_ tuple.select 0) tuple_105))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_105 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_106 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_104) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_106))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AllowUserToCook)) (= ((_ tuple.select 0) tuple_104) ((_ tuple.select 0) tuple_105)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_104 (Tuple Int))) (set.some (lambda ((tuple_105 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_106 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_104) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_106))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AllowUserToCook)) (= ((_ tuple.select 0) tuple_104) ((_ tuple.select 0) tuple_105)))) Measure)) UserWantsToCook)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_107 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_107) ((_ tuple.select 1) tuple_107))) (rel.product UserWantsToCook Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_108 (Tuple Int))) true) UserWantsToCook)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_109) ((_ tuple.select 0) tuple_110))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_110 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_109) ((_ tuple.select 0) tuple_110)))) UserWantsToCook)
Formula A: Bool
lhs: (set.all (lambda ((tuple_110 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_109) ((_ tuple.select 0) tuple_110)))) UserWantsToCook)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_109 (Tuple Int))) (and (set.all (lambda ((tuple_110 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_109) ((_ tuple.select 0) tuple_110)))) UserWantsToCook) true)) UserWantsToCook)
Formula A: Bool
lhs: (set.some (lambda ((tuple_108 (Tuple Int))) true) UserWantsToCook)
rhs: (set.some (lambda ((tuple_109 (Tuple Int))) (and (set.all (lambda ((tuple_110 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_109) ((_ tuple.select 0) tuple_110)))) UserWantsToCook) true)) UserWantsToCook)
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
Formula A: (set.some (lambda ((tuple_113 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_111) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_113))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely)
Formula A: Bool
lhs: (set.some (lambda ((tuple_113 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_111) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_113))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely)
rhs: (not (or (= ((_ tuple.select 14) tuple_112) 2) ((_ tuple.select 12) tuple_112)))
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (or (set.some (lambda ((tuple_113 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_111) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_113))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely) (not (or (= ((_ tuple.select 14) tuple_112) 2) ((_ tuple.select 12) tuple_112))))
rhs: (= ((_ tuple.select 0) tuple_111) ((_ tuple.select 0) tuple_112))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_112 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (set.some (lambda ((tuple_113 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_111) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_113))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely) (not (or (= ((_ tuple.select 14) tuple_112) 2) ((_ tuple.select 12) tuple_112)))) (= ((_ tuple.select 0) tuple_111) ((_ tuple.select 0) tuple_112)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_111 (Tuple Int))) (set.some (lambda ((tuple_112 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (set.some (lambda ((tuple_113 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_111) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_113))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely) (not (or (= ((_ tuple.select 14) tuple_112) 2) ((_ tuple.select 12) tuple_112)))) (= ((_ tuple.select 0) tuple_111) ((_ tuple.select 0) tuple_112)))) Measure)) AllowUserToCook)
Formula A: Bool
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
Formula A: (set.some (lambda ((tuple_116 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_114) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_116))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_116 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_114) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_116))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely))
rhs: (or (= ((_ tuple.select 14) tuple_115) 2) ((_ tuple.select 12) tuple_115))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (set.some (lambda ((tuple_116 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_114) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_116))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely)) (or (= ((_ tuple.select 14) tuple_115) 2) ((_ tuple.select 12) tuple_115)))
rhs: (= ((_ tuple.select 0) tuple_114) ((_ tuple.select 0) tuple_115))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_115 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (set.some (lambda ((tuple_116 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_114) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_116))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely)) (or (= ((_ tuple.select 14) tuple_115) 2) ((_ tuple.select 12) tuple_115))) (= ((_ tuple.select 0) tuple_114) ((_ tuple.select 0) tuple_115)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_114 (Tuple Int))) (set.some (lambda ((tuple_115 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (set.some (lambda ((tuple_116 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_114) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_116))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely)) (or (= ((_ tuple.select 14) tuple_115) 2) ((_ tuple.select 12) tuple_115))) (= ((_ tuple.select 0) tuple_114) ((_ tuple.select 0) tuple_115)))) Measure)) AllowUserToCook)
Formula A: Bool
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
Formula B: (set.some (lambda ((tuple_117 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (= ((_ tuple.select 15) tuple_117) 2) ((_ tuple.select 13) tuple_117)) (= ((_ tuple.select 0) tuple_117) ((_ tuple.select 1) tuple_117)))) (rel.product AllowUserToCook Measure))
Formula B: Bool
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
Formula A: (set.some (lambda ((tuple_119 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (= ((_ tuple.select 14) tuple_119) 2) ((_ tuple.select 12) tuple_119)) (= ((_ tuple.select 0) tuple_119) ((_ tuple.select 0) tuple_118)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_118 (Tuple Int))) (set.some (lambda ((tuple_119 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (= ((_ tuple.select 14) tuple_119) 2) ((_ tuple.select 12) tuple_119)) (= ((_ tuple.select 0) tuple_119) ((_ tuple.select 0) tuple_118)))) Measure)) AllowUserToCook)
Formula A: Bool
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
Formula A: (set.some (lambda ((tuple_121 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (= ((_ tuple.select 14) tuple_121) 2) ((_ tuple.select 12) tuple_121)) (= ((_ tuple.select 0) tuple_121) ((_ tuple.select 0) tuple_120)))) Measure)
Formula A: Bool
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
Formula A: (set.some (lambda ((tuple_123 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (= ((_ tuple.select 14) tuple_123) 2) ((_ tuple.select 12) tuple_123)) (= ((_ tuple.select 0) tuple_123) ((_ tuple.select 0) tuple_122)))) Measure)
Formula A: Bool
lhs: (set.some (lambda ((tuple_123 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (= ((_ tuple.select 14) tuple_123) 2) ((_ tuple.select 12) tuple_123)) (= ((_ tuple.select 0) tuple_123) ((_ tuple.select 0) tuple_122)))) Measure)
rhs: (>= ((_ tuple.select 0) tuple_120) ((_ tuple.select 0) tuple_122))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_122 (Tuple Int))) (=> (set.some (lambda ((tuple_123 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (= ((_ tuple.select 14) tuple_123) 2) ((_ tuple.select 12) tuple_123)) (= ((_ tuple.select 0) tuple_123) ((_ tuple.select 0) tuple_122)))) Measure) (>= ((_ tuple.select 0) tuple_120) ((_ tuple.select 0) tuple_122)))) AllowUserToCook)
Formula A: Bool
lhs: (set.all (lambda ((tuple_122 (Tuple Int))) (=> (set.some (lambda ((tuple_123 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (= ((_ tuple.select 14) tuple_123) 2) ((_ tuple.select 12) tuple_123)) (= ((_ tuple.select 0) tuple_123) ((_ tuple.select 0) tuple_122)))) Measure) (>= ((_ tuple.select 0) tuple_120) ((_ tuple.select 0) tuple_122)))) AllowUserToCook)
rhs: (set.some (lambda ((tuple_121 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (= ((_ tuple.select 14) tuple_121) 2) ((_ tuple.select 12) tuple_121)) (= ((_ tuple.select 0) tuple_121) ((_ tuple.select 0) tuple_120)))) Measure)
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_120 (Tuple Int))) (and (set.all (lambda ((tuple_122 (Tuple Int))) (=> (set.some (lambda ((tuple_123 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (= ((_ tuple.select 14) tuple_123) 2) ((_ tuple.select 12) tuple_123)) (= ((_ tuple.select 0) tuple_123) ((_ tuple.select 0) tuple_122)))) Measure) (>= ((_ tuple.select 0) tuple_120) ((_ tuple.select 0) tuple_122)))) AllowUserToCook) (set.some (lambda ((tuple_121 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (= ((_ tuple.select 14) tuple_121) 2) ((_ tuple.select 12) tuple_121)) (= ((_ tuple.select 0) tuple_121) ((_ tuple.select 0) tuple_120)))) Measure))) AllowUserToCook)
Formula A: Bool
lhs: (set.some (lambda ((tuple_118 (Tuple Int))) (set.some (lambda ((tuple_119 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (= ((_ tuple.select 14) tuple_119) 2) ((_ tuple.select 12) tuple_119)) (= ((_ tuple.select 0) tuple_119) ((_ tuple.select 0) tuple_118)))) Measure)) AllowUserToCook)
rhs: (set.some (lambda ((tuple_120 (Tuple Int))) (and (set.all (lambda ((tuple_122 (Tuple Int))) (=> (set.some (lambda ((tuple_123 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (= ((_ tuple.select 14) tuple_123) 2) ((_ tuple.select 12) tuple_123)) (= ((_ tuple.select 0) tuple_123) ((_ tuple.select 0) tuple_122)))) Measure) (>= ((_ tuple.select 0) tuple_120) ((_ tuple.select 0) tuple_122)))) AllowUserToCook) (set.some (lambda ((tuple_121 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (= ((_ tuple.select 14) tuple_121) 2) ((_ tuple.select 12) tuple_121)) (= ((_ tuple.select 0) tuple_121) ((_ tuple.select 0) tuple_120)))) Measure))) AllowUserToCook)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_126) (+ ((_ tuple.select 0) tuple_124) 0))
rhs: (<= ((_ tuple.select 0) tuple_126) (+ ((_ tuple.select 0) tuple_124) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_126 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_124) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_126))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)
Formula A: Bool
lhs: (set.some (lambda ((tuple_126 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_124) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_126))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)
rhs: (= ((_ tuple.select 0) tuple_124) ((_ tuple.select 0) tuple_125))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_125 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_126 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_124) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_126))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser) (= ((_ tuple.select 0) tuple_124) ((_ tuple.select 0) tuple_125)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_124 (Tuple Int))) (set.some (lambda ((tuple_125 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_126 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_124) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_126))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser) (= ((_ tuple.select 0) tuple_124) ((_ tuple.select 0) tuple_125)))) Measure)) UserHasLimitation)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_129) (+ ((_ tuple.select 0) tuple_127) 0))
rhs: (<= ((_ tuple.select 0) tuple_129) (+ ((_ tuple.select 0) tuple_127) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_129 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_127) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_129))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_129 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_127) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_129))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser))
rhs: (= ((_ tuple.select 0) tuple_127) ((_ tuple.select 0) tuple_128))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_128 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_129 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_127) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_129))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)) (= ((_ tuple.select 0) tuple_127) ((_ tuple.select 0) tuple_128)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_127 (Tuple Int))) (set.some (lambda ((tuple_128 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_129 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_127) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_129))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)) (= ((_ tuple.select 0) tuple_127) ((_ tuple.select 0) tuple_128)))) Measure)) UserHasLimitation)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_130 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_130) ((_ tuple.select 1) tuple_130))) (rel.product UserHasLimitation Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_131 (Tuple Int))) true) UserHasLimitation)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_132) ((_ tuple.select 0) tuple_133))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_133 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_132) ((_ tuple.select 0) tuple_133)))) UserHasLimitation)
Formula A: Bool
lhs: (set.all (lambda ((tuple_133 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_132) ((_ tuple.select 0) tuple_133)))) UserHasLimitation)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_132 (Tuple Int))) (and (set.all (lambda ((tuple_133 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_132) ((_ tuple.select 0) tuple_133)))) UserHasLimitation) true)) UserHasLimitation)
Formula A: Bool
lhs: (set.some (lambda ((tuple_131 (Tuple Int))) true) UserHasLimitation)
rhs: (set.some (lambda ((tuple_132 (Tuple Int))) (and (set.all (lambda ((tuple_133 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_132) ((_ tuple.select 0) tuple_133)))) UserHasLimitation) true)) UserHasLimitation)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_136) (+ ((_ tuple.select 0) tuple_134) 0))
rhs: (<= ((_ tuple.select 0) tuple_136) (+ ((_ tuple.select 0) tuple_134) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_136 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_134) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_136))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CheckTemperature)
Formula A: Bool
lhs: (set.some (lambda ((tuple_136 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_134) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_136))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CheckTemperature)
rhs: (= ((_ tuple.select 0) tuple_134) ((_ tuple.select 0) tuple_135))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_135 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_136 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_134) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_136))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CheckTemperature) (= ((_ tuple.select 0) tuple_134) ((_ tuple.select 0) tuple_135)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_134 (Tuple Int))) (set.some (lambda ((tuple_135 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_136 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_134) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_136))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CheckTemperature) (= ((_ tuple.select 0) tuple_134) ((_ tuple.select 0) tuple_135)))) Measure)) UserWantsToCook)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_139) (+ ((_ tuple.select 0) tuple_137) 0))
rhs: (<= ((_ tuple.select 0) tuple_139) (+ ((_ tuple.select 0) tuple_137) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_139 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_137) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_139))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CheckTemperature)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_139 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_137) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_139))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CheckTemperature))
rhs: (= ((_ tuple.select 0) tuple_137) ((_ tuple.select 0) tuple_138))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_138 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_139 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_137) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_139))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CheckTemperature)) (= ((_ tuple.select 0) tuple_137) ((_ tuple.select 0) tuple_138)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_137 (Tuple Int))) (set.some (lambda ((tuple_138 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_139 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_137) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_139))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CheckTemperature)) (= ((_ tuple.select 0) tuple_137) ((_ tuple.select 0) tuple_138)))) Measure)) UserWantsToCook)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_140 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_140) ((_ tuple.select 1) tuple_140))) (rel.product UserWantsToCook Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_141 (Tuple Int))) true) UserWantsToCook)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_142) ((_ tuple.select 0) tuple_143))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_143 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_142) ((_ tuple.select 0) tuple_143)))) UserWantsToCook)
Formula A: Bool
lhs: (set.all (lambda ((tuple_143 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_142) ((_ tuple.select 0) tuple_143)))) UserWantsToCook)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_142 (Tuple Int))) (and (set.all (lambda ((tuple_143 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_142) ((_ tuple.select 0) tuple_143)))) UserWantsToCook) true)) UserWantsToCook)
Formula A: Bool
lhs: (set.some (lambda ((tuple_141 (Tuple Int))) true) UserWantsToCook)
rhs: (set.some (lambda ((tuple_142 (Tuple Int))) (and (set.all (lambda ((tuple_143 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_142) ((_ tuple.select 0) tuple_143)))) UserWantsToCook) true)) UserWantsToCook)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_146) (+ ((_ tuple.select 0) tuple_144) 0))
rhs: (<= ((_ tuple.select 0) tuple_146) (+ ((_ tuple.select 0) tuple_144) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_146 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_144) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_146))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)
Formula A: Bool
lhs: (set.some (lambda ((tuple_146 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_144) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_146))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)
rhs: (not ((_ tuple.select 12) tuple_145))
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (or (set.some (lambda ((tuple_146 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_144) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_146))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser) (not ((_ tuple.select 12) tuple_145)))
rhs: (= ((_ tuple.select 0) tuple_144) ((_ tuple.select 0) tuple_145))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_145 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (set.some (lambda ((tuple_146 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_144) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_146))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser) (not ((_ tuple.select 12) tuple_145))) (= ((_ tuple.select 0) tuple_144) ((_ tuple.select 0) tuple_145)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_144 (Tuple Int))) (set.some (lambda ((tuple_145 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (set.some (lambda ((tuple_146 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_144) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_146))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser) (not ((_ tuple.select 12) tuple_145))) (= ((_ tuple.select 0) tuple_144) ((_ tuple.select 0) tuple_145)))) Measure)) CheckTemperature)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_149) (+ ((_ tuple.select 0) tuple_147) 0))
rhs: (<= ((_ tuple.select 0) tuple_149) (+ ((_ tuple.select 0) tuple_147) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_149 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_147) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_149))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_149 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_147) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_149))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser))
rhs: ((_ tuple.select 12) tuple_148)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (set.some (lambda ((tuple_149 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_147) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_149))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)) ((_ tuple.select 12) tuple_148))
rhs: (= ((_ tuple.select 0) tuple_147) ((_ tuple.select 0) tuple_148))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_148 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (set.some (lambda ((tuple_149 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_147) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_149))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)) ((_ tuple.select 12) tuple_148)) (= ((_ tuple.select 0) tuple_147) ((_ tuple.select 0) tuple_148)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_147 (Tuple Int))) (set.some (lambda ((tuple_148 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (set.some (lambda ((tuple_149 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_147) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_149))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)) ((_ tuple.select 12) tuple_148)) (= ((_ tuple.select 0) tuple_147) ((_ tuple.select 0) tuple_148)))) Measure)) CheckTemperature)
Formula A: Bool
lhs: ((_ tuple.select 13) tuple_150)
rhs: (= ((_ tuple.select 0) tuple_150) ((_ tuple.select 1) tuple_150))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula B: (set.some (lambda ((tuple_150 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 13) tuple_150) (= ((_ tuple.select 0) tuple_150) ((_ tuple.select 1) tuple_150)))) (rel.product CheckTemperature Measure))
Formula B: Bool
lhs: ((_ tuple.select 12) tuple_152)
rhs: (= ((_ tuple.select 0) tuple_152) ((_ tuple.select 0) tuple_151))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_152 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 12) tuple_152) (= ((_ tuple.select 0) tuple_152) ((_ tuple.select 0) tuple_151)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_151 (Tuple Int))) (set.some (lambda ((tuple_152 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 12) tuple_152) (= ((_ tuple.select 0) tuple_152) ((_ tuple.select 0) tuple_151)))) Measure)) CheckTemperature)
Formula A: Bool
lhs: ((_ tuple.select 12) tuple_154)
rhs: (= ((_ tuple.select 0) tuple_154) ((_ tuple.select 0) tuple_153))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_154 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 12) tuple_154) (= ((_ tuple.select 0) tuple_154) ((_ tuple.select 0) tuple_153)))) Measure)
Formula A: Bool
lhs: ((_ tuple.select 12) tuple_156)
rhs: (= ((_ tuple.select 0) tuple_156) ((_ tuple.select 0) tuple_155))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_156 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 12) tuple_156) (= ((_ tuple.select 0) tuple_156) ((_ tuple.select 0) tuple_155)))) Measure)
Formula A: Bool
lhs: (set.some (lambda ((tuple_156 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 12) tuple_156) (= ((_ tuple.select 0) tuple_156) ((_ tuple.select 0) tuple_155)))) Measure)
rhs: (>= ((_ tuple.select 0) tuple_153) ((_ tuple.select 0) tuple_155))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_155 (Tuple Int))) (=> (set.some (lambda ((tuple_156 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 12) tuple_156) (= ((_ tuple.select 0) tuple_156) ((_ tuple.select 0) tuple_155)))) Measure) (>= ((_ tuple.select 0) tuple_153) ((_ tuple.select 0) tuple_155)))) CheckTemperature)
Formula A: Bool
lhs: (set.all (lambda ((tuple_155 (Tuple Int))) (=> (set.some (lambda ((tuple_156 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 12) tuple_156) (= ((_ tuple.select 0) tuple_156) ((_ tuple.select 0) tuple_155)))) Measure) (>= ((_ tuple.select 0) tuple_153) ((_ tuple.select 0) tuple_155)))) CheckTemperature)
rhs: (set.some (lambda ((tuple_154 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 12) tuple_154) (= ((_ tuple.select 0) tuple_154) ((_ tuple.select 0) tuple_153)))) Measure)
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_153 (Tuple Int))) (and (set.all (lambda ((tuple_155 (Tuple Int))) (=> (set.some (lambda ((tuple_156 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 12) tuple_156) (= ((_ tuple.select 0) tuple_156) ((_ tuple.select 0) tuple_155)))) Measure) (>= ((_ tuple.select 0) tuple_153) ((_ tuple.select 0) tuple_155)))) CheckTemperature) (set.some (lambda ((tuple_154 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 12) tuple_154) (= ((_ tuple.select 0) tuple_154) ((_ tuple.select 0) tuple_153)))) Measure))) CheckTemperature)
Formula A: Bool
lhs: (set.some (lambda ((tuple_151 (Tuple Int))) (set.some (lambda ((tuple_152 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 12) tuple_152) (= ((_ tuple.select 0) tuple_152) ((_ tuple.select 0) tuple_151)))) Measure)) CheckTemperature)
rhs: (set.some (lambda ((tuple_153 (Tuple Int))) (and (set.all (lambda ((tuple_155 (Tuple Int))) (=> (set.some (lambda ((tuple_156 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 12) tuple_156) (= ((_ tuple.select 0) tuple_156) ((_ tuple.select 0) tuple_155)))) Measure) (>= ((_ tuple.select 0) tuple_153) ((_ tuple.select 0) tuple_155)))) CheckTemperature) (set.some (lambda ((tuple_154 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 12) tuple_154) (= ((_ tuple.select 0) tuple_154) ((_ tuple.select 0) tuple_153)))) Measure))) CheckTemperature)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_159) (+ ((_ tuple.select 0) tuple_157) 0))
rhs: (<= ((_ tuple.select 0) tuple_159) (+ ((_ tuple.select 0) tuple_157) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_159 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_157) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_159))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) TrackTime)
Formula A: Bool
lhs: (set.some (lambda ((tuple_159 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_157) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_159))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) TrackTime)
rhs: (= ((_ tuple.select 0) tuple_157) ((_ tuple.select 0) tuple_158))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_158 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_159 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_157) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_159))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) TrackTime) (= ((_ tuple.select 0) tuple_157) ((_ tuple.select 0) tuple_158)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_157 (Tuple Int))) (set.some (lambda ((tuple_158 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_159 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_157) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_159))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) TrackTime) (= ((_ tuple.select 0) tuple_157) ((_ tuple.select 0) tuple_158)))) Measure)) FoodPreparation)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_162) (+ ((_ tuple.select 0) tuple_160) 0))
rhs: (<= ((_ tuple.select 0) tuple_162) (+ ((_ tuple.select 0) tuple_160) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_162 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_160) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_162))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) TrackTime)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_162 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_160) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_162))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) TrackTime))
rhs: (= ((_ tuple.select 0) tuple_160) ((_ tuple.select 0) tuple_161))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_161 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_162 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_160) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_162))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) TrackTime)) (= ((_ tuple.select 0) tuple_160) ((_ tuple.select 0) tuple_161)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_160 (Tuple Int))) (set.some (lambda ((tuple_161 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_162 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_160) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_162))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) TrackTime)) (= ((_ tuple.select 0) tuple_160) ((_ tuple.select 0) tuple_161)))) Measure)) FoodPreparation)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_163 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_163) ((_ tuple.select 1) tuple_163))) (rel.product FoodPreparation Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_164 (Tuple Int))) true) FoodPreparation)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_165) ((_ tuple.select 0) tuple_166))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_166 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_165) ((_ tuple.select 0) tuple_166)))) FoodPreparation)
Formula A: Bool
lhs: (set.all (lambda ((tuple_166 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_165) ((_ tuple.select 0) tuple_166)))) FoodPreparation)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_165 (Tuple Int))) (and (set.all (lambda ((tuple_166 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_165) ((_ tuple.select 0) tuple_166)))) FoodPreparation) true)) FoodPreparation)
Formula A: Bool
lhs: (set.some (lambda ((tuple_164 (Tuple Int))) true) FoodPreparation)
rhs: (set.some (lambda ((tuple_165 (Tuple Int))) (and (set.all (lambda ((tuple_166 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_165) ((_ tuple.select 0) tuple_166)))) FoodPreparation) true)) FoodPreparation)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_169) (+ ((_ tuple.select 0) tuple_167) 0))
rhs: (<= ((_ tuple.select 0) tuple_169) (+ ((_ tuple.select 0) tuple_167) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_169 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_167) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_169))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)
Formula A: Bool
lhs: (set.some (lambda ((tuple_169 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_167) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_169))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)
rhs: (= ((_ tuple.select 0) tuple_167) ((_ tuple.select 0) tuple_168))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_168 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_169 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_167) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_169))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser) (= ((_ tuple.select 0) tuple_167) ((_ tuple.select 0) tuple_168)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_167 (Tuple Int))) (set.some (lambda ((tuple_168 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_169 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_167) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_169))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser) (= ((_ tuple.select 0) tuple_167) ((_ tuple.select 0) tuple_168)))) Measure)) TrackTime)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_172) (+ ((_ tuple.select 0) tuple_170) 0))
rhs: (<= ((_ tuple.select 0) tuple_172) (+ ((_ tuple.select 0) tuple_170) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_172 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_170) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_172))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_172 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_170) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_172))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser))
rhs: (= ((_ tuple.select 0) tuple_170) ((_ tuple.select 0) tuple_171))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_171 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_172 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_170) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_172))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)) (= ((_ tuple.select 0) tuple_170) ((_ tuple.select 0) tuple_171)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_170 (Tuple Int))) (set.some (lambda ((tuple_171 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_172 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_170) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_172))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)) (= ((_ tuple.select 0) tuple_170) ((_ tuple.select 0) tuple_171)))) Measure)) TrackTime)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_173 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_173) ((_ tuple.select 1) tuple_173))) (rel.product TrackTime Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_174 (Tuple Int))) true) TrackTime)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_175) ((_ tuple.select 0) tuple_176))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_176 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_175) ((_ tuple.select 0) tuple_176)))) TrackTime)
Formula A: Bool
lhs: (set.all (lambda ((tuple_176 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_175) ((_ tuple.select 0) tuple_176)))) TrackTime)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_175 (Tuple Int))) (and (set.all (lambda ((tuple_176 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_175) ((_ tuple.select 0) tuple_176)))) TrackTime) true)) TrackTime)
Formula A: Bool
lhs: (set.some (lambda ((tuple_174 (Tuple Int))) true) TrackTime)
rhs: (set.some (lambda ((tuple_175 (Tuple Int))) (and (set.all (lambda ((tuple_176 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_175) ((_ tuple.select 0) tuple_176)))) TrackTime) true)) TrackTime)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_179) (+ ((_ tuple.select 0) tuple_177) 0))
rhs: (<= ((_ tuple.select 0) tuple_179) (+ ((_ tuple.select 0) tuple_177) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_179 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_177) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_179))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CollectandRecordInformation)
Formula A: Bool
lhs: (set.some (lambda ((tuple_179 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_177) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_179))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CollectandRecordInformation)
rhs: (= ((_ tuple.select 0) tuple_177) ((_ tuple.select 0) tuple_178))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_178 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_179 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_177) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_179))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CollectandRecordInformation) (= ((_ tuple.select 0) tuple_177) ((_ tuple.select 0) tuple_178)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_177 (Tuple Int))) (set.some (lambda ((tuple_178 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_179 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_177) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_179))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CollectandRecordInformation) (= ((_ tuple.select 0) tuple_177) ((_ tuple.select 0) tuple_178)))) Measure)) MeetingUser)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_182) (+ ((_ tuple.select 0) tuple_180) 0))
rhs: (<= ((_ tuple.select 0) tuple_182) (+ ((_ tuple.select 0) tuple_180) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_182 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_180) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_182))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CollectandRecordInformation)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_182 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_180) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_182))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CollectandRecordInformation))
rhs: (= ((_ tuple.select 0) tuple_180) ((_ tuple.select 0) tuple_181))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_181 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_182 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_180) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_182))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CollectandRecordInformation)) (= ((_ tuple.select 0) tuple_180) ((_ tuple.select 0) tuple_181)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_180 (Tuple Int))) (set.some (lambda ((tuple_181 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_182 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_180) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_182))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CollectandRecordInformation)) (= ((_ tuple.select 0) tuple_180) ((_ tuple.select 0) tuple_181)))) Measure)) MeetingUser)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_183 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_183) ((_ tuple.select 1) tuple_183))) (rel.product MeetingUser Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_184 (Tuple Int))) true) MeetingUser)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_185) ((_ tuple.select 0) tuple_186))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_186 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_185) ((_ tuple.select 0) tuple_186)))) MeetingUser)
Formula A: Bool
lhs: (set.all (lambda ((tuple_186 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_185) ((_ tuple.select 0) tuple_186)))) MeetingUser)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_185 (Tuple Int))) (and (set.all (lambda ((tuple_186 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_185) ((_ tuple.select 0) tuple_186)))) MeetingUser) true)) MeetingUser)
Formula A: Bool
lhs: (set.some (lambda ((tuple_184 (Tuple Int))) true) MeetingUser)
rhs: (set.some (lambda ((tuple_185 (Tuple Int))) (and (set.all (lambda ((tuple_186 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_185) ((_ tuple.select 0) tuple_186)))) MeetingUser) true)) MeetingUser)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_189) (+ ((_ tuple.select 0) tuple_187) 0))
rhs: (<= ((_ tuple.select 0) tuple_189) (+ ((_ tuple.select 0) tuple_187) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_189 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_187) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_189))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateInformation)
Formula A: Bool
lhs: (set.some (lambda ((tuple_189 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_187) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_189))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateInformation)
rhs: (= ((_ tuple.select 0) tuple_187) ((_ tuple.select 0) tuple_188))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_188 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_189 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_187) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_189))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateInformation) (= ((_ tuple.select 0) tuple_187) ((_ tuple.select 0) tuple_188)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_187 (Tuple Int))) (set.some (lambda ((tuple_188 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_189 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_187) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_189))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateInformation) (= ((_ tuple.select 0) tuple_187) ((_ tuple.select 0) tuple_188)))) Measure)) AgentDeployed)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_192) (+ ((_ tuple.select 0) tuple_190) 0))
rhs: (<= ((_ tuple.select 0) tuple_192) (+ ((_ tuple.select 0) tuple_190) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_192 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_190) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_192))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateInformation)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_192 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_190) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_192))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateInformation))
rhs: (= ((_ tuple.select 0) tuple_190) ((_ tuple.select 0) tuple_191))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_191 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_192 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_190) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_192))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateInformation)) (= ((_ tuple.select 0) tuple_190) ((_ tuple.select 0) tuple_191)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_190 (Tuple Int))) (set.some (lambda ((tuple_191 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_192 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_190) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_192))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateInformation)) (= ((_ tuple.select 0) tuple_190) ((_ tuple.select 0) tuple_191)))) Measure)) AgentDeployed)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_193 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_193) ((_ tuple.select 1) tuple_193))) (rel.product AgentDeployed Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_194 (Tuple Int))) true) AgentDeployed)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_195) ((_ tuple.select 0) tuple_196))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_196 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_195) ((_ tuple.select 0) tuple_196)))) AgentDeployed)
Formula A: Bool
lhs: (set.all (lambda ((tuple_196 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_195) ((_ tuple.select 0) tuple_196)))) AgentDeployed)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_195 (Tuple Int))) (and (set.all (lambda ((tuple_196 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_195) ((_ tuple.select 0) tuple_196)))) AgentDeployed) true)) AgentDeployed)
Formula A: Bool
lhs: (set.some (lambda ((tuple_194 (Tuple Int))) true) AgentDeployed)
rhs: (set.some (lambda ((tuple_195 (Tuple Int))) (and (set.all (lambda ((tuple_196 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_195) ((_ tuple.select 0) tuple_196)))) AgentDeployed) true)) AgentDeployed)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_199) (+ ((_ tuple.select 0) tuple_197) 0))
rhs: (<= ((_ tuple.select 0) tuple_199) (+ ((_ tuple.select 0) tuple_197) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_199 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_197) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_199))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ConsiderUserPractices)
Formula A: Bool
lhs: (set.some (lambda ((tuple_199 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_197) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_199))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ConsiderUserPractices)
rhs: (= ((_ tuple.select 0) tuple_197) ((_ tuple.select 0) tuple_198))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_198 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_199 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_197) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_199))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ConsiderUserPractices) (= ((_ tuple.select 0) tuple_197) ((_ tuple.select 0) tuple_198)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_197 (Tuple Int))) (set.some (lambda ((tuple_198 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_199 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_197) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_199))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ConsiderUserPractices) (= ((_ tuple.select 0) tuple_197) ((_ tuple.select 0) tuple_198)))) Measure)) GiveSuggestion)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_202) (+ ((_ tuple.select 0) tuple_200) 0))
rhs: (<= ((_ tuple.select 0) tuple_202) (+ ((_ tuple.select 0) tuple_200) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_202 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_200) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_202))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ConsiderUserPractices)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_202 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_200) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_202))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ConsiderUserPractices))
rhs: (= ((_ tuple.select 0) tuple_200) ((_ tuple.select 0) tuple_201))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_201 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_202 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_200) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_202))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ConsiderUserPractices)) (= ((_ tuple.select 0) tuple_200) ((_ tuple.select 0) tuple_201)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_200 (Tuple Int))) (set.some (lambda ((tuple_201 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_202 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_200) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_202))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ConsiderUserPractices)) (= ((_ tuple.select 0) tuple_200) ((_ tuple.select 0) tuple_201)))) Measure)) GiveSuggestion)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_203 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_203) ((_ tuple.select 1) tuple_203))) (rel.product GiveSuggestion Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_204 (Tuple Int))) true) GiveSuggestion)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_205) ((_ tuple.select 0) tuple_206))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_206 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_205) ((_ tuple.select 0) tuple_206)))) GiveSuggestion)
Formula A: Bool
lhs: (set.all (lambda ((tuple_206 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_205) ((_ tuple.select 0) tuple_206)))) GiveSuggestion)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_205 (Tuple Int))) (and (set.all (lambda ((tuple_206 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_205) ((_ tuple.select 0) tuple_206)))) GiveSuggestion) true)) GiveSuggestion)
Formula A: Bool
lhs: (set.some (lambda ((tuple_204 (Tuple Int))) true) GiveSuggestion)
rhs: (set.some (lambda ((tuple_205 (Tuple Int))) (and (set.all (lambda ((tuple_206 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_205) ((_ tuple.select 0) tuple_206)))) GiveSuggestion) true)) GiveSuggestion)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_209) (+ ((_ tuple.select 0) tuple_207) 0))
rhs: (<= ((_ tuple.select 0) tuple_209) (+ ((_ tuple.select 0) tuple_207) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_209 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_207) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_209))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskForEmergencyContact)
Formula A: Bool
lhs: (set.some (lambda ((tuple_209 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_207) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_209))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskForEmergencyContact)
rhs: (= ((_ tuple.select 0) tuple_207) ((_ tuple.select 0) tuple_208))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_208 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_209 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_207) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_209))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskForEmergencyContact) (= ((_ tuple.select 0) tuple_207) ((_ tuple.select 0) tuple_208)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_207 (Tuple Int))) (set.some (lambda ((tuple_208 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_209 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_207) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_209))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskForEmergencyContact) (= ((_ tuple.select 0) tuple_207) ((_ tuple.select 0) tuple_208)))) Measure)) MeetingUser)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_212) (+ ((_ tuple.select 0) tuple_210) 0))
rhs: (<= ((_ tuple.select 0) tuple_212) (+ ((_ tuple.select 0) tuple_210) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_212 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_210) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_212))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskForEmergencyContact)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_212 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_210) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_212))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskForEmergencyContact))
rhs: (= ((_ tuple.select 0) tuple_210) ((_ tuple.select 0) tuple_211))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_211 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_212 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_210) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_212))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskForEmergencyContact)) (= ((_ tuple.select 0) tuple_210) ((_ tuple.select 0) tuple_211)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_210 (Tuple Int))) (set.some (lambda ((tuple_211 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_212 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_210) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_212))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskForEmergencyContact)) (= ((_ tuple.select 0) tuple_210) ((_ tuple.select 0) tuple_211)))) Measure)) MeetingUser)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_213 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_213) ((_ tuple.select 1) tuple_213))) (rel.product MeetingUser Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_214 (Tuple Int))) true) MeetingUser)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_215) ((_ tuple.select 0) tuple_216))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_216 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_215) ((_ tuple.select 0) tuple_216)))) MeetingUser)
Formula A: Bool
lhs: (set.all (lambda ((tuple_216 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_215) ((_ tuple.select 0) tuple_216)))) MeetingUser)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_215 (Tuple Int))) (and (set.all (lambda ((tuple_216 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_215) ((_ tuple.select 0) tuple_216)))) MeetingUser) true)) MeetingUser)
Formula A: Bool
lhs: (set.some (lambda ((tuple_214 (Tuple Int))) true) MeetingUser)
rhs: (set.some (lambda ((tuple_215 (Tuple Int))) (and (set.all (lambda ((tuple_216 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_215) ((_ tuple.select 0) tuple_216)))) MeetingUser) true)) MeetingUser)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_219) (+ ((_ tuple.select 0) tuple_217) 0))
rhs: (<= ((_ tuple.select 0) tuple_219) (+ ((_ tuple.select 0) tuple_217) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_219 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_217) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_219))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)
Formula A: Bool
lhs: (set.some (lambda ((tuple_219 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_217) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_219))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)
rhs: (= ((_ tuple.select 0) tuple_217) ((_ tuple.select 0) tuple_218))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_218 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_219 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_217) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_219))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser) (= ((_ tuple.select 0) tuple_217) ((_ tuple.select 0) tuple_218)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_217 (Tuple Int))) (set.some (lambda ((tuple_218 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_219 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_217) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_219))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser) (= ((_ tuple.select 0) tuple_217) ((_ tuple.select 0) tuple_218)))) Measure)) AskForEmergencyContact)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_222) (+ ((_ tuple.select 0) tuple_220) 0))
rhs: (<= ((_ tuple.select 0) tuple_222) (+ ((_ tuple.select 0) tuple_220) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_222 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_220) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_222))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_222 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_220) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_222))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser))
rhs: (= ((_ tuple.select 0) tuple_220) ((_ tuple.select 0) tuple_221))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_221 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_222 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_220) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_222))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)) (= ((_ tuple.select 0) tuple_220) ((_ tuple.select 0) tuple_221)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_220 (Tuple Int))) (set.some (lambda ((tuple_221 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_222 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_220) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_222))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)) (= ((_ tuple.select 0) tuple_220) ((_ tuple.select 0) tuple_221)))) Measure)) AskForEmergencyContact)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_223 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_223) ((_ tuple.select 1) tuple_223))) (rel.product AskForEmergencyContact Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_224 (Tuple Int))) true) AskForEmergencyContact)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_225) ((_ tuple.select 0) tuple_226))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_226 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_225) ((_ tuple.select 0) tuple_226)))) AskForEmergencyContact)
Formula A: Bool
lhs: (set.all (lambda ((tuple_226 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_225) ((_ tuple.select 0) tuple_226)))) AskForEmergencyContact)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_225 (Tuple Int))) (and (set.all (lambda ((tuple_226 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_225) ((_ tuple.select 0) tuple_226)))) AskForEmergencyContact) true)) AskForEmergencyContact)
Formula A: Bool
lhs: (set.some (lambda ((tuple_224 (Tuple Int))) true) AskForEmergencyContact)
rhs: (set.some (lambda ((tuple_225 (Tuple Int))) (and (set.all (lambda ((tuple_226 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_225) ((_ tuple.select 0) tuple_226)))) AskForEmergencyContact) true)) AskForEmergencyContact)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_229) (+ ((_ tuple.select 0) tuple_227) 0))
rhs: (<= ((_ tuple.select 0) tuple_229) (+ ((_ tuple.select 0) tuple_227) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_229 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_227) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_229))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ShowDataHistory)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_229 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_227) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_229))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ShowDataHistory))
rhs: (not (not ((_ tuple.select 3) tuple_228)))
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (or (not (set.some (lambda ((tuple_229 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_227) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_229))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ShowDataHistory)) (not (not ((_ tuple.select 3) tuple_228))))
rhs: (= ((_ tuple.select 0) tuple_227) ((_ tuple.select 0) tuple_228))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_228 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (not (set.some (lambda ((tuple_229 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_227) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_229))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ShowDataHistory)) (not (not ((_ tuple.select 3) tuple_228)))) (= ((_ tuple.select 0) tuple_227) ((_ tuple.select 0) tuple_228)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_227 (Tuple Int))) (set.some (lambda ((tuple_228 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (not (set.some (lambda ((tuple_229 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_227) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_229))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ShowDataHistory)) (not (not ((_ tuple.select 3) tuple_228)))) (= ((_ tuple.select 0) tuple_227) ((_ tuple.select 0) tuple_228)))) Measure)) AgentDeployed)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_232) (+ ((_ tuple.select 0) tuple_230) 0))
rhs: (<= ((_ tuple.select 0) tuple_232) (+ ((_ tuple.select 0) tuple_230) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_232 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_230) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_232))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ShowDataHistory)
Formula A: Bool
lhs: (not (not (set.some (lambda ((tuple_232 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_230) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_232))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ShowDataHistory)))
rhs: (not ((_ tuple.select 3) tuple_231))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (not (set.some (lambda ((tuple_232 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_230) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_232))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ShowDataHistory))) (not ((_ tuple.select 3) tuple_231)))
rhs: (= ((_ tuple.select 0) tuple_230) ((_ tuple.select 0) tuple_231))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_231 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (not (set.some (lambda ((tuple_232 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_230) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_232))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ShowDataHistory))) (not ((_ tuple.select 3) tuple_231))) (= ((_ tuple.select 0) tuple_230) ((_ tuple.select 0) tuple_231)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_230 (Tuple Int))) (set.some (lambda ((tuple_231 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (not (set.some (lambda ((tuple_232 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_230) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_232))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ShowDataHistory))) (not ((_ tuple.select 3) tuple_231))) (= ((_ tuple.select 0) tuple_230) ((_ tuple.select 0) tuple_231)))) Measure)) AgentDeployed)
Formula A: Bool
lhs: (not ((_ tuple.select 4) tuple_233))
rhs: (= ((_ tuple.select 0) tuple_233) ((_ tuple.select 1) tuple_233))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula B: (set.some (lambda ((tuple_233 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 4) tuple_233)) (= ((_ tuple.select 0) tuple_233) ((_ tuple.select 1) tuple_233)))) (rel.product AgentDeployed Measure))
Formula B: Bool
lhs: (not ((_ tuple.select 3) tuple_235))
rhs: (= ((_ tuple.select 0) tuple_235) ((_ tuple.select 0) tuple_234))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_235 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 3) tuple_235)) (= ((_ tuple.select 0) tuple_235) ((_ tuple.select 0) tuple_234)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_234 (Tuple Int))) (set.some (lambda ((tuple_235 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 3) tuple_235)) (= ((_ tuple.select 0) tuple_235) ((_ tuple.select 0) tuple_234)))) Measure)) AgentDeployed)
Formula A: Bool
lhs: (not ((_ tuple.select 3) tuple_237))
rhs: (= ((_ tuple.select 0) tuple_237) ((_ tuple.select 0) tuple_236))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_237 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 3) tuple_237)) (= ((_ tuple.select 0) tuple_237) ((_ tuple.select 0) tuple_236)))) Measure)
Formula A: Bool
lhs: (not ((_ tuple.select 3) tuple_239))
rhs: (= ((_ tuple.select 0) tuple_239) ((_ tuple.select 0) tuple_238))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_239 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 3) tuple_239)) (= ((_ tuple.select 0) tuple_239) ((_ tuple.select 0) tuple_238)))) Measure)
Formula A: Bool
lhs: (set.some (lambda ((tuple_239 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 3) tuple_239)) (= ((_ tuple.select 0) tuple_239) ((_ tuple.select 0) tuple_238)))) Measure)
rhs: (>= ((_ tuple.select 0) tuple_236) ((_ tuple.select 0) tuple_238))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_238 (Tuple Int))) (=> (set.some (lambda ((tuple_239 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 3) tuple_239)) (= ((_ tuple.select 0) tuple_239) ((_ tuple.select 0) tuple_238)))) Measure) (>= ((_ tuple.select 0) tuple_236) ((_ tuple.select 0) tuple_238)))) AgentDeployed)
Formula A: Bool
lhs: (set.all (lambda ((tuple_238 (Tuple Int))) (=> (set.some (lambda ((tuple_239 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 3) tuple_239)) (= ((_ tuple.select 0) tuple_239) ((_ tuple.select 0) tuple_238)))) Measure) (>= ((_ tuple.select 0) tuple_236) ((_ tuple.select 0) tuple_238)))) AgentDeployed)
rhs: (set.some (lambda ((tuple_237 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 3) tuple_237)) (= ((_ tuple.select 0) tuple_237) ((_ tuple.select 0) tuple_236)))) Measure)
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_236 (Tuple Int))) (and (set.all (lambda ((tuple_238 (Tuple Int))) (=> (set.some (lambda ((tuple_239 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 3) tuple_239)) (= ((_ tuple.select 0) tuple_239) ((_ tuple.select 0) tuple_238)))) Measure) (>= ((_ tuple.select 0) tuple_236) ((_ tuple.select 0) tuple_238)))) AgentDeployed) (set.some (lambda ((tuple_237 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 3) tuple_237)) (= ((_ tuple.select 0) tuple_237) ((_ tuple.select 0) tuple_236)))) Measure))) AgentDeployed)
Formula A: Bool
lhs: (set.some (lambda ((tuple_234 (Tuple Int))) (set.some (lambda ((tuple_235 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 3) tuple_235)) (= ((_ tuple.select 0) tuple_235) ((_ tuple.select 0) tuple_234)))) Measure)) AgentDeployed)
rhs: (set.some (lambda ((tuple_236 (Tuple Int))) (and (set.all (lambda ((tuple_238 (Tuple Int))) (=> (set.some (lambda ((tuple_239 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 3) tuple_239)) (= ((_ tuple.select 0) tuple_239) ((_ tuple.select 0) tuple_238)))) Measure) (>= ((_ tuple.select 0) tuple_236) ((_ tuple.select 0) tuple_238)))) AgentDeployed) (set.some (lambda ((tuple_237 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 3) tuple_237)) (= ((_ tuple.select 0) tuple_237) ((_ tuple.select 0) tuple_236)))) Measure))) AgentDeployed)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_242) (+ ((_ tuple.select 0) tuple_240) 0))
rhs: (<= ((_ tuple.select 0) tuple_242) (+ ((_ tuple.select 0) tuple_240) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_242 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_240) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_242))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ProvideDataSummaries)
Formula A: Bool
lhs: (set.some (lambda ((tuple_242 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_240) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_242))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ProvideDataSummaries)
rhs: (not ((_ tuple.select 4) tuple_241))
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (or (set.some (lambda ((tuple_242 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_240) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_242))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ProvideDataSummaries) (not ((_ tuple.select 4) tuple_241)))
rhs: (= ((_ tuple.select 0) tuple_240) ((_ tuple.select 0) tuple_241))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_241 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (set.some (lambda ((tuple_242 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_240) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_242))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ProvideDataSummaries) (not ((_ tuple.select 4) tuple_241))) (= ((_ tuple.select 0) tuple_240) ((_ tuple.select 0) tuple_241)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_240 (Tuple Int))) (set.some (lambda ((tuple_241 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (or (set.some (lambda ((tuple_242 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_240) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_242))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ProvideDataSummaries) (not ((_ tuple.select 4) tuple_241))) (= ((_ tuple.select 0) tuple_240) ((_ tuple.select 0) tuple_241)))) Measure)) ShowDataHistory)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_245) (+ ((_ tuple.select 0) tuple_243) 0))
rhs: (<= ((_ tuple.select 0) tuple_245) (+ ((_ tuple.select 0) tuple_243) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_245 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_243) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_245))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ProvideDataSummaries)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_245 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_243) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_245))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ProvideDataSummaries))
rhs: ((_ tuple.select 4) tuple_244)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (set.some (lambda ((tuple_245 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_243) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_245))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ProvideDataSummaries)) ((_ tuple.select 4) tuple_244))
rhs: (= ((_ tuple.select 0) tuple_243) ((_ tuple.select 0) tuple_244))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_244 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (set.some (lambda ((tuple_245 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_243) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_245))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ProvideDataSummaries)) ((_ tuple.select 4) tuple_244)) (= ((_ tuple.select 0) tuple_243) ((_ tuple.select 0) tuple_244)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_243 (Tuple Int))) (set.some (lambda ((tuple_244 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (set.some (lambda ((tuple_245 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_243) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_245))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ProvideDataSummaries)) ((_ tuple.select 4) tuple_244)) (= ((_ tuple.select 0) tuple_243) ((_ tuple.select 0) tuple_244)))) Measure)) ShowDataHistory)
Formula A: Bool
lhs: ((_ tuple.select 5) tuple_246)
rhs: (= ((_ tuple.select 0) tuple_246) ((_ tuple.select 1) tuple_246))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula B: (set.some (lambda ((tuple_246 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 5) tuple_246) (= ((_ tuple.select 0) tuple_246) ((_ tuple.select 1) tuple_246)))) (rel.product ShowDataHistory Measure))
Formula B: Bool
lhs: ((_ tuple.select 4) tuple_248)
rhs: (= ((_ tuple.select 0) tuple_248) ((_ tuple.select 0) tuple_247))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_248 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 4) tuple_248) (= ((_ tuple.select 0) tuple_248) ((_ tuple.select 0) tuple_247)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_247 (Tuple Int))) (set.some (lambda ((tuple_248 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 4) tuple_248) (= ((_ tuple.select 0) tuple_248) ((_ tuple.select 0) tuple_247)))) Measure)) ShowDataHistory)
Formula A: Bool
lhs: ((_ tuple.select 4) tuple_250)
rhs: (= ((_ tuple.select 0) tuple_250) ((_ tuple.select 0) tuple_249))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_250 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 4) tuple_250) (= ((_ tuple.select 0) tuple_250) ((_ tuple.select 0) tuple_249)))) Measure)
Formula A: Bool
lhs: ((_ tuple.select 4) tuple_252)
rhs: (= ((_ tuple.select 0) tuple_252) ((_ tuple.select 0) tuple_251))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_252 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 4) tuple_252) (= ((_ tuple.select 0) tuple_252) ((_ tuple.select 0) tuple_251)))) Measure)
Formula A: Bool
lhs: (set.some (lambda ((tuple_252 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 4) tuple_252) (= ((_ tuple.select 0) tuple_252) ((_ tuple.select 0) tuple_251)))) Measure)
rhs: (>= ((_ tuple.select 0) tuple_249) ((_ tuple.select 0) tuple_251))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_251 (Tuple Int))) (=> (set.some (lambda ((tuple_252 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 4) tuple_252) (= ((_ tuple.select 0) tuple_252) ((_ tuple.select 0) tuple_251)))) Measure) (>= ((_ tuple.select 0) tuple_249) ((_ tuple.select 0) tuple_251)))) ShowDataHistory)
Formula A: Bool
lhs: (set.all (lambda ((tuple_251 (Tuple Int))) (=> (set.some (lambda ((tuple_252 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 4) tuple_252) (= ((_ tuple.select 0) tuple_252) ((_ tuple.select 0) tuple_251)))) Measure) (>= ((_ tuple.select 0) tuple_249) ((_ tuple.select 0) tuple_251)))) ShowDataHistory)
rhs: (set.some (lambda ((tuple_250 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 4) tuple_250) (= ((_ tuple.select 0) tuple_250) ((_ tuple.select 0) tuple_249)))) Measure)
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_249 (Tuple Int))) (and (set.all (lambda ((tuple_251 (Tuple Int))) (=> (set.some (lambda ((tuple_252 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 4) tuple_252) (= ((_ tuple.select 0) tuple_252) ((_ tuple.select 0) tuple_251)))) Measure) (>= ((_ tuple.select 0) tuple_249) ((_ tuple.select 0) tuple_251)))) ShowDataHistory) (set.some (lambda ((tuple_250 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 4) tuple_250) (= ((_ tuple.select 0) tuple_250) ((_ tuple.select 0) tuple_249)))) Measure))) ShowDataHistory)
Formula A: Bool
lhs: (set.some (lambda ((tuple_247 (Tuple Int))) (set.some (lambda ((tuple_248 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 4) tuple_248) (= ((_ tuple.select 0) tuple_248) ((_ tuple.select 0) tuple_247)))) Measure)) ShowDataHistory)
rhs: (set.some (lambda ((tuple_249 (Tuple Int))) (and (set.all (lambda ((tuple_251 (Tuple Int))) (=> (set.some (lambda ((tuple_252 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 4) tuple_252) (= ((_ tuple.select 0) tuple_252) ((_ tuple.select 0) tuple_251)))) Measure) (>= ((_ tuple.select 0) tuple_249) ((_ tuple.select 0) tuple_251)))) ShowDataHistory) (set.some (lambda ((tuple_250 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and ((_ tuple.select 4) tuple_250) (= ((_ tuple.select 0) tuple_250) ((_ tuple.select 0) tuple_249)))) Measure))) ShowDataHistory)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_255) (+ ((_ tuple.select 0) tuple_253) 0))
rhs: (<= ((_ tuple.select 0) tuple_255) (+ ((_ tuple.select 0) tuple_253) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_255 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_253) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_255))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) GiveUserDangerousObjects)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_255 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_253) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_255))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) GiveUserDangerousObjects))
rhs: (= ((_ tuple.select 0) tuple_253) ((_ tuple.select 0) tuple_254))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_254 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_255 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_253) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_255))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) GiveUserDangerousObjects)) (= ((_ tuple.select 0) tuple_253) ((_ tuple.select 0) tuple_254)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_253 (Tuple Int))) (set.some (lambda ((tuple_254 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_255 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_253) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_255))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) GiveUserDangerousObjects)) (= ((_ tuple.select 0) tuple_253) ((_ tuple.select 0) tuple_254)))) Measure)) UserUnpredictable)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_258) (+ ((_ tuple.select 0) tuple_256) 0))
rhs: (<= ((_ tuple.select 0) tuple_258) (+ ((_ tuple.select 0) tuple_256) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_258 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_256) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_258))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) GiveUserDangerousObjects)
Formula A: Bool
lhs: (not (not (set.some (lambda ((tuple_258 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_256) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_258))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) GiveUserDangerousObjects)))
rhs: (= ((_ tuple.select 0) tuple_256) ((_ tuple.select 0) tuple_257))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_257 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (not (set.some (lambda ((tuple_258 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_256) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_258))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) GiveUserDangerousObjects))) (= ((_ tuple.select 0) tuple_256) ((_ tuple.select 0) tuple_257)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_256 (Tuple Int))) (set.some (lambda ((tuple_257 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (not (set.some (lambda ((tuple_258 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_256) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_258))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) GiveUserDangerousObjects))) (= ((_ tuple.select 0) tuple_256) ((_ tuple.select 0) tuple_257)))) Measure)) UserUnpredictable)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_259 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_259) ((_ tuple.select 1) tuple_259))) (rel.product UserUnpredictable Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_260 (Tuple Int))) true) UserUnpredictable)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_261) ((_ tuple.select 0) tuple_262))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_262 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_261) ((_ tuple.select 0) tuple_262)))) UserUnpredictable)
Formula A: Bool
lhs: (set.all (lambda ((tuple_262 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_261) ((_ tuple.select 0) tuple_262)))) UserUnpredictable)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_261 (Tuple Int))) (and (set.all (lambda ((tuple_262 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_261) ((_ tuple.select 0) tuple_262)))) UserUnpredictable) true)) UserUnpredictable)
Formula A: Bool
lhs: (set.some (lambda ((tuple_260 (Tuple Int))) true) UserUnpredictable)
rhs: (set.some (lambda ((tuple_261 (Tuple Int))) (and (set.all (lambda ((tuple_262 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_261) ((_ tuple.select 0) tuple_262)))) UserUnpredictable) true)) UserUnpredictable)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_265) (+ ((_ tuple.select 0) tuple_263) 0))
rhs: (<= ((_ tuple.select 0) tuple_265) (+ ((_ tuple.select 0) tuple_263) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_265 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_263) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_265))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindUserOfLimitations)
Formula A: Bool
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
rhs: (set.some (lambda ((tuple_265 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_263) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_265))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindUserOfLimitations)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not (> ((_ tuple.select 9) tuple_264) 1)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not (> ((_ tuple.select 9) tuple_264) 1)) true)) (set.some (lambda ((tuple_265 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_263) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_265))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindUserOfLimitations))
rhs: (=> (and (> ((_ tuple.select 9) tuple_264) 1) true) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 (> ((_ tuple.select 9) tuple_264) 1))) (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_265 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_263) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_265))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindUserOfLimitations)) (=> (and _let_1 true) true)))
rhs: (not (not ((_ tuple.select 5) tuple_264)))
lhs: Bool
rhs: Bool
compare: Kind.OR
lhs: (let ((_let_1 (> ((_ tuple.select 9) tuple_264) 1))) (or (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_265 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_263) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_265))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindUserOfLimitations)) (=> (and _let_1 true) true)) (not (not ((_ tuple.select 5) tuple_264)))))
rhs: (= ((_ tuple.select 0) tuple_263) ((_ tuple.select 0) tuple_264))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_264 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 (> ((_ tuple.select 9) tuple_264) 1))) (and (or (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_265 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_263) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_265))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindUserOfLimitations)) (=> (and _let_1 true) true)) (not (not ((_ tuple.select 5) tuple_264)))) (= ((_ tuple.select 0) tuple_263) ((_ tuple.select 0) tuple_264))))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_263 (Tuple Int))) (set.some (lambda ((tuple_264 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 (> ((_ tuple.select 9) tuple_264) 1))) (and (or (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_265 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_263) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_265))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindUserOfLimitations)) (=> (and _let_1 true) true)) (not (not ((_ tuple.select 5) tuple_264)))) (= ((_ tuple.select 0) tuple_263) ((_ tuple.select 0) tuple_264))))) Measure)) AgentDeployed)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_268) (+ ((_ tuple.select 0) tuple_266) 0))
rhs: (<= ((_ tuple.select 0) tuple_268) (+ ((_ tuple.select 0) tuple_266) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_268 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_266) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_268))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindUserOfLimitations)
Formula A: Bool
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
rhs: (set.some (lambda ((tuple_268 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_266) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_268))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindUserOfLimitations)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not (> ((_ tuple.select 9) tuple_267) 1)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not (> ((_ tuple.select 9) tuple_267) 1)) true)) (set.some (lambda ((tuple_268 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_266) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_268))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindUserOfLimitations))
rhs: (=> (and (> ((_ tuple.select 9) tuple_267) 1) true) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 (> ((_ tuple.select 9) tuple_267) 1))) (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_268 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_266) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_268))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindUserOfLimitations)) (=> (and _let_1 true) true))))
rhs: (not ((_ tuple.select 5) tuple_267))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 (> ((_ tuple.select 9) tuple_267) 1))) (and (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_268 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_266) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_268))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindUserOfLimitations)) (=> (and _let_1 true) true))) (not ((_ tuple.select 5) tuple_267))))
rhs: (= ((_ tuple.select 0) tuple_266) ((_ tuple.select 0) tuple_267))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_267 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 (> ((_ tuple.select 9) tuple_267) 1))) (and (and (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_268 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_266) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_268))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindUserOfLimitations)) (=> (and _let_1 true) true))) (not ((_ tuple.select 5) tuple_267))) (= ((_ tuple.select 0) tuple_266) ((_ tuple.select 0) tuple_267))))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_266 (Tuple Int))) (set.some (lambda ((tuple_267 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 (> ((_ tuple.select 9) tuple_267) 1))) (and (and (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_268 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_266) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_268))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RemindUserOfLimitations)) (=> (and _let_1 true) true))) (not ((_ tuple.select 5) tuple_267))) (= ((_ tuple.select 0) tuple_266) ((_ tuple.select 0) tuple_267))))) Measure)) AgentDeployed)
Formula A: Bool
lhs: (not ((_ tuple.select 6) tuple_269))
rhs: (= ((_ tuple.select 0) tuple_269) ((_ tuple.select 1) tuple_269))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula B: (set.some (lambda ((tuple_269 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 6) tuple_269)) (= ((_ tuple.select 0) tuple_269) ((_ tuple.select 1) tuple_269)))) (rel.product AgentDeployed Measure))
Formula B: Bool
lhs: (not ((_ tuple.select 5) tuple_271))
rhs: (= ((_ tuple.select 0) tuple_271) ((_ tuple.select 0) tuple_270))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_271 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 5) tuple_271)) (= ((_ tuple.select 0) tuple_271) ((_ tuple.select 0) tuple_270)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_270 (Tuple Int))) (set.some (lambda ((tuple_271 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 5) tuple_271)) (= ((_ tuple.select 0) tuple_271) ((_ tuple.select 0) tuple_270)))) Measure)) AgentDeployed)
Formula A: Bool
lhs: (not ((_ tuple.select 5) tuple_273))
rhs: (= ((_ tuple.select 0) tuple_273) ((_ tuple.select 0) tuple_272))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_273 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 5) tuple_273)) (= ((_ tuple.select 0) tuple_273) ((_ tuple.select 0) tuple_272)))) Measure)
Formula A: Bool
lhs: (not ((_ tuple.select 5) tuple_275))
rhs: (= ((_ tuple.select 0) tuple_275) ((_ tuple.select 0) tuple_274))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_275 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 5) tuple_275)) (= ((_ tuple.select 0) tuple_275) ((_ tuple.select 0) tuple_274)))) Measure)
Formula A: Bool
lhs: (set.some (lambda ((tuple_275 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 5) tuple_275)) (= ((_ tuple.select 0) tuple_275) ((_ tuple.select 0) tuple_274)))) Measure)
rhs: (>= ((_ tuple.select 0) tuple_272) ((_ tuple.select 0) tuple_274))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_274 (Tuple Int))) (=> (set.some (lambda ((tuple_275 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 5) tuple_275)) (= ((_ tuple.select 0) tuple_275) ((_ tuple.select 0) tuple_274)))) Measure) (>= ((_ tuple.select 0) tuple_272) ((_ tuple.select 0) tuple_274)))) AgentDeployed)
Formula A: Bool
lhs: (set.all (lambda ((tuple_274 (Tuple Int))) (=> (set.some (lambda ((tuple_275 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 5) tuple_275)) (= ((_ tuple.select 0) tuple_275) ((_ tuple.select 0) tuple_274)))) Measure) (>= ((_ tuple.select 0) tuple_272) ((_ tuple.select 0) tuple_274)))) AgentDeployed)
rhs: (set.some (lambda ((tuple_273 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 5) tuple_273)) (= ((_ tuple.select 0) tuple_273) ((_ tuple.select 0) tuple_272)))) Measure)
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_272 (Tuple Int))) (and (set.all (lambda ((tuple_274 (Tuple Int))) (=> (set.some (lambda ((tuple_275 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 5) tuple_275)) (= ((_ tuple.select 0) tuple_275) ((_ tuple.select 0) tuple_274)))) Measure) (>= ((_ tuple.select 0) tuple_272) ((_ tuple.select 0) tuple_274)))) AgentDeployed) (set.some (lambda ((tuple_273 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 5) tuple_273)) (= ((_ tuple.select 0) tuple_273) ((_ tuple.select 0) tuple_272)))) Measure))) AgentDeployed)
Formula A: Bool
lhs: (set.some (lambda ((tuple_270 (Tuple Int))) (set.some (lambda ((tuple_271 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 5) tuple_271)) (= ((_ tuple.select 0) tuple_271) ((_ tuple.select 0) tuple_270)))) Measure)) AgentDeployed)
rhs: (set.some (lambda ((tuple_272 (Tuple Int))) (and (set.all (lambda ((tuple_274 (Tuple Int))) (=> (set.some (lambda ((tuple_275 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 5) tuple_275)) (= ((_ tuple.select 0) tuple_275) ((_ tuple.select 0) tuple_274)))) Measure) (>= ((_ tuple.select 0) tuple_272) ((_ tuple.select 0) tuple_274)))) AgentDeployed) (set.some (lambda ((tuple_273 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not ((_ tuple.select 5) tuple_273)) (= ((_ tuple.select 0) tuple_273) ((_ tuple.select 0) tuple_272)))) Measure))) AgentDeployed)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_278) (+ ((_ tuple.select 0) tuple_276) 0))
rhs: (<= ((_ tuple.select 0) tuple_278) (+ ((_ tuple.select 0) tuple_276) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_278 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_276) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_278))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AgentHasAppropriateAppearance)
Formula A: Bool
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
rhs: (set.some (lambda ((tuple_278 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_276) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_278))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AgentHasAppropriateAppearance)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not ((_ tuple.select 6) tuple_277)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not ((_ tuple.select 6) tuple_277)) true)) (set.some (lambda ((tuple_278 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_276) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_278))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AgentHasAppropriateAppearance))
rhs: (=> (and ((_ tuple.select 6) tuple_277) true) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 ((_ tuple.select 6) tuple_277))) (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_278 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_276) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_278))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AgentHasAppropriateAppearance)) (=> (and _let_1 true) true)))
rhs: (= ((_ tuple.select 0) tuple_276) ((_ tuple.select 0) tuple_277))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_277 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 ((_ tuple.select 6) tuple_277))) (and (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_278 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_276) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_278))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AgentHasAppropriateAppearance)) (=> (and _let_1 true) true)) (= ((_ tuple.select 0) tuple_276) ((_ tuple.select 0) tuple_277))))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_276 (Tuple Int))) (set.some (lambda ((tuple_277 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 ((_ tuple.select 6) tuple_277))) (and (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_278 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_276) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_278))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AgentHasAppropriateAppearance)) (=> (and _let_1 true) true)) (= ((_ tuple.select 0) tuple_276) ((_ tuple.select 0) tuple_277))))) Measure)) PreparingDeployment)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_281) (+ ((_ tuple.select 0) tuple_279) 0))
rhs: (<= ((_ tuple.select 0) tuple_281) (+ ((_ tuple.select 0) tuple_279) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_281 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_279) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_281))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AgentHasAppropriateAppearance)
Formula A: Bool
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
rhs: (set.some (lambda ((tuple_281 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_279) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_281))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AgentHasAppropriateAppearance)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not ((_ tuple.select 6) tuple_280)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not ((_ tuple.select 6) tuple_280)) true)) (set.some (lambda ((tuple_281 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_279) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_281))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AgentHasAppropriateAppearance))
rhs: (=> (and ((_ tuple.select 6) tuple_280) true) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 ((_ tuple.select 6) tuple_280))) (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_281 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_279) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_281))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AgentHasAppropriateAppearance)) (=> (and _let_1 true) true))))
rhs: (= ((_ tuple.select 0) tuple_279) ((_ tuple.select 0) tuple_280))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_280 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 ((_ tuple.select 6) tuple_280))) (and (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_281 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_279) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_281))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AgentHasAppropriateAppearance)) (=> (and _let_1 true) true))) (= ((_ tuple.select 0) tuple_279) ((_ tuple.select 0) tuple_280))))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_279 (Tuple Int))) (set.some (lambda ((tuple_280 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 ((_ tuple.select 6) tuple_280))) (and (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_281 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_279) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_281))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AgentHasAppropriateAppearance)) (=> (and _let_1 true) true))) (= ((_ tuple.select 0) tuple_279) ((_ tuple.select 0) tuple_280))))) Measure)) PreparingDeployment)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_282 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_282) ((_ tuple.select 1) tuple_282))) (rel.product PreparingDeployment Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_283 (Tuple Int))) true) PreparingDeployment)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_284) ((_ tuple.select 0) tuple_285))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_285 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_284) ((_ tuple.select 0) tuple_285)))) PreparingDeployment)
Formula A: Bool
lhs: (set.all (lambda ((tuple_285 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_284) ((_ tuple.select 0) tuple_285)))) PreparingDeployment)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_284 (Tuple Int))) (and (set.all (lambda ((tuple_285 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_284) ((_ tuple.select 0) tuple_285)))) PreparingDeployment) true)) PreparingDeployment)
Formula A: Bool
lhs: (set.some (lambda ((tuple_283 (Tuple Int))) true) PreparingDeployment)
rhs: (set.some (lambda ((tuple_284 (Tuple Int))) (and (set.all (lambda ((tuple_285 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_284) ((_ tuple.select 0) tuple_285)))) PreparingDeployment) true)) PreparingDeployment)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_288) (+ ((_ tuple.select 0) tuple_286) 0))
rhs: (<= ((_ tuple.select 0) tuple_288) (+ ((_ tuple.select 0) tuple_286) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_288 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_286) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_288))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CalibrateSpeech)
Formula A: Bool
lhs: (set.some (lambda ((tuple_288 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_286) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_288))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CalibrateSpeech)
rhs: (= ((_ tuple.select 0) tuple_286) ((_ tuple.select 0) tuple_287))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_287 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_288 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_286) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_288))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CalibrateSpeech) (= ((_ tuple.select 0) tuple_286) ((_ tuple.select 0) tuple_287)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_286 (Tuple Int))) (set.some (lambda ((tuple_287 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_288 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_286) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_288))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CalibrateSpeech) (= ((_ tuple.select 0) tuple_286) ((_ tuple.select 0) tuple_287)))) Measure)) PreparingDeployment)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_291) (+ ((_ tuple.select 0) tuple_289) 0))
rhs: (<= ((_ tuple.select 0) tuple_291) (+ ((_ tuple.select 0) tuple_289) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_291 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_289) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_291))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CalibrateSpeech)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_291 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_289) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_291))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CalibrateSpeech))
rhs: (= ((_ tuple.select 0) tuple_289) ((_ tuple.select 0) tuple_290))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_290 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_291 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_289) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_291))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CalibrateSpeech)) (= ((_ tuple.select 0) tuple_289) ((_ tuple.select 0) tuple_290)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_289 (Tuple Int))) (set.some (lambda ((tuple_290 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_291 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_289) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_291))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CalibrateSpeech)) (= ((_ tuple.select 0) tuple_289) ((_ tuple.select 0) tuple_290)))) Measure)) PreparingDeployment)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_292 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_292) ((_ tuple.select 1) tuple_292))) (rel.product PreparingDeployment Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_293 (Tuple Int))) true) PreparingDeployment)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_294) ((_ tuple.select 0) tuple_295))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_295 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_294) ((_ tuple.select 0) tuple_295)))) PreparingDeployment)
Formula A: Bool
lhs: (set.all (lambda ((tuple_295 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_294) ((_ tuple.select 0) tuple_295)))) PreparingDeployment)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_294 (Tuple Int))) (and (set.all (lambda ((tuple_295 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_294) ((_ tuple.select 0) tuple_295)))) PreparingDeployment) true)) PreparingDeployment)
Formula A: Bool
lhs: (set.some (lambda ((tuple_293 (Tuple Int))) true) PreparingDeployment)
rhs: (set.some (lambda ((tuple_294 (Tuple Int))) (and (set.all (lambda ((tuple_295 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_294) ((_ tuple.select 0) tuple_295)))) PreparingDeployment) true)) PreparingDeployment)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_298) (+ ((_ tuple.select 0) tuple_296) 0))
rhs: (<= ((_ tuple.select 0) tuple_298) (+ ((_ tuple.select 0) tuple_296) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_298 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_296) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_298))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UseFirstPersonPluralLanguage)
Formula A: Bool
lhs: (set.some (lambda ((tuple_298 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_296) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_298))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UseFirstPersonPluralLanguage)
rhs: (= ((_ tuple.select 0) tuple_296) ((_ tuple.select 0) tuple_297))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_297 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_298 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_296) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_298))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UseFirstPersonPluralLanguage) (= ((_ tuple.select 0) tuple_296) ((_ tuple.select 0) tuple_297)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_296 (Tuple Int))) (set.some (lambda ((tuple_297 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_298 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_296) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_298))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UseFirstPersonPluralLanguage) (= ((_ tuple.select 0) tuple_296) ((_ tuple.select 0) tuple_297)))) Measure)) GivingCookingInstructions)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_301) (+ ((_ tuple.select 0) tuple_299) 0))
rhs: (<= ((_ tuple.select 0) tuple_301) (+ ((_ tuple.select 0) tuple_299) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_301 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_299) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_301))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UseFirstPersonPluralLanguage)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_301 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_299) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_301))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UseFirstPersonPluralLanguage))
rhs: (= ((_ tuple.select 0) tuple_299) ((_ tuple.select 0) tuple_300))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_300 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_301 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_299) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_301))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UseFirstPersonPluralLanguage)) (= ((_ tuple.select 0) tuple_299) ((_ tuple.select 0) tuple_300)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_299 (Tuple Int))) (set.some (lambda ((tuple_300 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_301 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_299) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_301))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UseFirstPersonPluralLanguage)) (= ((_ tuple.select 0) tuple_299) ((_ tuple.select 0) tuple_300)))) Measure)) GivingCookingInstructions)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_302 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_302) ((_ tuple.select 1) tuple_302))) (rel.product GivingCookingInstructions Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_303 (Tuple Int))) true) GivingCookingInstructions)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_304) ((_ tuple.select 0) tuple_305))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_305 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_304) ((_ tuple.select 0) tuple_305)))) GivingCookingInstructions)
Formula A: Bool
lhs: (set.all (lambda ((tuple_305 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_304) ((_ tuple.select 0) tuple_305)))) GivingCookingInstructions)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_304 (Tuple Int))) (and (set.all (lambda ((tuple_305 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_304) ((_ tuple.select 0) tuple_305)))) GivingCookingInstructions) true)) GivingCookingInstructions)
Formula A: Bool
lhs: (set.some (lambda ((tuple_303 (Tuple Int))) true) GivingCookingInstructions)
rhs: (set.some (lambda ((tuple_304 (Tuple Int))) (and (set.all (lambda ((tuple_305 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_304) ((_ tuple.select 0) tuple_305)))) GivingCookingInstructions) true)) GivingCookingInstructions)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_308) (+ ((_ tuple.select 0) tuple_306) 0))
rhs: (<= ((_ tuple.select 0) tuple_308) (+ ((_ tuple.select 0) tuple_306) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_308 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_306) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_308))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)
Formula A: Bool
lhs: (set.some (lambda ((tuple_308 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_306) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_308))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)
rhs: (= ((_ tuple.select 0) tuple_306) ((_ tuple.select 0) tuple_307))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_307 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_308 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_306) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_308))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser) (= ((_ tuple.select 0) tuple_306) ((_ tuple.select 0) tuple_307)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_306 (Tuple Int))) (set.some (lambda ((tuple_307 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_308 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_306) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_308))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser) (= ((_ tuple.select 0) tuple_306) ((_ tuple.select 0) tuple_307)))) Measure)) GivingCookingInstructions)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_311) (+ ((_ tuple.select 0) tuple_309) 0))
rhs: (<= ((_ tuple.select 0) tuple_311) (+ ((_ tuple.select 0) tuple_309) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_311 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_309) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_311))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_311 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_309) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_311))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser))
rhs: (= ((_ tuple.select 0) tuple_309) ((_ tuple.select 0) tuple_310))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_310 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_311 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_309) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_311))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)) (= ((_ tuple.select 0) tuple_309) ((_ tuple.select 0) tuple_310)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_309 (Tuple Int))) (set.some (lambda ((tuple_310 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_311 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_309) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_311))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)) (= ((_ tuple.select 0) tuple_309) ((_ tuple.select 0) tuple_310)))) Measure)) GivingCookingInstructions)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_312 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_312) ((_ tuple.select 1) tuple_312))) (rel.product GivingCookingInstructions Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_313 (Tuple Int))) true) GivingCookingInstructions)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_314) ((_ tuple.select 0) tuple_315))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_315 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_314) ((_ tuple.select 0) tuple_315)))) GivingCookingInstructions)
Formula A: Bool
lhs: (set.all (lambda ((tuple_315 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_314) ((_ tuple.select 0) tuple_315)))) GivingCookingInstructions)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_314 (Tuple Int))) (and (set.all (lambda ((tuple_315 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_314) ((_ tuple.select 0) tuple_315)))) GivingCookingInstructions) true)) GivingCookingInstructions)
Formula A: Bool
lhs: (set.some (lambda ((tuple_313 (Tuple Int))) true) GivingCookingInstructions)
rhs: (set.some (lambda ((tuple_314 (Tuple Int))) (and (set.all (lambda ((tuple_315 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_314) ((_ tuple.select 0) tuple_315)))) GivingCookingInstructions) true)) GivingCookingInstructions)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_318) (+ ((_ tuple.select 0) tuple_316) 0))
rhs: (<= ((_ tuple.select 0) tuple_318) (+ ((_ tuple.select 0) tuple_316) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_318 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_316) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_318))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskForDetailLevelOfInstructions)
Formula A: Bool
lhs: (set.some (lambda ((tuple_318 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_316) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_318))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskForDetailLevelOfInstructions)
rhs: (= ((_ tuple.select 0) tuple_316) ((_ tuple.select 0) tuple_317))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_317 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_318 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_316) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_318))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskForDetailLevelOfInstructions) (= ((_ tuple.select 0) tuple_316) ((_ tuple.select 0) tuple_317)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_316 (Tuple Int))) (set.some (lambda ((tuple_317 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_318 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_316) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_318))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskForDetailLevelOfInstructions) (= ((_ tuple.select 0) tuple_316) ((_ tuple.select 0) tuple_317)))) Measure)) BeforeCookingBegins)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_321) (+ ((_ tuple.select 0) tuple_319) 0))
rhs: (<= ((_ tuple.select 0) tuple_321) (+ ((_ tuple.select 0) tuple_319) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_321 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_319) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_321))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskForDetailLevelOfInstructions)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_321 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_319) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_321))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskForDetailLevelOfInstructions))
rhs: (= ((_ tuple.select 0) tuple_319) ((_ tuple.select 0) tuple_320))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_320 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_321 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_319) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_321))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskForDetailLevelOfInstructions)) (= ((_ tuple.select 0) tuple_319) ((_ tuple.select 0) tuple_320)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_319 (Tuple Int))) (set.some (lambda ((tuple_320 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_321 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_319) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_321))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskForDetailLevelOfInstructions)) (= ((_ tuple.select 0) tuple_319) ((_ tuple.select 0) tuple_320)))) Measure)) BeforeCookingBegins)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_322 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_322) ((_ tuple.select 1) tuple_322))) (rel.product BeforeCookingBegins Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_323 (Tuple Int))) true) BeforeCookingBegins)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_324) ((_ tuple.select 0) tuple_325))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_325 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_324) ((_ tuple.select 0) tuple_325)))) BeforeCookingBegins)
Formula A: Bool
lhs: (set.all (lambda ((tuple_325 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_324) ((_ tuple.select 0) tuple_325)))) BeforeCookingBegins)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_324 (Tuple Int))) (and (set.all (lambda ((tuple_325 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_324) ((_ tuple.select 0) tuple_325)))) BeforeCookingBegins) true)) BeforeCookingBegins)
Formula A: Bool
lhs: (set.some (lambda ((tuple_323 (Tuple Int))) true) BeforeCookingBegins)
rhs: (set.some (lambda ((tuple_324 (Tuple Int))) (and (set.all (lambda ((tuple_325 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_324) ((_ tuple.select 0) tuple_325)))) BeforeCookingBegins) true)) BeforeCookingBegins)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_328) (+ ((_ tuple.select 0) tuple_326) 0))
rhs: (<= ((_ tuple.select 0) tuple_328) (+ ((_ tuple.select 0) tuple_326) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_328 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_326) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_328))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RecalculateApproach)
Formula A: Bool
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
rhs: (set.some (lambda ((tuple_328 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_326) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_328))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RecalculateApproach)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not (= ((_ tuple.select 14) tuple_327) 2)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not (= ((_ tuple.select 14) tuple_327) 2)) true)) (set.some (lambda ((tuple_328 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_326) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_328))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RecalculateApproach))
rhs: (=> (and (= ((_ tuple.select 14) tuple_327) 2) true) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 (= ((_ tuple.select 14) tuple_327) 2))) (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_328 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_326) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_328))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RecalculateApproach)) (=> (and _let_1 true) true)))
rhs: (= ((_ tuple.select 0) tuple_326) ((_ tuple.select 0) tuple_327))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_327 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 (= ((_ tuple.select 14) tuple_327) 2))) (and (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_328 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_326) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_328))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RecalculateApproach)) (=> (and _let_1 true) true)) (= ((_ tuple.select 0) tuple_326) ((_ tuple.select 0) tuple_327))))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_326 (Tuple Int))) (set.some (lambda ((tuple_327 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 (= ((_ tuple.select 14) tuple_327) 2))) (and (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_328 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_326) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_328))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RecalculateApproach)) (=> (and _let_1 true) true)) (= ((_ tuple.select 0) tuple_326) ((_ tuple.select 0) tuple_327))))) Measure)) UserChangeMind)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_331) (+ ((_ tuple.select 0) tuple_329) 0))
rhs: (<= ((_ tuple.select 0) tuple_331) (+ ((_ tuple.select 0) tuple_329) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_331 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_329) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_331))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RecalculateApproach)
Formula A: Bool
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
rhs: (set.some (lambda ((tuple_331 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_329) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_331))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RecalculateApproach)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not (= ((_ tuple.select 14) tuple_330) 2)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not (= ((_ tuple.select 14) tuple_330) 2)) true)) (set.some (lambda ((tuple_331 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_329) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_331))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RecalculateApproach))
rhs: (=> (and (= ((_ tuple.select 14) tuple_330) 2) true) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 (= ((_ tuple.select 14) tuple_330) 2))) (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_331 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_329) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_331))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RecalculateApproach)) (=> (and _let_1 true) true))))
rhs: (= ((_ tuple.select 0) tuple_329) ((_ tuple.select 0) tuple_330))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_330 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 (= ((_ tuple.select 14) tuple_330) 2))) (and (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_331 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_329) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_331))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RecalculateApproach)) (=> (and _let_1 true) true))) (= ((_ tuple.select 0) tuple_329) ((_ tuple.select 0) tuple_330))))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_329 (Tuple Int))) (set.some (lambda ((tuple_330 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 (= ((_ tuple.select 14) tuple_330) 2))) (and (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_331 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_329) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_331))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RecalculateApproach)) (=> (and _let_1 true) true))) (= ((_ tuple.select 0) tuple_329) ((_ tuple.select 0) tuple_330))))) Measure)) UserChangeMind)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_332 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_332) ((_ tuple.select 1) tuple_332))) (rel.product UserChangeMind Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_333 (Tuple Int))) true) UserChangeMind)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_334) ((_ tuple.select 0) tuple_335))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_335 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_334) ((_ tuple.select 0) tuple_335)))) UserChangeMind)
Formula A: Bool
lhs: (set.all (lambda ((tuple_335 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_334) ((_ tuple.select 0) tuple_335)))) UserChangeMind)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_334 (Tuple Int))) (and (set.all (lambda ((tuple_335 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_334) ((_ tuple.select 0) tuple_335)))) UserChangeMind) true)) UserChangeMind)
Formula A: Bool
lhs: (set.some (lambda ((tuple_333 (Tuple Int))) true) UserChangeMind)
rhs: (set.some (lambda ((tuple_334 (Tuple Int))) (and (set.all (lambda ((tuple_335 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_334) ((_ tuple.select 0) tuple_335)))) UserChangeMind) true)) UserChangeMind)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_338) (+ ((_ tuple.select 0) tuple_336) 0))
rhs: (<= ((_ tuple.select 0) tuple_338) (+ ((_ tuple.select 0) tuple_336) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_338 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_336) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_338))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateMap)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_339) (+ ((_ tuple.select 0) tuple_336) 0))
rhs: (<= ((_ tuple.select 0) tuple_339) (+ ((_ tuple.select 0) tuple_336) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_339 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_336) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_339))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely)
Formula A: Bool
lhs: (= ((_ tuple.select 14) tuple_337) 2)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (= ((_ tuple.select 14) tuple_337) 2) true)
rhs: (set.some (lambda ((tuple_339 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_336) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_339))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely)
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
rhs: (set.some (lambda ((tuple_338 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_336) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_338))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateMap)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not (= ((_ tuple.select 14) tuple_337) 2)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not (= ((_ tuple.select 14) tuple_337) 2)) true)) (set.some (lambda ((tuple_338 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_336) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_338))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateMap))
rhs: (=> (and (= ((_ tuple.select 14) tuple_337) 2) true) (set.some (lambda ((tuple_339 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_336) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_339))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 (= ((_ tuple.select 14) tuple_337) 2))) (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_338 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_336) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_338))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateMap)) (=> (and _let_1 true) (set.some (lambda ((tuple_339 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_336) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_339))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely))))
rhs: (= ((_ tuple.select 0) tuple_336) ((_ tuple.select 0) tuple_337))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_337 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 (= ((_ tuple.select 14) tuple_337) 2))) (and (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_338 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_336) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_338))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateMap)) (=> (and _let_1 true) (set.some (lambda ((tuple_339 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_336) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_339))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely))) (= ((_ tuple.select 0) tuple_336) ((_ tuple.select 0) tuple_337))))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_336 (Tuple Int))) (set.some (lambda ((tuple_337 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 (= ((_ tuple.select 14) tuple_337) 2))) (and (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_338 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_336) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_338))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateMap)) (=> (and _let_1 true) (set.some (lambda ((tuple_339 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_336) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_339))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely))) (= ((_ tuple.select 0) tuple_336) ((_ tuple.select 0) tuple_337))))) Measure)) UserChangeItemLocation)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_342) (+ ((_ tuple.select 0) tuple_340) 0))
rhs: (<= ((_ tuple.select 0) tuple_342) (+ ((_ tuple.select 0) tuple_340) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_342 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_340) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_342))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateMap)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_343) (+ ((_ tuple.select 0) tuple_340) 0))
rhs: (<= ((_ tuple.select 0) tuple_343) (+ ((_ tuple.select 0) tuple_340) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_343 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_340) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_343))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely)
Formula A: Bool
lhs: (= ((_ tuple.select 14) tuple_341) 2)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (= ((_ tuple.select 14) tuple_341) 2) true)
rhs: (set.some (lambda ((tuple_343 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_340) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_343))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely)
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
rhs: (set.some (lambda ((tuple_342 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_340) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_342))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateMap)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not (= ((_ tuple.select 14) tuple_341) 2)) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not (= ((_ tuple.select 14) tuple_341) 2)) true)) (set.some (lambda ((tuple_342 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_340) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_342))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateMap))
rhs: (=> (and (= ((_ tuple.select 14) tuple_341) 2) true) (set.some (lambda ((tuple_343 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_340) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_343))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 (= ((_ tuple.select 14) tuple_341) 2))) (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_342 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_340) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_342))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateMap)) (=> (and _let_1 true) (set.some (lambda ((tuple_343 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_340) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_343))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely)))))
rhs: (= ((_ tuple.select 0) tuple_340) ((_ tuple.select 0) tuple_341))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_341 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 (= ((_ tuple.select 14) tuple_341) 2))) (and (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_342 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_340) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_342))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateMap)) (=> (and _let_1 true) (set.some (lambda ((tuple_343 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_340) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_343))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely)))) (= ((_ tuple.select 0) tuple_340) ((_ tuple.select 0) tuple_341))))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_340 (Tuple Int))) (set.some (lambda ((tuple_341 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 (= ((_ tuple.select 14) tuple_341) 2))) (and (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_342 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_340) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_342))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UpdateMap)) (=> (and _let_1 true) (set.some (lambda ((tuple_343 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_340) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_343))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely)))) (= ((_ tuple.select 0) tuple_340) ((_ tuple.select 0) tuple_341))))) Measure)) UserChangeItemLocation)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_344 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_344) ((_ tuple.select 1) tuple_344))) (rel.product UserChangeItemLocation Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_345 (Tuple Int))) true) UserChangeItemLocation)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_346) ((_ tuple.select 0) tuple_347))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_347 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_346) ((_ tuple.select 0) tuple_347)))) UserChangeItemLocation)
Formula A: Bool
lhs: (set.all (lambda ((tuple_347 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_346) ((_ tuple.select 0) tuple_347)))) UserChangeItemLocation)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_346 (Tuple Int))) (and (set.all (lambda ((tuple_347 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_346) ((_ tuple.select 0) tuple_347)))) UserChangeItemLocation) true)) UserChangeItemLocation)
Formula A: Bool
lhs: (set.some (lambda ((tuple_345 (Tuple Int))) true) UserChangeItemLocation)
rhs: (set.some (lambda ((tuple_346 (Tuple Int))) (and (set.all (lambda ((tuple_347 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_346) ((_ tuple.select 0) tuple_347)))) UserChangeItemLocation) true)) UserChangeItemLocation)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_350) (+ ((_ tuple.select 0) tuple_348) 0))
rhs: (<= ((_ tuple.select 0) tuple_350) (+ ((_ tuple.select 0) tuple_348) 300))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_350 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_348))) (let ((_let_2 ((_ tuple.select 0) tuple_350))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 300)))))) CallEmergencyServices)
Formula A: Bool
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
Formula A: (set.some (lambda ((tuple_351 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_348) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_351))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures)
Formula A: Bool
lhs: (and (not ((_ tuple.select 8) tuple_349)) ((_ tuple.select 7) tuple_349))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (and (not ((_ tuple.select 8) tuple_349)) ((_ tuple.select 7) tuple_349)) true)
rhs: (set.some (lambda ((tuple_351 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_348) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_351))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures)
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
rhs: (set.some (lambda ((tuple_350 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_348))) (let ((_let_2 ((_ tuple.select 0) tuple_350))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 300)))))) CallEmergencyServices)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not (and (not ((_ tuple.select 8) tuple_349)) ((_ tuple.select 7) tuple_349))) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not (and (not ((_ tuple.select 8) tuple_349)) ((_ tuple.select 7) tuple_349))) true)) (set.some (lambda ((tuple_350 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_348))) (let ((_let_2 ((_ tuple.select 0) tuple_350))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 300)))))) CallEmergencyServices))
rhs: (=> (and (and (not ((_ tuple.select 8) tuple_349)) ((_ tuple.select 7) tuple_349)) true) (set.some (lambda ((tuple_351 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_348) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_351))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 (and (not ((_ tuple.select 8) tuple_349)) ((_ tuple.select 7) tuple_349)))) (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_350 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_348))) (let ((_let_2 ((_ tuple.select 0) tuple_350))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 300)))))) CallEmergencyServices)) (=> (and _let_1 true) (set.some (lambda ((tuple_351 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_348) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_351))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures))))
rhs: (= ((_ tuple.select 0) tuple_348) ((_ tuple.select 0) tuple_349))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_349 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 (and (not ((_ tuple.select 8) tuple_349)) ((_ tuple.select 7) tuple_349)))) (and (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_350 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_348))) (let ((_let_2 ((_ tuple.select 0) tuple_350))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 300)))))) CallEmergencyServices)) (=> (and _let_1 true) (set.some (lambda ((tuple_351 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_348) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_351))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures))) (= ((_ tuple.select 0) tuple_348) ((_ tuple.select 0) tuple_349))))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_348 (Tuple Int))) (set.some (lambda ((tuple_349 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 (and (not ((_ tuple.select 8) tuple_349)) ((_ tuple.select 7) tuple_349)))) (and (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_350 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_348))) (let ((_let_2 ((_ tuple.select 0) tuple_350))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 300)))))) CallEmergencyServices)) (=> (and _let_1 true) (set.some (lambda ((tuple_351 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_348) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_351))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures))) (= ((_ tuple.select 0) tuple_348) ((_ tuple.select 0) tuple_349))))) Measure)) SmokeDetectorAlarm)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_354) (+ ((_ tuple.select 0) tuple_352) 0))
rhs: (<= ((_ tuple.select 0) tuple_354) (+ ((_ tuple.select 0) tuple_352) 300))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_354 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_352))) (let ((_let_2 ((_ tuple.select 0) tuple_354))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 300)))))) CallEmergencyServices)
Formula A: Bool
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
Formula A: (set.some (lambda ((tuple_355 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_352) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_355))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures)
Formula A: Bool
lhs: (and (not ((_ tuple.select 8) tuple_353)) ((_ tuple.select 7) tuple_353))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (and (not ((_ tuple.select 8) tuple_353)) ((_ tuple.select 7) tuple_353)) true)
rhs: (set.some (lambda ((tuple_355 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_352) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_355))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures)
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
rhs: (set.some (lambda ((tuple_354 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_352))) (let ((_let_2 ((_ tuple.select 0) tuple_354))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 300)))))) CallEmergencyServices)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not (and (not ((_ tuple.select 8) tuple_353)) ((_ tuple.select 7) tuple_353))) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not (and (not ((_ tuple.select 8) tuple_353)) ((_ tuple.select 7) tuple_353))) true)) (set.some (lambda ((tuple_354 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_352))) (let ((_let_2 ((_ tuple.select 0) tuple_354))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 300)))))) CallEmergencyServices))
rhs: (=> (and (and (not ((_ tuple.select 8) tuple_353)) ((_ tuple.select 7) tuple_353)) true) (set.some (lambda ((tuple_355 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_352) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_355))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 (and (not ((_ tuple.select 8) tuple_353)) ((_ tuple.select 7) tuple_353)))) (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_354 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_352))) (let ((_let_2 ((_ tuple.select 0) tuple_354))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 300)))))) CallEmergencyServices)) (=> (and _let_1 true) (set.some (lambda ((tuple_355 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_352) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_355))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures)))))
rhs: (= ((_ tuple.select 0) tuple_352) ((_ tuple.select 0) tuple_353))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_353 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 (and (not ((_ tuple.select 8) tuple_353)) ((_ tuple.select 7) tuple_353)))) (and (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_354 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_352))) (let ((_let_2 ((_ tuple.select 0) tuple_354))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 300)))))) CallEmergencyServices)) (=> (and _let_1 true) (set.some (lambda ((tuple_355 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_352) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_355))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures)))) (= ((_ tuple.select 0) tuple_352) ((_ tuple.select 0) tuple_353))))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_352 (Tuple Int))) (set.some (lambda ((tuple_353 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 (and (not ((_ tuple.select 8) tuple_353)) ((_ tuple.select 7) tuple_353)))) (and (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_354 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_352))) (let ((_let_2 ((_ tuple.select 0) tuple_354))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 300)))))) CallEmergencyServices)) (=> (and _let_1 true) (set.some (lambda ((tuple_355 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_352) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_355))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures)))) (= ((_ tuple.select 0) tuple_352) ((_ tuple.select 0) tuple_353))))) Measure)) SmokeDetectorAlarm)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_356 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_356) ((_ tuple.select 1) tuple_356))) (rel.product SmokeDetectorAlarm Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_357 (Tuple Int))) true) SmokeDetectorAlarm)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_358) ((_ tuple.select 0) tuple_359))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_359 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_358) ((_ tuple.select 0) tuple_359)))) SmokeDetectorAlarm)
Formula A: Bool
lhs: (set.all (lambda ((tuple_359 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_358) ((_ tuple.select 0) tuple_359)))) SmokeDetectorAlarm)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_358 (Tuple Int))) (and (set.all (lambda ((tuple_359 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_358) ((_ tuple.select 0) tuple_359)))) SmokeDetectorAlarm) true)) SmokeDetectorAlarm)
Formula A: Bool
lhs: (set.some (lambda ((tuple_357 (Tuple Int))) true) SmokeDetectorAlarm)
rhs: (set.some (lambda ((tuple_358 (Tuple Int))) (and (set.all (lambda ((tuple_359 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_358) ((_ tuple.select 0) tuple_359)))) SmokeDetectorAlarm) true)) SmokeDetectorAlarm)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_362) (+ ((_ tuple.select 0) tuple_360) 0))
rhs: (<= ((_ tuple.select 0) tuple_362) (+ ((_ tuple.select 0) tuple_360) 120))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_362 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_360))) (let ((_let_2 ((_ tuple.select 0) tuple_362))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 120)))))) CallEmergencyServices)
Formula A: Bool
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
Formula A: (set.some (lambda ((tuple_363 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_360) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_363))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures)
Formula A: Bool
lhs: (and (not ((_ tuple.select 8) tuple_361)) ((_ tuple.select 7) tuple_361))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (and (not ((_ tuple.select 8) tuple_361)) ((_ tuple.select 7) tuple_361)) true)
rhs: (set.some (lambda ((tuple_363 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_360) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_363))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures)
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
rhs: (set.some (lambda ((tuple_362 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_360))) (let ((_let_2 ((_ tuple.select 0) tuple_362))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 120)))))) CallEmergencyServices)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not (and (not ((_ tuple.select 8) tuple_361)) ((_ tuple.select 7) tuple_361))) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not (and (not ((_ tuple.select 8) tuple_361)) ((_ tuple.select 7) tuple_361))) true)) (set.some (lambda ((tuple_362 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_360))) (let ((_let_2 ((_ tuple.select 0) tuple_362))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 120)))))) CallEmergencyServices))
rhs: (=> (and (and (not ((_ tuple.select 8) tuple_361)) ((_ tuple.select 7) tuple_361)) true) (set.some (lambda ((tuple_363 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_360) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_363))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 (and (not ((_ tuple.select 8) tuple_361)) ((_ tuple.select 7) tuple_361)))) (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_362 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_360))) (let ((_let_2 ((_ tuple.select 0) tuple_362))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 120)))))) CallEmergencyServices)) (=> (and _let_1 true) (set.some (lambda ((tuple_363 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_360) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_363))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures))))
rhs: (= ((_ tuple.select 0) tuple_360) ((_ tuple.select 0) tuple_361))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_361 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 (and (not ((_ tuple.select 8) tuple_361)) ((_ tuple.select 7) tuple_361)))) (and (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_362 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_360))) (let ((_let_2 ((_ tuple.select 0) tuple_362))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 120)))))) CallEmergencyServices)) (=> (and _let_1 true) (set.some (lambda ((tuple_363 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_360) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_363))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures))) (= ((_ tuple.select 0) tuple_360) ((_ tuple.select 0) tuple_361))))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_360 (Tuple Int))) (set.some (lambda ((tuple_361 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 (and (not ((_ tuple.select 8) tuple_361)) ((_ tuple.select 7) tuple_361)))) (and (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_362 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_360))) (let ((_let_2 ((_ tuple.select 0) tuple_362))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 120)))))) CallEmergencyServices)) (=> (and _let_1 true) (set.some (lambda ((tuple_363 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_360) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_363))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures))) (= ((_ tuple.select 0) tuple_360) ((_ tuple.select 0) tuple_361))))) Measure)) SmokeDetectorAlarm)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_366) (+ ((_ tuple.select 0) tuple_364) 0))
rhs: (<= ((_ tuple.select 0) tuple_366) (+ ((_ tuple.select 0) tuple_364) 120))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_366 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_364))) (let ((_let_2 ((_ tuple.select 0) tuple_366))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 120)))))) CallEmergencyServices)
Formula A: Bool
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
Formula A: (set.some (lambda ((tuple_367 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_364) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_367))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures)
Formula A: Bool
lhs: (and (not ((_ tuple.select 8) tuple_365)) ((_ tuple.select 7) tuple_365))
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (and (not ((_ tuple.select 8) tuple_365)) ((_ tuple.select 7) tuple_365)) true)
rhs: (set.some (lambda ((tuple_367 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_364) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_367))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures)
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
rhs: (set.some (lambda ((tuple_366 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_364))) (let ((_let_2 ((_ tuple.select 0) tuple_366))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 120)))))) CallEmergencyServices)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (not true)
rhs: (and (not (and (not ((_ tuple.select 8) tuple_365)) ((_ tuple.select 7) tuple_365))) true)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (=> (and true (and (not (and (not ((_ tuple.select 8) tuple_365)) ((_ tuple.select 7) tuple_365))) true)) (set.some (lambda ((tuple_366 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_364))) (let ((_let_2 ((_ tuple.select 0) tuple_366))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 120)))))) CallEmergencyServices))
rhs: (=> (and (and (not ((_ tuple.select 8) tuple_365)) ((_ tuple.select 7) tuple_365)) true) (set.some (lambda ((tuple_367 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_364) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_367))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (let ((_let_1 (and (not ((_ tuple.select 8) tuple_365)) ((_ tuple.select 7) tuple_365)))) (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_366 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_364))) (let ((_let_2 ((_ tuple.select 0) tuple_366))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 120)))))) CallEmergencyServices)) (=> (and _let_1 true) (set.some (lambda ((tuple_367 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_364) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_367))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures)))))
rhs: (= ((_ tuple.select 0) tuple_364) ((_ tuple.select 0) tuple_365))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_365 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 (and (not ((_ tuple.select 8) tuple_365)) ((_ tuple.select 7) tuple_365)))) (and (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_366 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_364))) (let ((_let_2 ((_ tuple.select 0) tuple_366))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 120)))))) CallEmergencyServices)) (=> (and _let_1 true) (set.some (lambda ((tuple_367 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_364) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_367))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures)))) (= ((_ tuple.select 0) tuple_364) ((_ tuple.select 0) tuple_365))))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_364 (Tuple Int))) (set.some (lambda ((tuple_365 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 (and (not ((_ tuple.select 8) tuple_365)) ((_ tuple.select 7) tuple_365)))) (and (not (and (=> (and true (and (not _let_1) true)) (set.some (lambda ((tuple_366 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_364))) (let ((_let_2 ((_ tuple.select 0) tuple_366))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 120)))))) CallEmergencyServices)) (=> (and _let_1 true) (set.some (lambda ((tuple_367 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_364) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_367))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) FireSafetyMeasures)))) (= ((_ tuple.select 0) tuple_364) ((_ tuple.select 0) tuple_365))))) Measure)) SmokeDetectorAlarm)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_368 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_368) ((_ tuple.select 1) tuple_368))) (rel.product SmokeDetectorAlarm Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_369 (Tuple Int))) true) SmokeDetectorAlarm)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_370) ((_ tuple.select 0) tuple_371))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_371 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_370) ((_ tuple.select 0) tuple_371)))) SmokeDetectorAlarm)
Formula A: Bool
lhs: (set.all (lambda ((tuple_371 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_370) ((_ tuple.select 0) tuple_371)))) SmokeDetectorAlarm)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_370 (Tuple Int))) (and (set.all (lambda ((tuple_371 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_370) ((_ tuple.select 0) tuple_371)))) SmokeDetectorAlarm) true)) SmokeDetectorAlarm)
Formula A: Bool
lhs: (set.some (lambda ((tuple_369 (Tuple Int))) true) SmokeDetectorAlarm)
rhs: (set.some (lambda ((tuple_370 (Tuple Int))) (and (set.all (lambda ((tuple_371 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_370) ((_ tuple.select 0) tuple_371)))) SmokeDetectorAlarm) true)) SmokeDetectorAlarm)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_374) (+ ((_ tuple.select 0) tuple_372) 0))
rhs: (<= ((_ tuple.select 0) tuple_374) (+ ((_ tuple.select 0) tuple_372) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_374 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_372) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_374))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) OpenWindows)
Formula A: Bool
lhs: (set.some (lambda ((tuple_374 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_372) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_374))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) OpenWindows)
rhs: (= ((_ tuple.select 0) tuple_372) ((_ tuple.select 0) tuple_373))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_373 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_374 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_372) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_374))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) OpenWindows) (= ((_ tuple.select 0) tuple_372) ((_ tuple.select 0) tuple_373)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_372 (Tuple Int))) (set.some (lambda ((tuple_373 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_374 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_372) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_374))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) OpenWindows) (= ((_ tuple.select 0) tuple_372) ((_ tuple.select 0) tuple_373)))) Measure)) FireSafetyMeasures)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_377) (+ ((_ tuple.select 0) tuple_375) 0))
rhs: (<= ((_ tuple.select 0) tuple_377) (+ ((_ tuple.select 0) tuple_375) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_377 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_375) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_377))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) OpenWindows)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_377 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_375) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_377))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) OpenWindows))
rhs: (= ((_ tuple.select 0) tuple_375) ((_ tuple.select 0) tuple_376))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_376 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_377 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_375) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_377))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) OpenWindows)) (= ((_ tuple.select 0) tuple_375) ((_ tuple.select 0) tuple_376)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_375 (Tuple Int))) (set.some (lambda ((tuple_376 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_377 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_375) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_377))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) OpenWindows)) (= ((_ tuple.select 0) tuple_375) ((_ tuple.select 0) tuple_376)))) Measure)) FireSafetyMeasures)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_378 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_378) ((_ tuple.select 1) tuple_378))) (rel.product FireSafetyMeasures Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_379 (Tuple Int))) true) FireSafetyMeasures)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_380) ((_ tuple.select 0) tuple_381))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_381 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_380) ((_ tuple.select 0) tuple_381)))) FireSafetyMeasures)
Formula A: Bool
lhs: (set.all (lambda ((tuple_381 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_380) ((_ tuple.select 0) tuple_381)))) FireSafetyMeasures)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_380 (Tuple Int))) (and (set.all (lambda ((tuple_381 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_380) ((_ tuple.select 0) tuple_381)))) FireSafetyMeasures) true)) FireSafetyMeasures)
Formula A: Bool
lhs: (set.some (lambda ((tuple_379 (Tuple Int))) true) FireSafetyMeasures)
rhs: (set.some (lambda ((tuple_380 (Tuple Int))) (and (set.all (lambda ((tuple_381 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_380) ((_ tuple.select 0) tuple_381)))) FireSafetyMeasures) true)) FireSafetyMeasures)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_384) (+ ((_ tuple.select 0) tuple_382) 0))
rhs: (<= ((_ tuple.select 0) tuple_384) (+ ((_ tuple.select 0) tuple_382) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_384 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_382) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_384))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskUserIfOK)
Formula A: Bool
lhs: (set.some (lambda ((tuple_384 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_382) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_384))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskUserIfOK)
rhs: (= ((_ tuple.select 0) tuple_382) ((_ tuple.select 0) tuple_383))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_383 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_384 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_382) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_384))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskUserIfOK) (= ((_ tuple.select 0) tuple_382) ((_ tuple.select 0) tuple_383)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_382 (Tuple Int))) (set.some (lambda ((tuple_383 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_384 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_382) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_384))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskUserIfOK) (= ((_ tuple.select 0) tuple_382) ((_ tuple.select 0) tuple_383)))) Measure)) FireSafetyMeasures)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_387) (+ ((_ tuple.select 0) tuple_385) 0))
rhs: (<= ((_ tuple.select 0) tuple_387) (+ ((_ tuple.select 0) tuple_385) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_387 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_385) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_387))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskUserIfOK)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_387 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_385) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_387))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskUserIfOK))
rhs: (= ((_ tuple.select 0) tuple_385) ((_ tuple.select 0) tuple_386))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_386 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_387 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_385) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_387))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskUserIfOK)) (= ((_ tuple.select 0) tuple_385) ((_ tuple.select 0) tuple_386)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_385 (Tuple Int))) (set.some (lambda ((tuple_386 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_387 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_385) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_387))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskUserIfOK)) (= ((_ tuple.select 0) tuple_385) ((_ tuple.select 0) tuple_386)))) Measure)) FireSafetyMeasures)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_388 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_388) ((_ tuple.select 1) tuple_388))) (rel.product FireSafetyMeasures Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_389 (Tuple Int))) true) FireSafetyMeasures)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_390) ((_ tuple.select 0) tuple_391))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_391 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_390) ((_ tuple.select 0) tuple_391)))) FireSafetyMeasures)
Formula A: Bool
lhs: (set.all (lambda ((tuple_391 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_390) ((_ tuple.select 0) tuple_391)))) FireSafetyMeasures)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_390 (Tuple Int))) (and (set.all (lambda ((tuple_391 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_390) ((_ tuple.select 0) tuple_391)))) FireSafetyMeasures) true)) FireSafetyMeasures)
Formula A: Bool
lhs: (set.some (lambda ((tuple_389 (Tuple Int))) true) FireSafetyMeasures)
rhs: (set.some (lambda ((tuple_390 (Tuple Int))) (and (set.all (lambda ((tuple_391 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_390) ((_ tuple.select 0) tuple_391)))) FireSafetyMeasures) true)) FireSafetyMeasures)
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
lhs: (>= ((_ tuple.select 0) tuple_394) (+ ((_ tuple.select 0) tuple_392) 0))
rhs: (<= ((_ tuple.select 0) tuple_394) (+ ((_ tuple.select 0) tuple_392) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_394 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_392) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_394))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver)
Formula A: Bool
lhs: (set.some (lambda ((tuple_394 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_392) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_394))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver)
rhs: (= ((_ tuple.select 0) tuple_392) ((_ tuple.select 0) tuple_393))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_393 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_394 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_392) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_394))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver) (= ((_ tuple.select 0) tuple_392) ((_ tuple.select 0) tuple_393)))) Measure)
Formula A: Bool
Formula A: (set.all (lambda ((tuple_392 (Tuple Int))) (set.some (lambda ((tuple_393 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_394 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_392) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_394))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver) (= ((_ tuple.select 0) tuple_392) ((_ tuple.select 0) tuple_393)))) Measure)) FireSafetyMeasures)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_397) (+ ((_ tuple.select 0) tuple_395) 0))
rhs: (<= ((_ tuple.select 0) tuple_397) (+ ((_ tuple.select 0) tuple_395) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_397 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_395) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_397))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_397 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_395) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_397))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver))
rhs: (= ((_ tuple.select 0) tuple_395) ((_ tuple.select 0) tuple_396))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_396 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_397 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_395) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_397))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver)) (= ((_ tuple.select 0) tuple_395) ((_ tuple.select 0) tuple_396)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_395 (Tuple Int))) (set.some (lambda ((tuple_396 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_397 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_395) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_397))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformCaregiver)) (= ((_ tuple.select 0) tuple_395) ((_ tuple.select 0) tuple_396)))) Measure)) FireSafetyMeasures)
Formula A: Bool
Formula B: (set.some (lambda ((tuple_398 (Tuple Int Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (= ((_ tuple.select 0) tuple_398) ((_ tuple.select 1) tuple_398))) (rel.product FireSafetyMeasures Measure))
Formula B: Bool
Formula A: (set.some (lambda ((tuple_399 (Tuple Int))) true) FireSafetyMeasures)
Formula A: Bool
lhs: true
rhs: (>= ((_ tuple.select 0) tuple_400) ((_ tuple.select 0) tuple_401))
lhs: Bool
rhs: Bool
compare: Kind.IMPLIES
Formula A: (set.all (lambda ((tuple_401 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_400) ((_ tuple.select 0) tuple_401)))) FireSafetyMeasures)
Formula A: Bool
lhs: (set.all (lambda ((tuple_401 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_400) ((_ tuple.select 0) tuple_401)))) FireSafetyMeasures)
rhs: true
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_400 (Tuple Int))) (and (set.all (lambda ((tuple_401 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_400) ((_ tuple.select 0) tuple_401)))) FireSafetyMeasures) true)) FireSafetyMeasures)
Formula A: Bool
lhs: (set.some (lambda ((tuple_399 (Tuple Int))) true) FireSafetyMeasures)
rhs: (set.some (lambda ((tuple_400 (Tuple Int))) (and (set.all (lambda ((tuple_401 (Tuple Int))) (=> true (>= ((_ tuple.select 0) tuple_400) ((_ tuple.select 0) tuple_401)))) FireSafetyMeasures) true)) FireSafetyMeasures)
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
Formula A: (set.some (lambda ((tuple_404 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_402) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_404))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_404 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_402) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_404))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely))
rhs: (or (= ((_ tuple.select 14) tuple_403) 2) ((_ tuple.select 12) tuple_403))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (set.some (lambda ((tuple_404 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_402) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_404))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely)) (or (= ((_ tuple.select 14) tuple_403) 2) ((_ tuple.select 12) tuple_403)))
rhs: (= ((_ tuple.select 0) tuple_402) ((_ tuple.select 0) tuple_403))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_403 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (set.some (lambda ((tuple_404 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_402) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_404))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely)) (or (= ((_ tuple.select 14) tuple_403) 2) ((_ tuple.select 12) tuple_403))) (= ((_ tuple.select 0) tuple_402) ((_ tuple.select 0) tuple_403)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_402 (Tuple Int))) (set.some (lambda ((tuple_403 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (set.some (lambda ((tuple_404 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_402) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_404))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InterfereSafely)) (or (= ((_ tuple.select 14) tuple_403) 2) ((_ tuple.select 12) tuple_403))) (= ((_ tuple.select 0) tuple_402) ((_ tuple.select 0) tuple_403)))) Measure)) AllowUserToCook)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_407) (+ ((_ tuple.select 0) tuple_405) 0))
rhs: (<= ((_ tuple.select 0) tuple_407) (+ ((_ tuple.select 0) tuple_405) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_407 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_405) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_407))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_407 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_405) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_407))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser))
rhs: ((_ tuple.select 12) tuple_406)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (set.some (lambda ((tuple_407 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_405) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_407))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)) ((_ tuple.select 12) tuple_406))
rhs: (= ((_ tuple.select 0) tuple_405) ((_ tuple.select 0) tuple_406))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_406 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (set.some (lambda ((tuple_407 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_405) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_407))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)) ((_ tuple.select 12) tuple_406)) (= ((_ tuple.select 0) tuple_405) ((_ tuple.select 0) tuple_406)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_405 (Tuple Int))) (set.some (lambda ((tuple_406 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (set.some (lambda ((tuple_407 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_405) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_407))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)) ((_ tuple.select 12) tuple_406)) (= ((_ tuple.select 0) tuple_405) ((_ tuple.select 0) tuple_406)))) Measure)) CheckTemperature)
Formula A: Bool
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
Formula A: (set.some (lambda ((tuple_410 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_408))) (let ((_let_2 ((_ tuple.select 0) tuple_410))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 120)))))) CallEmergencyServices)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_410 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_408))) (let ((_let_2 ((_ tuple.select 0) tuple_410))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 120)))))) CallEmergencyServices))
rhs: (or ((_ tuple.select 8) tuple_409) (not ((_ tuple.select 7) tuple_409)))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (set.some (lambda ((tuple_410 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_408))) (let ((_let_2 ((_ tuple.select 0) tuple_410))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 120)))))) CallEmergencyServices)) (or ((_ tuple.select 8) tuple_409) (not ((_ tuple.select 7) tuple_409))))
rhs: (= ((_ tuple.select 0) tuple_408) ((_ tuple.select 0) tuple_409))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_409 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (set.some (lambda ((tuple_410 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_408))) (let ((_let_2 ((_ tuple.select 0) tuple_410))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 120)))))) CallEmergencyServices)) (or ((_ tuple.select 8) tuple_409) (not ((_ tuple.select 7) tuple_409)))) (= ((_ tuple.select 0) tuple_408) ((_ tuple.select 0) tuple_409)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_408 (Tuple Int))) (set.some (lambda ((tuple_409 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (set.some (lambda ((tuple_410 (Tuple Int))) (let ((_let_1 ((_ tuple.select 0) tuple_408))) (let ((_let_2 ((_ tuple.select 0) tuple_410))) (and (>= _let_2 (+ _let_1 0)) (<= _let_2 (+ _let_1 120)))))) CallEmergencyServices)) (or ((_ tuple.select 8) tuple_409) (not ((_ tuple.select 7) tuple_409)))) (= ((_ tuple.select 0) tuple_408) ((_ tuple.select 0) tuple_409)))) Measure)) SmokeDetectorAlarm)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_413) (+ ((_ tuple.select 0) tuple_411) 0))
rhs: (<= ((_ tuple.select 0) tuple_413) (+ ((_ tuple.select 0) tuple_411) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_413 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_411) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_413))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) OpenWindows)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_413 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_411) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_413))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) OpenWindows))
rhs: (= ((_ tuple.select 0) tuple_411) ((_ tuple.select 0) tuple_412))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_412 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_413 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_411) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_413))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) OpenWindows)) (= ((_ tuple.select 0) tuple_411) ((_ tuple.select 0) tuple_412)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_411 (Tuple Int))) (set.some (lambda ((tuple_412 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_413 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_411) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_413))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) OpenWindows)) (= ((_ tuple.select 0) tuple_411) ((_ tuple.select 0) tuple_412)))) Measure)) FireSafetyMeasures)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_416) (+ ((_ tuple.select 0) tuple_414) 0))
rhs: (<= ((_ tuple.select 0) tuple_416) (+ ((_ tuple.select 0) tuple_414) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_416 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_414) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_416))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AllowUserToCook)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_416 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_414) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_416))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AllowUserToCook))
rhs: (= ((_ tuple.select 0) tuple_414) ((_ tuple.select 0) tuple_415))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_415 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_416 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_414) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_416))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AllowUserToCook)) (= ((_ tuple.select 0) tuple_414) ((_ tuple.select 0) tuple_415)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_414 (Tuple Int))) (set.some (lambda ((tuple_415 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_416 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_414) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_416))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AllowUserToCook)) (= ((_ tuple.select 0) tuple_414) ((_ tuple.select 0) tuple_415)))) Measure)) UserWantsToCook)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_419) (+ ((_ tuple.select 0) tuple_417) 0))
rhs: (<= ((_ tuple.select 0) tuple_419) (+ ((_ tuple.select 0) tuple_417) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_419 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_417) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_419))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UseFirstPersonPluralLanguage)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_419 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_417) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_419))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UseFirstPersonPluralLanguage))
rhs: (= ((_ tuple.select 0) tuple_417) ((_ tuple.select 0) tuple_418))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_418 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_419 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_417) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_419))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UseFirstPersonPluralLanguage)) (= ((_ tuple.select 0) tuple_417) ((_ tuple.select 0) tuple_418)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_417 (Tuple Int))) (set.some (lambda ((tuple_418 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_419 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_417) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_419))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) UseFirstPersonPluralLanguage)) (= ((_ tuple.select 0) tuple_417) ((_ tuple.select 0) tuple_418)))) Measure)) GivingCookingInstructions)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_422) (+ ((_ tuple.select 0) tuple_420) 0))
rhs: (<= ((_ tuple.select 0) tuple_422) (+ ((_ tuple.select 0) tuple_420) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_422 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_420) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_422))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RecalculateApproach)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_422 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_420) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_422))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RecalculateApproach))
rhs: (< ((_ tuple.select 14) tuple_421) 2)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (set.some (lambda ((tuple_422 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_420) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_422))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RecalculateApproach)) (< ((_ tuple.select 14) tuple_421) 2))
rhs: (= ((_ tuple.select 0) tuple_420) ((_ tuple.select 0) tuple_421))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_421 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (set.some (lambda ((tuple_422 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_420) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_422))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RecalculateApproach)) (< ((_ tuple.select 14) tuple_421) 2)) (= ((_ tuple.select 0) tuple_420) ((_ tuple.select 0) tuple_421)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_420 (Tuple Int))) (set.some (lambda ((tuple_421 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (set.some (lambda ((tuple_422 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_420) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_422))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) RecalculateApproach)) (< ((_ tuple.select 14) tuple_421) 2)) (= ((_ tuple.select 0) tuple_420) ((_ tuple.select 0) tuple_421)))) Measure)) UserChangeMind)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_425) (+ ((_ tuple.select 0) tuple_423) 0))
rhs: (<= ((_ tuple.select 0) tuple_425) (+ ((_ tuple.select 0) tuple_423) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_425 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_423) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_425))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ConsiderUserPractices)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_425 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_423) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_425))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ConsiderUserPractices))
rhs: (= ((_ tuple.select 0) tuple_423) ((_ tuple.select 0) tuple_424))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_424 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_425 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_423) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_425))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ConsiderUserPractices)) (= ((_ tuple.select 0) tuple_423) ((_ tuple.select 0) tuple_424)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_423 (Tuple Int))) (set.some (lambda ((tuple_424 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (not (set.some (lambda ((tuple_425 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_423) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_425))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ConsiderUserPractices)) (= ((_ tuple.select 0) tuple_423) ((_ tuple.select 0) tuple_424)))) Measure)) GiveSuggestion)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_428) (+ ((_ tuple.select 0) tuple_426) 0))
rhs: (<= ((_ tuple.select 0) tuple_428) (+ ((_ tuple.select 0) tuple_426) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_428 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_426) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_428))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ShowDataHistory)
Formula A: Bool
lhs: (set.some (lambda ((tuple_428 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_426) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_428))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ShowDataHistory)
rhs: (not ((_ tuple.select 3) tuple_427))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (set.some (lambda ((tuple_428 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_426) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_428))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ShowDataHistory) (not ((_ tuple.select 3) tuple_427)))
rhs: (= ((_ tuple.select 0) tuple_426) ((_ tuple.select 0) tuple_427))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_427 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (set.some (lambda ((tuple_428 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_426) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_428))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ShowDataHistory) (not ((_ tuple.select 3) tuple_427))) (= ((_ tuple.select 0) tuple_426) ((_ tuple.select 0) tuple_427)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_426 (Tuple Int))) (set.some (lambda ((tuple_427 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (set.some (lambda ((tuple_428 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_426) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_428))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ShowDataHistory) (not ((_ tuple.select 3) tuple_427))) (= ((_ tuple.select 0) tuple_426) ((_ tuple.select 0) tuple_427)))) Measure)) AgentDeployed)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_431) (+ ((_ tuple.select 0) tuple_429) 0))
rhs: (<= ((_ tuple.select 0) tuple_431) (+ ((_ tuple.select 0) tuple_429) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_431 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_429) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_431))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ProvideDataSummaries)
Formula A: Bool
lhs: (not (set.some (lambda ((tuple_431 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_429) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_431))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ProvideDataSummaries))
rhs: ((_ tuple.select 4) tuple_430)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (not (set.some (lambda ((tuple_431 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_429) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_431))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ProvideDataSummaries)) ((_ tuple.select 4) tuple_430))
rhs: (= ((_ tuple.select 0) tuple_429) ((_ tuple.select 0) tuple_430))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_430 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (set.some (lambda ((tuple_431 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_429) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_431))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ProvideDataSummaries)) ((_ tuple.select 4) tuple_430)) (= ((_ tuple.select 0) tuple_429) ((_ tuple.select 0) tuple_430)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_429 (Tuple Int))) (set.some (lambda ((tuple_430 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (not (set.some (lambda ((tuple_431 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_429) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_431))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) ProvideDataSummaries)) ((_ tuple.select 4) tuple_430)) (= ((_ tuple.select 0) tuple_429) ((_ tuple.select 0) tuple_430)))) Measure)) ShowDataHistory)
Formula A: Bool
lhs: true
rhs: (= ((_ tuple.select 0) tuple_432) ((_ tuple.select 0) tuple_433))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_433 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and true (= ((_ tuple.select 0) tuple_432) ((_ tuple.select 0) tuple_433)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_432 (Tuple Int))) (set.some (lambda ((tuple_433 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and true (= ((_ tuple.select 0) tuple_432) ((_ tuple.select 0) tuple_433)))) Measure)) PreparingDeployment)
Formula A: Bool
lhs: true
rhs: (= ((_ tuple.select 0) tuple_434) ((_ tuple.select 0) tuple_435))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_435 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and true (= ((_ tuple.select 0) tuple_434) ((_ tuple.select 0) tuple_435)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_434 (Tuple Int))) (set.some (lambda ((tuple_435 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and true (= ((_ tuple.select 0) tuple_434) ((_ tuple.select 0) tuple_435)))) Measure)) MeetingUser)
Formula A: Bool
lhs: true
rhs: (= ((_ tuple.select 0) tuple_436) ((_ tuple.select 0) tuple_437))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_437 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and true (= ((_ tuple.select 0) tuple_436) ((_ tuple.select 0) tuple_437)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_436 (Tuple Int))) (set.some (lambda ((tuple_437 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and true (= ((_ tuple.select 0) tuple_436) ((_ tuple.select 0) tuple_437)))) Measure)) InformUser)
Formula A: Bool
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
Formula A: (set.some (lambda ((tuple_440 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_438) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_440))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)
Formula A: Bool
lhs: (set.some (lambda ((tuple_440 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_438) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_440))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser)
rhs: (or ((_ tuple.select 8) tuple_439) ((_ tuple.select 7) tuple_439))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (set.some (lambda ((tuple_440 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_438) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_440))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser) (or ((_ tuple.select 8) tuple_439) ((_ tuple.select 7) tuple_439)))
rhs: (= ((_ tuple.select 0) tuple_438) ((_ tuple.select 0) tuple_439))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_439 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (set.some (lambda ((tuple_440 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_438) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_440))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser) (or ((_ tuple.select 8) tuple_439) ((_ tuple.select 7) tuple_439))) (= ((_ tuple.select 0) tuple_438) ((_ tuple.select 0) tuple_439)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_438 (Tuple Int))) (set.some (lambda ((tuple_439 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (set.some (lambda ((tuple_440 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_438) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_440))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) InformUser) (or ((_ tuple.select 8) tuple_439) ((_ tuple.select 7) tuple_439))) (= ((_ tuple.select 0) tuple_438) ((_ tuple.select 0) tuple_439)))) Measure)) SmokeDetectorAlarm)
Formula A: Bool
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
Formula A: (set.some (lambda ((tuple_442 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and true (and (= ((_ tuple.select 14) tuple_442) 2) ((_ tuple.select 1) tuple_442))) (= ((_ tuple.select 0) tuple_441) ((_ tuple.select 0) tuple_442)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_441 (Tuple Int))) (set.some (lambda ((tuple_442 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and true (and (= ((_ tuple.select 14) tuple_442) 2) ((_ tuple.select 1) tuple_442))) (= ((_ tuple.select 0) tuple_441) ((_ tuple.select 0) tuple_442)))) Measure)) RemindUserOfLimitations)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_445) (+ ((_ tuple.select 0) tuple_443) 0))
rhs: (<= ((_ tuple.select 0) tuple_445) (+ ((_ tuple.select 0) tuple_443) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_445 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_443) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_445))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskUserIfOK)
Formula A: Bool
lhs: (set.some (lambda ((tuple_445 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_443) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_445))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskUserIfOK)
rhs: ((_ tuple.select 10) tuple_444)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (set.some (lambda ((tuple_445 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_443) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_445))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskUserIfOK) ((_ tuple.select 10) tuple_444))
rhs: (= ((_ tuple.select 0) tuple_443) ((_ tuple.select 0) tuple_444))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_444 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (set.some (lambda ((tuple_445 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_443) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_445))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskUserIfOK) ((_ tuple.select 10) tuple_444)) (= ((_ tuple.select 0) tuple_443) ((_ tuple.select 0) tuple_444)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_443 (Tuple Int))) (set.some (lambda ((tuple_444 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (set.some (lambda ((tuple_445 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_443) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_445))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskUserIfOK) ((_ tuple.select 10) tuple_444)) (= ((_ tuple.select 0) tuple_443) ((_ tuple.select 0) tuple_444)))) Measure)) HumanOnFloor)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_448) (+ ((_ tuple.select 0) tuple_446) 0))
rhs: (<= ((_ tuple.select 0) tuple_448) (+ ((_ tuple.select 0) tuple_446) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_448 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_446) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_448))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CallEmergencyServices)
Formula A: Bool
lhs: (set.some (lambda ((tuple_448 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_446) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_448))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CallEmergencyServices)
rhs: (= ((_ tuple.select 14) tuple_447) 2)
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (set.some (lambda ((tuple_448 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_446) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_448))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CallEmergencyServices) (= ((_ tuple.select 14) tuple_447) 2))
rhs: (= ((_ tuple.select 0) tuple_446) ((_ tuple.select 0) tuple_447))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_447 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (set.some (lambda ((tuple_448 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_446) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_448))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CallEmergencyServices) (= ((_ tuple.select 14) tuple_447) 2)) (= ((_ tuple.select 0) tuple_446) ((_ tuple.select 0) tuple_447)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_446 (Tuple Int))) (set.some (lambda ((tuple_447 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (set.some (lambda ((tuple_448 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_446) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_448))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) CallEmergencyServices) (= ((_ tuple.select 14) tuple_447) 2)) (= ((_ tuple.select 0) tuple_446) ((_ tuple.select 0) tuple_447)))) Measure)) HumanOnFloor)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_451) (+ ((_ tuple.select 0) tuple_449) 0))
rhs: (<= ((_ tuple.select 0) tuple_451) (+ ((_ tuple.select 0) tuple_449) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_451 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_449) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_451))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskUserIfOK)
Formula A: Bool
lhs: (set.some (lambda ((tuple_451 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_449) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_451))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskUserIfOK)
rhs: (= ((_ tuple.select 0) tuple_449) ((_ tuple.select 0) tuple_450))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_450 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_451 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_449) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_451))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskUserIfOK) (= ((_ tuple.select 0) tuple_449) ((_ tuple.select 0) tuple_450)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_449 (Tuple Int))) (set.some (lambda ((tuple_450 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_451 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_449) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_451))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) AskUserIfOK) (= ((_ tuple.select 0) tuple_449) ((_ tuple.select 0) tuple_450)))) Measure)) UserUnpredictable)
Formula A: Bool
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
Formula A: (set.some (lambda ((tuple_453 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and true ((_ tuple.select 3) tuple_453)) (= ((_ tuple.select 0) tuple_452) ((_ tuple.select 0) tuple_453)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_452 (Tuple Int))) (set.some (lambda ((tuple_453 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and true ((_ tuple.select 3) tuple_453)) (= ((_ tuple.select 0) tuple_452) ((_ tuple.select 0) tuple_453)))) Measure)) ShowDataHistory)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_456) (+ ((_ tuple.select 0) tuple_454) 0))
rhs: (<= ((_ tuple.select 0) tuple_456) (+ ((_ tuple.select 0) tuple_454) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_456 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_454) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_456))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) MonitorMealTime)
Formula A: Bool
lhs: (set.some (lambda ((tuple_456 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_454) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_456))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) MonitorMealTime)
rhs: (not ((_ tuple.select 1) tuple_455))
lhs: Bool
rhs: Bool
compare: Kind.AND
lhs: (and (set.some (lambda ((tuple_456 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_454) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_456))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) MonitorMealTime) (not ((_ tuple.select 1) tuple_455)))
rhs: (= ((_ tuple.select 0) tuple_454) ((_ tuple.select 0) tuple_455))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_455 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (set.some (lambda ((tuple_456 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_454) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_456))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) MonitorMealTime) (not ((_ tuple.select 1) tuple_455))) (= ((_ tuple.select 0) tuple_454) ((_ tuple.select 0) tuple_455)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_454 (Tuple Int))) (set.some (lambda ((tuple_455 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and (set.some (lambda ((tuple_456 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_454) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_456))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) MonitorMealTime) (not ((_ tuple.select 1) tuple_455))) (= ((_ tuple.select 0) tuple_454) ((_ tuple.select 0) tuple_455)))) Measure)) InformUser)
Formula A: Bool
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
Formula A: (set.some (lambda ((tuple_458 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and true ((_ tuple.select 12) tuple_458)) (= ((_ tuple.select 0) tuple_457) ((_ tuple.select 0) tuple_458)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_457 (Tuple Int))) (set.some (lambda ((tuple_458 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and true ((_ tuple.select 12) tuple_458)) (= ((_ tuple.select 0) tuple_457) ((_ tuple.select 0) tuple_458)))) Measure)) InformUser)
Formula A: Bool
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
Formula A: (set.some (lambda ((tuple_460 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and true (or (= ((_ tuple.select 14) tuple_460) 2) ((_ tuple.select 12) tuple_460))) (= ((_ tuple.select 0) tuple_459) ((_ tuple.select 0) tuple_460)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_459 (Tuple Int))) (set.some (lambda ((tuple_460 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and true (or (= ((_ tuple.select 14) tuple_460) 2) ((_ tuple.select 12) tuple_460))) (= ((_ tuple.select 0) tuple_459) ((_ tuple.select 0) tuple_460)))) Measure)) InterfereSafely)
Formula A: Bool
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
Formula A: (set.some (lambda ((tuple_462 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and true (< ((_ tuple.select 14) tuple_462) 2)) (= ((_ tuple.select 0) tuple_461) ((_ tuple.select 0) tuple_462)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_461 (Tuple Int))) (set.some (lambda ((tuple_462 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (and true (< ((_ tuple.select 14) tuple_462) 2)) (= ((_ tuple.select 0) tuple_461) ((_ tuple.select 0) tuple_462)))) Measure)) UserChangeMind)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_465) (+ ((_ tuple.select 0) tuple_463) 0))
rhs: (<= ((_ tuple.select 0) tuple_465) (+ ((_ tuple.select 0) tuple_463) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_465 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_463) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_465))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) HumanOnFloor)
Formula A: Bool
lhs: (set.some (lambda ((tuple_465 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_463) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_465))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) HumanOnFloor)
rhs: (= ((_ tuple.select 0) tuple_463) ((_ tuple.select 0) tuple_464))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_464 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_465 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_463) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_465))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) HumanOnFloor) (= ((_ tuple.select 0) tuple_463) ((_ tuple.select 0) tuple_464)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_463 (Tuple Int))) (set.some (lambda ((tuple_464 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_465 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_463) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_465))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) HumanOnFloor) (= ((_ tuple.select 0) tuple_463) ((_ tuple.select 0) tuple_464)))) Measure)) CallEmergencyServices)
Formula A: Bool
lhs: (>= ((_ tuple.select 0) tuple_468) (+ ((_ tuple.select 0) tuple_466) 0))
rhs: (<= ((_ tuple.select 0) tuple_468) (+ ((_ tuple.select 0) tuple_466) 0))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_468 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_466) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_468))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) SmokeDetectorAlarm)
Formula A: Bool
lhs: (set.some (lambda ((tuple_468 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_466) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_468))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) SmokeDetectorAlarm)
rhs: (= ((_ tuple.select 0) tuple_466) ((_ tuple.select 0) tuple_467))
lhs: Bool
rhs: Bool
compare: Kind.AND
Formula A: (set.some (lambda ((tuple_467 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_468 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_466) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_468))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) SmokeDetectorAlarm) (= ((_ tuple.select 0) tuple_466) ((_ tuple.select 0) tuple_467)))) Measure)
Formula A: Bool
Formula A: (set.some (lambda ((tuple_466 (Tuple Int))) (set.some (lambda ((tuple_467 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (and (set.some (lambda ((tuple_468 (Tuple Int))) (let ((_let_1 (+ ((_ tuple.select 0) tuple_466) 0))) (let ((_let_2 ((_ tuple.select 0) tuple_468))) (and (>= _let_2 _let_1) (<= _let_2 _let_1))))) SmokeDetectorAlarm) (= ((_ tuple.select 0) tuple_466) ((_ tuple.select 0) tuple_467)))) Measure)) CallEmergencyServices)
Formula A: Bool
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
Formula B: (set.all (lambda ((tuple_469 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 (= ((_ tuple.select 0) tuple_469) ((_ tuple.select 16) tuple_469)))) (=> _let_1 (and (= ((_ tuple.select 15) tuple_469) ((_ tuple.select 31) tuple_469)) (and (= ((_ tuple.select 14) tuple_469) ((_ tuple.select 30) tuple_469)) (and (= ((_ tuple.select 13) tuple_469) ((_ tuple.select 29) tuple_469)) (and (= ((_ tuple.select 12) tuple_469) ((_ tuple.select 28) tuple_469)) (and (= ((_ tuple.select 11) tuple_469) ((_ tuple.select 27) tuple_469)) (and (= ((_ tuple.select 10) tuple_469) ((_ tuple.select 26) tuple_469)) (and (= ((_ tuple.select 9) tuple_469) ((_ tuple.select 25) tuple_469)) (and (= ((_ tuple.select 8) tuple_469) ((_ tuple.select 24) tuple_469)) (and (= ((_ tuple.select 7) tuple_469) ((_ tuple.select 23) tuple_469)) (and (= ((_ tuple.select 6) tuple_469) ((_ tuple.select 22) tuple_469)) (and (= ((_ tuple.select 5) tuple_469) ((_ tuple.select 21) tuple_469)) (and (= ((_ tuple.select 4) tuple_469) ((_ tuple.select 20) tuple_469)) (and (= ((_ tuple.select 3) tuple_469) ((_ tuple.select 19) tuple_469)) (and (= ((_ tuple.select 2) tuple_469) ((_ tuple.select 18) tuple_469)) (and (= ((_ tuple.select 1) tuple_469) ((_ tuple.select 17) tuple_469)) _let_1)))))))))))))))))) (rel.product Measure Measure))
Formula B: Bool
lhs: (rel.product Measure Measure)
rhs: (lambda ((tuple_469 (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))) (let ((_let_1 (= ((_ tuple.select 0) tuple_469) ((_ tuple.select 16) tuple_469)))) (=> _let_1 (and (= ((_ tuple.select 15) tuple_469) ((_ tuple.select 31) tuple_469)) (and (= ((_ tuple.select 14) tuple_469) ((_ tuple.select 30) tuple_469)) (and (= ((_ tuple.select 13) tuple_469) ((_ tuple.select 29) tuple_469)) (and (= ((_ tuple.select 12) tuple_469) ((_ tuple.select 28) tuple_469)) (and (= ((_ tuple.select 11) tuple_469) ((_ tuple.select 27) tuple_469)) (and (= ((_ tuple.select 10) tuple_469) ((_ tuple.select 26) tuple_469)) (and (= ((_ tuple.select 9) tuple_469) ((_ tuple.select 25) tuple_469)) (and (= ((_ tuple.select 8) tuple_469) ((_ tuple.select 24) tuple_469)) (and (= ((_ tuple.select 7) tuple_469) ((_ tuple.select 23) tuple_469)) (and (= ((_ tuple.select 6) tuple_469) ((_ tuple.select 22) tuple_469)) (and (= ((_ tuple.select 5) tuple_469) ((_ tuple.select 21) tuple_469)) (and (= ((_ tuple.select 4) tuple_469) ((_ tuple.select 20) tuple_469)) (and (= ((_ tuple.select 3) tuple_469) ((_ tuple.select 19) tuple_469)) (and (= ((_ tuple.select 2) tuple_469) ((_ tuple.select 18) tuple_469)) (and (= ((_ tuple.select 1) tuple_469) ((_ tuple.select 17) tuple_469)) _let_1))))))))))))))))))
lhs: (Set (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool))
rhs: (-> (Tuple Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool Int Bool Int Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool) Bool)
compare: Kind.AND
