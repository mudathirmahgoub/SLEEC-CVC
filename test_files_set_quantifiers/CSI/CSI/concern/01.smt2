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
(declare-const time (Set (Tuple Int)))
(declare-const RobotMoving (Set (Tuple Int)))
(declare-const not_RobotMoving (Set (Tuple Int Int)))
(declare-const RobotWorking (Set (Tuple Int)))
(declare-const not_RobotWorking (Set (Tuple Int Int)))
(declare-const RobotContinueTask (Set (Tuple Int)))
(declare-const not_RobotContinueTask (Set (Tuple Int Int)))
(declare-const RobotStopAction (Set (Tuple Int)))
(declare-const not_RobotStopAction (Set (Tuple Int Int)))
(declare-const AvoidBumping (Set (Tuple Int)))
(declare-const not_AvoidBumping (Set (Tuple Int Int)))
(declare-const AdjustRoute (Set (Tuple Int)))
(declare-const not_AdjustRoute (Set (Tuple Int Int)))
(declare-const InquireSafety (Set (Tuple Int)))
(declare-const not_InquireSafety (Set (Tuple Int Int)))
(declare-const AccountHumanRandomness (Set (Tuple Int)))
(declare-const not_AccountHumanRandomness (Set (Tuple Int Int)))
(declare-const TrackHumanLocation (Set (Tuple Int)))
(declare-const not_TrackHumanLocation (Set (Tuple Int Int)))
(declare-const InformHuman (Set (Tuple Int)))
(declare-const not_InformHuman (Set (Tuple Int Int)))
(declare-const HumanSaysStop (Set (Tuple Int)))
(declare-const not_HumanSaysStop (Set (Tuple Int Int)))
(declare-const AskPermission (Set (Tuple Int)))
(declare-const not_AskPermission (Set (Tuple Int Int)))
(declare-const MoveAtSafeSpeed (Set (Tuple Int)))
(declare-const not_MoveAtSafeSpeed (Set (Tuple Int Int)))
(declare-const IncreaseSpeed (Set (Tuple Int)))
(declare-const not_IncreaseSpeed (Set (Tuple Int Int)))
(declare-const PreparingRobot (Set (Tuple Int)))
(declare-const not_PreparingRobot (Set (Tuple Int Int)))
(declare-const AssignToRobot (Set (Tuple Int)))
(declare-const not_AssignToRobot (Set (Tuple Int Int)))
(declare-const AssignLiability (Set (Tuple Int)))
(declare-const not_AssignLiability (Set (Tuple Int Int)))
(declare-const ConsiderAppearance (Set (Tuple Int)))
(declare-const not_ConsiderAppearance (Set (Tuple Int Int)))
(declare-const ReportIncident (Set (Tuple Int)))
(declare-const not_ReportIncident (Set (Tuple Int Int)))
(declare-const MinimizeCobotCollaboration (Set (Tuple Int)))
(declare-const not_MinimizeCobotCollaboration (Set (Tuple Int Int)))
(declare-const PrioritizeHumans (Set (Tuple Int)))
(declare-const not_PrioritizeHumans (Set (Tuple Int Int)))
(declare-const ActionHumanRandom (Set (Tuple Int)))
(declare-const not_ActionHumanRandom (Set (Tuple Int Int)))
(declare-const MoveAwayFromHuman (Set (Tuple Int)))
(declare-const not_MoveAwayFromHuman (Set (Tuple Int Int)))
(declare-const risk (Set (Tuple Int)))
(declare-const efficiency (Set (Tuple Int)))
(declare-const Measure (Set (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool)))
(assert (set.exists ((tuple_244 (Tuple Int))) RobotMoving (set.exists ((tuple_245 (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool))) Measure (and (and (set.exists ((tuple_247 (Tuple Int Int))) not_AvoidBumping (and (= ((_ tuple.select 1) tuple_247) (+ ((_ tuple.select 0) tuple_244) 0)) (= ((_ tuple.select 0) tuple_247) (+ ((_ tuple.select 0) tuple_244) 0)))) (or (or (not ((_ tuple.select 5) tuple_245)) ((_ tuple.select 4) tuple_245)) ((_ tuple.select 2) tuple_245))) (= ((_ tuple.select 0) tuple_244) ((_ tuple.select 0) tuple_245))))))
(assert (set.forall ((tuple_4 (Tuple Int))) RobotMoving (set.exists ((tuple_5 (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool))) Measure (and (and (=> (and true (and (not ((_ tuple.select 1) tuple_5)) (and (not ((_ tuple.select 4) tuple_5)) (and (not ((_ tuple.select 3) tuple_5)) true)))) (set.exists ((tuple_6 (Tuple Int))) AvoidBumping (and (>= ((_ tuple.select 0) tuple_6) (+ ((_ tuple.select 0) tuple_4) 0)) (<= ((_ tuple.select 0) tuple_6) (+ ((_ tuple.select 0) tuple_4) 0))))) (and (=> (and ((_ tuple.select 1) tuple_5) (and (not ((_ tuple.select 4) tuple_5)) (and (not ((_ tuple.select 3) tuple_5)) true))) (set.exists ((tuple_7 (Tuple Int))) AdjustRoute (and (>= ((_ tuple.select 0) tuple_7) (+ ((_ tuple.select 0) tuple_4) 0)) (<= ((_ tuple.select 0) tuple_7) (+ ((_ tuple.select 0) tuple_4) 0))))) (and (=> (and ((_ tuple.select 4) tuple_5) (and (not ((_ tuple.select 3) tuple_5)) true)) (set.exists ((tuple_8 (Tuple Int))) AdjustRoute (and (>= ((_ tuple.select 0) tuple_8) (+ ((_ tuple.select 0) tuple_4) 0)) (<= ((_ tuple.select 0) tuple_8) (+ ((_ tuple.select 0) tuple_4) 0))))) (=> (and ((_ tuple.select 3) tuple_5) true) (set.exists ((tuple_9 (Tuple Int))) InquireSafety (and (>= ((_ tuple.select 0) tuple_9) (+ ((_ tuple.select 0) tuple_4) 0)) (<= ((_ tuple.select 0) tuple_9) (+ ((_ tuple.select 0) tuple_4) 0)))))))) (= ((_ tuple.select 0) tuple_4) ((_ tuple.select 0) tuple_5))))))
(assert (set.forall ((tuple_20 (Tuple Int))) RobotMoving (set.exists ((tuple_21 (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool))) Measure (and (set.exists ((tuple_22 (Tuple Int))) AccountHumanRandomness (and (>= ((_ tuple.select 0) tuple_22) (+ ((_ tuple.select 0) tuple_20) 0)) (<= ((_ tuple.select 0) tuple_22) (+ ((_ tuple.select 0) tuple_20) 0)))) (= ((_ tuple.select 0) tuple_20) ((_ tuple.select 0) tuple_21))))))
(assert (set.forall ((tuple_30 (Tuple Int))) RobotMoving (set.exists ((tuple_31 (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool))) Measure (and (set.exists ((tuple_32 (Tuple Int))) TrackHumanLocation (and (>= ((_ tuple.select 0) tuple_32) (+ ((_ tuple.select 0) tuple_30) 0)) (<= ((_ tuple.select 0) tuple_32) (+ ((_ tuple.select 0) tuple_30) 0)))) (= ((_ tuple.select 0) tuple_30) ((_ tuple.select 0) tuple_31))))))
(assert (set.forall ((tuple_40 (Tuple Int))) RobotWorking (set.exists ((tuple_41 (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool))) Measure (and (set.exists ((tuple_42 (Tuple Int))) InformHuman (and (>= ((_ tuple.select 0) tuple_42) (+ ((_ tuple.select 0) tuple_40) 0)) (<= ((_ tuple.select 0) tuple_42) (+ ((_ tuple.select 0) tuple_40) 0)))) (= ((_ tuple.select 0) tuple_40) ((_ tuple.select 0) tuple_41))))))
(assert (set.forall ((tuple_50 (Tuple Int))) RobotWorking (set.exists ((tuple_51 (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool))) Measure (and (set.exists ((tuple_52 (Tuple Int))) InformHuman (and (>= ((_ tuple.select 0) tuple_52) (+ ((_ tuple.select 0) tuple_50) 0)) (<= ((_ tuple.select 0) tuple_52) (+ ((_ tuple.select 0) tuple_50) 0)))) (= ((_ tuple.select 0) tuple_50) ((_ tuple.select 0) tuple_51))))))
(assert (set.forall ((tuple_60 (Tuple Int))) HumanSaysStop (set.exists ((tuple_61 (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool))) Measure (and (set.exists ((tuple_62 (Tuple Int))) RobotStopAction (and (>= ((_ tuple.select 0) tuple_62) (+ ((_ tuple.select 0) tuple_60) 0)) (<= ((_ tuple.select 0) tuple_62) (+ ((_ tuple.select 0) tuple_60) 0)))) (= ((_ tuple.select 0) tuple_60) ((_ tuple.select 0) tuple_61))))))
(assert (set.forall ((tuple_70 (Tuple Int))) InformHuman (set.exists ((tuple_71 (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool))) Measure (and (and (=> (and true (and (not ((_ tuple.select 1) tuple_71)) (and (not (not ((_ tuple.select 5) tuple_71))) true))) (set.exists ((tuple_72 (Tuple Int))) RobotMoving (and (>= ((_ tuple.select 0) tuple_72) (+ ((_ tuple.select 0) tuple_70) 0)) (<= ((_ tuple.select 0) tuple_72) (+ ((_ tuple.select 0) tuple_70) 0))))) (and (=> (and ((_ tuple.select 1) tuple_71) (and (not (not ((_ tuple.select 5) tuple_71))) true)) (set.exists ((tuple_73 (Tuple Int))) AdjustRoute (and (>= ((_ tuple.select 0) tuple_73) (+ ((_ tuple.select 0) tuple_70) 0)) (<= ((_ tuple.select 0) tuple_73) (+ ((_ tuple.select 0) tuple_70) 0))))) (=> (and (not ((_ tuple.select 5) tuple_71)) true) (set.exists ((tuple_74 (Tuple Int))) AskPermission (and (>= ((_ tuple.select 0) tuple_74) (+ ((_ tuple.select 0) tuple_70) 0)) (<= ((_ tuple.select 0) tuple_74) (+ ((_ tuple.select 0) tuple_70) 0))))))) (= ((_ tuple.select 0) tuple_70) ((_ tuple.select 0) tuple_71))))))
(assert (set.forall ((tuple_84 (Tuple Int))) RobotMoving (set.exists ((tuple_85 (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool))) Measure (and (or (and (=> (and true (and (not ((_ tuple.select 6) tuple_85)) true)) (set.exists ((tuple_86 (Tuple Int))) RobotStopAction (and (>= ((_ tuple.select 0) tuple_86) (+ ((_ tuple.select 0) tuple_84) 0)) (<= ((_ tuple.select 0) tuple_86) (+ ((_ tuple.select 0) tuple_84) 0))))) (=> (and ((_ tuple.select 6) tuple_85) true) (set.exists ((tuple_87 (Tuple Int))) RobotContinueTask (and (>= ((_ tuple.select 0) tuple_87) (+ ((_ tuple.select 0) tuple_84) 0)) (<= ((_ tuple.select 0) tuple_87) (+ ((_ tuple.select 0) tuple_84) 0)))))) (not ((_ tuple.select 2) tuple_85))) (= ((_ tuple.select 0) tuple_84) ((_ tuple.select 0) tuple_85))))))
(assert (set.forall ((tuple_99 (Tuple Int))) RobotMoving (set.exists ((tuple_100 (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool))) Measure (and (and (=> (and true (and (not (and (= ((_ tuple.select 7) tuple_100) 0) (= ((_ tuple.select 8) tuple_100) 0))) true)) (set.exists ((tuple_101 (Tuple Int))) MoveAtSafeSpeed (and (>= ((_ tuple.select 0) tuple_101) (+ ((_ tuple.select 0) tuple_99) 0)) (<= ((_ tuple.select 0) tuple_101) (+ ((_ tuple.select 0) tuple_99) 0))))) (=> (and (and (= ((_ tuple.select 7) tuple_100) 0) (= ((_ tuple.select 8) tuple_100) 0)) true) (set.exists ((tuple_102 (Tuple Int))) IncreaseSpeed (and (>= ((_ tuple.select 0) tuple_102) (+ ((_ tuple.select 0) tuple_99) 0)) (<= ((_ tuple.select 0) tuple_102) (+ ((_ tuple.select 0) tuple_99) 0)))))) (= ((_ tuple.select 0) tuple_99) ((_ tuple.select 0) tuple_100))))))
(assert (set.forall ((tuple_111 (Tuple Int))) PreparingRobot (set.exists ((tuple_112 (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool))) Measure (and (or (and (=> (and true (and (not ((_ tuple.select 10) tuple_112)) true)) (set.exists ((tuple_114 (Tuple Int Int))) not_AssignToRobot (and (= ((_ tuple.select 1) tuple_114) (+ ((_ tuple.select 0) tuple_111) 0)) (= ((_ tuple.select 0) tuple_114) (+ ((_ tuple.select 0) tuple_111) 0))))) (=> (and ((_ tuple.select 10) tuple_112) true) true)) (not ((_ tuple.select 9) tuple_112))) (= ((_ tuple.select 0) tuple_111) ((_ tuple.select 0) tuple_112))))))
(assert (set.forall ((tuple_126 (Tuple Int))) PreparingRobot (set.exists ((tuple_127 (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool))) Measure (and (set.exists ((tuple_128 (Tuple Int))) AssignLiability (and (>= ((_ tuple.select 0) tuple_128) (+ ((_ tuple.select 0) tuple_126) 0)) (<= ((_ tuple.select 0) tuple_128) (+ ((_ tuple.select 0) tuple_126) 0)))) (= ((_ tuple.select 0) tuple_126) ((_ tuple.select 0) tuple_127))))))
(assert (set.forall ((tuple_136 (Tuple Int))) PreparingRobot (set.exists ((tuple_137 (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool))) Measure (and (set.exists ((tuple_138 (Tuple Int))) InformHuman (and (>= ((_ tuple.select 0) tuple_138) (+ ((_ tuple.select 0) tuple_136) 0)) (<= ((_ tuple.select 0) tuple_138) (+ ((_ tuple.select 0) tuple_136) 0)))) (= ((_ tuple.select 0) tuple_136) ((_ tuple.select 0) tuple_137))))))
(assert (set.forall ((tuple_146 (Tuple Int))) PreparingRobot (set.exists ((tuple_147 (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool))) Measure (and (set.exists ((tuple_148 (Tuple Int))) ConsiderAppearance (and (>= ((_ tuple.select 0) tuple_148) (+ ((_ tuple.select 0) tuple_146) 0)) (<= ((_ tuple.select 0) tuple_148) (+ ((_ tuple.select 0) tuple_146) 0)))) (= ((_ tuple.select 0) tuple_146) ((_ tuple.select 0) tuple_147))))))
(assert (set.forall ((tuple_156 (Tuple Int))) PreparingRobot (set.exists ((tuple_157 (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool))) Measure (and (set.exists ((tuple_158 (Tuple Int))) MinimizeCobotCollaboration (and (>= ((_ tuple.select 0) tuple_158) (+ ((_ tuple.select 0) tuple_156) 0)) (<= ((_ tuple.select 0) tuple_158) (+ ((_ tuple.select 0) tuple_156) 0)))) (= ((_ tuple.select 0) tuple_156) ((_ tuple.select 0) tuple_157))))))
(assert (set.forall ((tuple_166 (Tuple Int))) PreparingRobot (set.exists ((tuple_167 (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool))) Measure (and (set.exists ((tuple_168 (Tuple Int))) PrioritizeHumans (and (>= ((_ tuple.select 0) tuple_168) (+ ((_ tuple.select 0) tuple_166) 0)) (<= ((_ tuple.select 0) tuple_168) (+ ((_ tuple.select 0) tuple_166) 0)))) (= ((_ tuple.select 0) tuple_166) ((_ tuple.select 0) tuple_167))))))
(assert (set.forall ((tuple_176 (Tuple Int))) RobotWorking (set.exists ((tuple_177 (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool))) Measure (and (or (set.exists ((tuple_178 (Tuple Int))) RobotStopAction (and (>= ((_ tuple.select 0) tuple_178) (+ ((_ tuple.select 0) tuple_176) 0)) (<= ((_ tuple.select 0) tuple_178) (+ ((_ tuple.select 0) tuple_176) 0)))) (not ((_ tuple.select 11) tuple_177))) (= ((_ tuple.select 0) tuple_176) ((_ tuple.select 0) tuple_177))))))
(assert (set.forall ((tuple_189 (Tuple Int))) RobotWorking (set.exists ((tuple_190 (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool))) Measure (and (or (set.exists ((tuple_191 (Tuple Int))) ReportIncident (and (>= ((_ tuple.select 0) tuple_191) (+ ((_ tuple.select 0) tuple_189) 0)) (<= ((_ tuple.select 0) tuple_191) (+ ((_ tuple.select 0) tuple_189) 0)))) (not ((_ tuple.select 11) tuple_190))) (= ((_ tuple.select 0) tuple_189) ((_ tuple.select 0) tuple_190))))))
(assert (set.forall ((tuple_202 (Tuple Int))) PreparingRobot (set.exists ((tuple_203 (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool))) Measure (and (or (set.exists ((tuple_204 (Tuple Int))) InformHuman (and (>= ((_ tuple.select 0) tuple_204) (+ ((_ tuple.select 0) tuple_202) 0)) (<= ((_ tuple.select 0) tuple_204) (+ ((_ tuple.select 0) tuple_202) 0)))) (not ((_ tuple.select 12) tuple_203))) (= ((_ tuple.select 0) tuple_202) ((_ tuple.select 0) tuple_203))))))
(assert (set.forall ((tuple_215 (Tuple Int))) RobotWorking (set.exists ((tuple_216 (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool))) Measure (and (or (set.exists ((tuple_217 (Tuple Int))) ReportIncident (and (>= ((_ tuple.select 0) tuple_217) (+ ((_ tuple.select 0) tuple_215) 0)) (<= ((_ tuple.select 0) tuple_217) (+ ((_ tuple.select 0) tuple_215) 0)))) (not ((_ tuple.select 13) tuple_216))) (= ((_ tuple.select 0) tuple_215) ((_ tuple.select 0) tuple_216))))))
(assert (set.forall ((tuple_228 (Tuple Int))) RobotWorking (set.exists ((tuple_229 (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool))) Measure (and (or (set.exists ((tuple_230 (Tuple Int))) RobotStopAction (and (>= ((_ tuple.select 0) tuple_230) (+ ((_ tuple.select 0) tuple_228) 0)) (<= ((_ tuple.select 0) tuple_230) (+ ((_ tuple.select 0) tuple_228) 0)))) (not ((_ tuple.select 13) tuple_229))) (= ((_ tuple.select 0) tuple_228) ((_ tuple.select 0) tuple_229))))))
(assert (and (and (forall ((MoveAwayFromHuman_time_Int_66 Int) (not_MoveAwayFromHuman_start_time_Int_67 Int) (not_MoveAwayFromHuman_end_time_Int_68 Int)) (=> (and (set.member (tuple not_MoveAwayFromHuman_start_time_Int_67 not_MoveAwayFromHuman_end_time_Int_68) not_MoveAwayFromHuman) (set.member (tuple MoveAwayFromHuman_time_Int_66) MoveAwayFromHuman)) (not (and (<= MoveAwayFromHuman_time_Int_66 not_MoveAwayFromHuman_end_time_Int_68) (<= not_MoveAwayFromHuman_start_time_Int_67 MoveAwayFromHuman_time_Int_66))))) (and (forall ((ActionHumanRandom_time_Int_63 Int) (not_ActionHumanRandom_start_time_Int_64 Int) (not_ActionHumanRandom_end_time_Int_65 Int)) (=> (and (set.member (tuple not_ActionHumanRandom_start_time_Int_64 not_ActionHumanRandom_end_time_Int_65) not_ActionHumanRandom) (set.member (tuple ActionHumanRandom_time_Int_63) ActionHumanRandom)) (not (and (<= ActionHumanRandom_time_Int_63 not_ActionHumanRandom_end_time_Int_65) (<= not_ActionHumanRandom_start_time_Int_64 ActionHumanRandom_time_Int_63))))) (and (forall ((PrioritizeHumans_time_Int_60 Int) (not_PrioritizeHumans_start_time_Int_61 Int) (not_PrioritizeHumans_end_time_Int_62 Int)) (=> (and (set.member (tuple not_PrioritizeHumans_start_time_Int_61 not_PrioritizeHumans_end_time_Int_62) not_PrioritizeHumans) (set.member (tuple PrioritizeHumans_time_Int_60) PrioritizeHumans)) (not (and (<= PrioritizeHumans_time_Int_60 not_PrioritizeHumans_end_time_Int_62) (<= not_PrioritizeHumans_start_time_Int_61 PrioritizeHumans_time_Int_60))))) (and (forall ((MinimizeCobotCollaboration_time_Int_57 Int) (not_MinimizeCobotCollaboration_start_time_Int_58 Int) (not_MinimizeCobotCollaboration_end_time_Int_59 Int)) (=> (and (set.member (tuple not_MinimizeCobotCollaboration_start_time_Int_58 not_MinimizeCobotCollaboration_end_time_Int_59) not_MinimizeCobotCollaboration) (set.member (tuple MinimizeCobotCollaboration_time_Int_57) MinimizeCobotCollaboration)) (not (and (<= MinimizeCobotCollaboration_time_Int_57 not_MinimizeCobotCollaboration_end_time_Int_59) (<= not_MinimizeCobotCollaboration_start_time_Int_58 MinimizeCobotCollaboration_time_Int_57))))) (and (forall ((ReportIncident_time_Int_54 Int) (not_ReportIncident_start_time_Int_55 Int) (not_ReportIncident_end_time_Int_56 Int)) (=> (and (set.member (tuple not_ReportIncident_start_time_Int_55 not_ReportIncident_end_time_Int_56) not_ReportIncident) (set.member (tuple ReportIncident_time_Int_54) ReportIncident)) (not (and (<= ReportIncident_time_Int_54 not_ReportIncident_end_time_Int_56) (<= not_ReportIncident_start_time_Int_55 ReportIncident_time_Int_54))))) (and (forall ((ConsiderAppearance_time_Int_51 Int) (not_ConsiderAppearance_start_time_Int_52 Int) (not_ConsiderAppearance_end_time_Int_53 Int)) (=> (and (set.member (tuple not_ConsiderAppearance_start_time_Int_52 not_ConsiderAppearance_end_time_Int_53) not_ConsiderAppearance) (set.member (tuple ConsiderAppearance_time_Int_51) ConsiderAppearance)) (not (and (<= ConsiderAppearance_time_Int_51 not_ConsiderAppearance_end_time_Int_53) (<= not_ConsiderAppearance_start_time_Int_52 ConsiderAppearance_time_Int_51))))) (and (forall ((AssignLiability_time_Int_48 Int) (not_AssignLiability_start_time_Int_49 Int) (not_AssignLiability_end_time_Int_50 Int)) (=> (and (set.member (tuple not_AssignLiability_start_time_Int_49 not_AssignLiability_end_time_Int_50) not_AssignLiability) (set.member (tuple AssignLiability_time_Int_48) AssignLiability)) (not (and (<= AssignLiability_time_Int_48 not_AssignLiability_end_time_Int_50) (<= not_AssignLiability_start_time_Int_49 AssignLiability_time_Int_48))))) (and (forall ((AssignToRobot_time_Int_45 Int) (not_AssignToRobot_start_time_Int_46 Int) (not_AssignToRobot_end_time_Int_47 Int)) (=> (and (set.member (tuple not_AssignToRobot_start_time_Int_46 not_AssignToRobot_end_time_Int_47) not_AssignToRobot) (set.member (tuple AssignToRobot_time_Int_45) AssignToRobot)) (not (and (<= AssignToRobot_time_Int_45 not_AssignToRobot_end_time_Int_47) (<= not_AssignToRobot_start_time_Int_46 AssignToRobot_time_Int_45))))) (and (forall ((PreparingRobot_time_Int_42 Int) (not_PreparingRobot_start_time_Int_43 Int) (not_PreparingRobot_end_time_Int_44 Int)) (=> (and (set.member (tuple not_PreparingRobot_start_time_Int_43 not_PreparingRobot_end_time_Int_44) not_PreparingRobot) (set.member (tuple PreparingRobot_time_Int_42) PreparingRobot)) (not (and (<= PreparingRobot_time_Int_42 not_PreparingRobot_end_time_Int_44) (<= not_PreparingRobot_start_time_Int_43 PreparingRobot_time_Int_42))))) (and (forall ((IncreaseSpeed_time_Int_39 Int) (not_IncreaseSpeed_start_time_Int_40 Int) (not_IncreaseSpeed_end_time_Int_41 Int)) (=> (and (set.member (tuple not_IncreaseSpeed_start_time_Int_40 not_IncreaseSpeed_end_time_Int_41) not_IncreaseSpeed) (set.member (tuple IncreaseSpeed_time_Int_39) IncreaseSpeed)) (not (and (<= IncreaseSpeed_time_Int_39 not_IncreaseSpeed_end_time_Int_41) (<= not_IncreaseSpeed_start_time_Int_40 IncreaseSpeed_time_Int_39))))) (and (forall ((MoveAtSafeSpeed_time_Int_36 Int) (not_MoveAtSafeSpeed_start_time_Int_37 Int) (not_MoveAtSafeSpeed_end_time_Int_38 Int)) (=> (and (set.member (tuple not_MoveAtSafeSpeed_start_time_Int_37 not_MoveAtSafeSpeed_end_time_Int_38) not_MoveAtSafeSpeed) (set.member (tuple MoveAtSafeSpeed_time_Int_36) MoveAtSafeSpeed)) (not (and (<= MoveAtSafeSpeed_time_Int_36 not_MoveAtSafeSpeed_end_time_Int_38) (<= not_MoveAtSafeSpeed_start_time_Int_37 MoveAtSafeSpeed_time_Int_36))))) (and (forall ((AskPermission_time_Int_33 Int) (not_AskPermission_start_time_Int_34 Int) (not_AskPermission_end_time_Int_35 Int)) (=> (and (set.member (tuple not_AskPermission_start_time_Int_34 not_AskPermission_end_time_Int_35) not_AskPermission) (set.member (tuple AskPermission_time_Int_33) AskPermission)) (not (and (<= AskPermission_time_Int_33 not_AskPermission_end_time_Int_35) (<= not_AskPermission_start_time_Int_34 AskPermission_time_Int_33))))) (and (forall ((HumanSaysStop_time_Int_30 Int) (not_HumanSaysStop_start_time_Int_31 Int) (not_HumanSaysStop_end_time_Int_32 Int)) (=> (and (set.member (tuple not_HumanSaysStop_start_time_Int_31 not_HumanSaysStop_end_time_Int_32) not_HumanSaysStop) (set.member (tuple HumanSaysStop_time_Int_30) HumanSaysStop)) (not (and (<= HumanSaysStop_time_Int_30 not_HumanSaysStop_end_time_Int_32) (<= not_HumanSaysStop_start_time_Int_31 HumanSaysStop_time_Int_30))))) (and (forall ((InformHuman_time_Int_27 Int) (not_InformHuman_start_time_Int_28 Int) (not_InformHuman_end_time_Int_29 Int)) (=> (and (set.member (tuple not_InformHuman_start_time_Int_28 not_InformHuman_end_time_Int_29) not_InformHuman) (set.member (tuple InformHuman_time_Int_27) InformHuman)) (not (and (<= InformHuman_time_Int_27 not_InformHuman_end_time_Int_29) (<= not_InformHuman_start_time_Int_28 InformHuman_time_Int_27))))) (and (forall ((TrackHumanLocation_time_Int_24 Int) (not_TrackHumanLocation_start_time_Int_25 Int) (not_TrackHumanLocation_end_time_Int_26 Int)) (=> (and (set.member (tuple not_TrackHumanLocation_start_time_Int_25 not_TrackHumanLocation_end_time_Int_26) not_TrackHumanLocation) (set.member (tuple TrackHumanLocation_time_Int_24) TrackHumanLocation)) (not (and (<= TrackHumanLocation_time_Int_24 not_TrackHumanLocation_end_time_Int_26) (<= not_TrackHumanLocation_start_time_Int_25 TrackHumanLocation_time_Int_24))))) (and (forall ((AccountHumanRandomness_time_Int_21 Int) (not_AccountHumanRandomness_start_time_Int_22 Int) (not_AccountHumanRandomness_end_time_Int_23 Int)) (=> (and (set.member (tuple not_AccountHumanRandomness_start_time_Int_22 not_AccountHumanRandomness_end_time_Int_23) not_AccountHumanRandomness) (set.member (tuple AccountHumanRandomness_time_Int_21) AccountHumanRandomness)) (not (and (<= AccountHumanRandomness_time_Int_21 not_AccountHumanRandomness_end_time_Int_23) (<= not_AccountHumanRandomness_start_time_Int_22 AccountHumanRandomness_time_Int_21))))) (and (forall ((InquireSafety_time_Int_18 Int) (not_InquireSafety_start_time_Int_19 Int) (not_InquireSafety_end_time_Int_20 Int)) (=> (and (set.member (tuple not_InquireSafety_start_time_Int_19 not_InquireSafety_end_time_Int_20) not_InquireSafety) (set.member (tuple InquireSafety_time_Int_18) InquireSafety)) (not (and (<= InquireSafety_time_Int_18 not_InquireSafety_end_time_Int_20) (<= not_InquireSafety_start_time_Int_19 InquireSafety_time_Int_18))))) (and (forall ((AdjustRoute_time_Int_15 Int) (not_AdjustRoute_start_time_Int_16 Int) (not_AdjustRoute_end_time_Int_17 Int)) (=> (and (set.member (tuple not_AdjustRoute_start_time_Int_16 not_AdjustRoute_end_time_Int_17) not_AdjustRoute) (set.member (tuple AdjustRoute_time_Int_15) AdjustRoute)) (not (and (<= AdjustRoute_time_Int_15 not_AdjustRoute_end_time_Int_17) (<= not_AdjustRoute_start_time_Int_16 AdjustRoute_time_Int_15))))) (and (forall ((AvoidBumping_time_Int_12 Int) (not_AvoidBumping_start_time_Int_13 Int) (not_AvoidBumping_end_time_Int_14 Int)) (=> (and (set.member (tuple not_AvoidBumping_start_time_Int_13 not_AvoidBumping_end_time_Int_14) not_AvoidBumping) (set.member (tuple AvoidBumping_time_Int_12) AvoidBumping)) (not (and (<= AvoidBumping_time_Int_12 not_AvoidBumping_end_time_Int_14) (<= not_AvoidBumping_start_time_Int_13 AvoidBumping_time_Int_12))))) (and (forall ((RobotStopAction_time_Int_9 Int) (not_RobotStopAction_start_time_Int_10 Int) (not_RobotStopAction_end_time_Int_11 Int)) (=> (and (set.member (tuple not_RobotStopAction_start_time_Int_10 not_RobotStopAction_end_time_Int_11) not_RobotStopAction) (set.member (tuple RobotStopAction_time_Int_9) RobotStopAction)) (not (and (<= RobotStopAction_time_Int_9 not_RobotStopAction_end_time_Int_11) (<= not_RobotStopAction_start_time_Int_10 RobotStopAction_time_Int_9))))) (and (forall ((RobotContinueTask_time_Int_6 Int) (not_RobotContinueTask_start_time_Int_7 Int) (not_RobotContinueTask_end_time_Int_8 Int)) (=> (and (set.member (tuple not_RobotContinueTask_start_time_Int_7 not_RobotContinueTask_end_time_Int_8) not_RobotContinueTask) (set.member (tuple RobotContinueTask_time_Int_6) RobotContinueTask)) (not (and (<= RobotContinueTask_time_Int_6 not_RobotContinueTask_end_time_Int_8) (<= not_RobotContinueTask_start_time_Int_7 RobotContinueTask_time_Int_6))))) (and (forall ((RobotWorking_time_Int_3 Int) (not_RobotWorking_start_time_Int_4 Int) (not_RobotWorking_end_time_Int_5 Int)) (=> (and (set.member (tuple not_RobotWorking_start_time_Int_4 not_RobotWorking_end_time_Int_5) not_RobotWorking) (set.member (tuple RobotWorking_time_Int_3) RobotWorking)) (not (and (<= RobotWorking_time_Int_3 not_RobotWorking_end_time_Int_5) (<= not_RobotWorking_start_time_Int_4 RobotWorking_time_Int_3))))) (forall ((RobotMoving_time_Int_0 Int) (not_RobotMoving_start_time_Int_1 Int) (not_RobotMoving_end_time_Int_2 Int)) (=> (and (set.member (tuple not_RobotMoving_start_time_Int_1 not_RobotMoving_end_time_Int_2) not_RobotMoving) (set.member (tuple RobotMoving_time_Int_0) RobotMoving)) (not (and (<= RobotMoving_time_Int_0 not_RobotMoving_end_time_Int_2) (<= not_RobotMoving_start_time_Int_1 RobotMoving_time_Int_0))))))))))))))))))))))))))) (set.forall ((tuple_423 (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool))) (rel.product Measure Measure) (=> (= ((_ tuple.select 0) tuple_423) ((_ tuple.select 14) tuple_423)) (and (= ((_ tuple.select 13) tuple_423) ((_ tuple.select 27) tuple_423)) (and (= ((_ tuple.select 12) tuple_423) ((_ tuple.select 26) tuple_423)) (and (= ((_ tuple.select 11) tuple_423) ((_ tuple.select 25) tuple_423)) (and (= ((_ tuple.select 10) tuple_423) ((_ tuple.select 24) tuple_423)) (and (= ((_ tuple.select 9) tuple_423) ((_ tuple.select 23) tuple_423)) (and (= ((_ tuple.select 8) tuple_423) ((_ tuple.select 22) tuple_423)) (and (= ((_ tuple.select 7) tuple_423) ((_ tuple.select 21) tuple_423)) (and (= ((_ tuple.select 6) tuple_423) ((_ tuple.select 20) tuple_423)) (and (= ((_ tuple.select 5) tuple_423) ((_ tuple.select 19) tuple_423)) (and (= ((_ tuple.select 4) tuple_423) ((_ tuple.select 18) tuple_423)) (and (= ((_ tuple.select 3) tuple_423) ((_ tuple.select 17) tuple_423)) (and (= ((_ tuple.select 2) tuple_423) ((_ tuple.select 16) tuple_423)) (and (= ((_ tuple.select 1) tuple_423) ((_ tuple.select 15) tuple_423)) (= ((_ tuple.select 0) tuple_423) ((_ tuple.select 14) tuple_423)))))))))))))))))))
(assert (=> (set.exists ((tuple_308 (Tuple Int))) RobotMoving true) (and (set.exists ((tuple_311 (Tuple Int))) RobotMoving (set.forall ((tuple_312 (Tuple Int))) RobotMoving (<= ((_ tuple.select 0) tuple_312) ((_ tuple.select 0) tuple_311)))) (set.exists ((tuple_309 (Tuple Int))) RobotMoving (set.forall ((tuple_310 (Tuple Int))) RobotMoving (>= ((_ tuple.select 0) tuple_310) ((_ tuple.select 0) tuple_309)))))))
(assert (=> (set.exists ((tuple_313 (Tuple Int))) RobotWorking true) (and (set.exists ((tuple_316 (Tuple Int))) RobotWorking (set.forall ((tuple_317 (Tuple Int))) RobotWorking (<= ((_ tuple.select 0) tuple_317) ((_ tuple.select 0) tuple_316)))) (set.exists ((tuple_314 (Tuple Int))) RobotWorking (set.forall ((tuple_315 (Tuple Int))) RobotWorking (>= ((_ tuple.select 0) tuple_315) ((_ tuple.select 0) tuple_314)))))))
(assert (=> (set.exists ((tuple_318 (Tuple Int))) RobotContinueTask true) (and (set.exists ((tuple_321 (Tuple Int))) RobotContinueTask (set.forall ((tuple_322 (Tuple Int))) RobotContinueTask (<= ((_ tuple.select 0) tuple_322) ((_ tuple.select 0) tuple_321)))) (set.exists ((tuple_319 (Tuple Int))) RobotContinueTask (set.forall ((tuple_320 (Tuple Int))) RobotContinueTask (>= ((_ tuple.select 0) tuple_320) ((_ tuple.select 0) tuple_319)))))))
(assert (=> (set.exists ((tuple_323 (Tuple Int))) RobotStopAction true) (and (set.exists ((tuple_326 (Tuple Int))) RobotStopAction (set.forall ((tuple_327 (Tuple Int))) RobotStopAction (<= ((_ tuple.select 0) tuple_327) ((_ tuple.select 0) tuple_326)))) (set.exists ((tuple_324 (Tuple Int))) RobotStopAction (set.forall ((tuple_325 (Tuple Int))) RobotStopAction (>= ((_ tuple.select 0) tuple_325) ((_ tuple.select 0) tuple_324)))))))
(assert (=> (set.exists ((tuple_328 (Tuple Int))) AvoidBumping true) (and (set.exists ((tuple_331 (Tuple Int))) AvoidBumping (set.forall ((tuple_332 (Tuple Int))) AvoidBumping (<= ((_ tuple.select 0) tuple_332) ((_ tuple.select 0) tuple_331)))) (set.exists ((tuple_329 (Tuple Int))) AvoidBumping (set.forall ((tuple_330 (Tuple Int))) AvoidBumping (>= ((_ tuple.select 0) tuple_330) ((_ tuple.select 0) tuple_329)))))))
(assert (=> (set.exists ((tuple_333 (Tuple Int))) AdjustRoute true) (and (set.exists ((tuple_336 (Tuple Int))) AdjustRoute (set.forall ((tuple_337 (Tuple Int))) AdjustRoute (<= ((_ tuple.select 0) tuple_337) ((_ tuple.select 0) tuple_336)))) (set.exists ((tuple_334 (Tuple Int))) AdjustRoute (set.forall ((tuple_335 (Tuple Int))) AdjustRoute (>= ((_ tuple.select 0) tuple_335) ((_ tuple.select 0) tuple_334)))))))
(assert (=> (set.exists ((tuple_338 (Tuple Int))) InquireSafety true) (and (set.exists ((tuple_341 (Tuple Int))) InquireSafety (set.forall ((tuple_342 (Tuple Int))) InquireSafety (<= ((_ tuple.select 0) tuple_342) ((_ tuple.select 0) tuple_341)))) (set.exists ((tuple_339 (Tuple Int))) InquireSafety (set.forall ((tuple_340 (Tuple Int))) InquireSafety (>= ((_ tuple.select 0) tuple_340) ((_ tuple.select 0) tuple_339)))))))
(assert (=> (set.exists ((tuple_343 (Tuple Int))) AccountHumanRandomness true) (and (set.exists ((tuple_346 (Tuple Int))) AccountHumanRandomness (set.forall ((tuple_347 (Tuple Int))) AccountHumanRandomness (<= ((_ tuple.select 0) tuple_347) ((_ tuple.select 0) tuple_346)))) (set.exists ((tuple_344 (Tuple Int))) AccountHumanRandomness (set.forall ((tuple_345 (Tuple Int))) AccountHumanRandomness (>= ((_ tuple.select 0) tuple_345) ((_ tuple.select 0) tuple_344)))))))
(assert (=> (set.exists ((tuple_348 (Tuple Int))) TrackHumanLocation true) (and (set.exists ((tuple_351 (Tuple Int))) TrackHumanLocation (set.forall ((tuple_352 (Tuple Int))) TrackHumanLocation (<= ((_ tuple.select 0) tuple_352) ((_ tuple.select 0) tuple_351)))) (set.exists ((tuple_349 (Tuple Int))) TrackHumanLocation (set.forall ((tuple_350 (Tuple Int))) TrackHumanLocation (>= ((_ tuple.select 0) tuple_350) ((_ tuple.select 0) tuple_349)))))))
(assert (=> (set.exists ((tuple_353 (Tuple Int))) InformHuman true) (and (set.exists ((tuple_356 (Tuple Int))) InformHuman (set.forall ((tuple_357 (Tuple Int))) InformHuman (<= ((_ tuple.select 0) tuple_357) ((_ tuple.select 0) tuple_356)))) (set.exists ((tuple_354 (Tuple Int))) InformHuman (set.forall ((tuple_355 (Tuple Int))) InformHuman (>= ((_ tuple.select 0) tuple_355) ((_ tuple.select 0) tuple_354)))))))
(assert (=> (set.exists ((tuple_358 (Tuple Int))) HumanSaysStop true) (and (set.exists ((tuple_361 (Tuple Int))) HumanSaysStop (set.forall ((tuple_362 (Tuple Int))) HumanSaysStop (<= ((_ tuple.select 0) tuple_362) ((_ tuple.select 0) tuple_361)))) (set.exists ((tuple_359 (Tuple Int))) HumanSaysStop (set.forall ((tuple_360 (Tuple Int))) HumanSaysStop (>= ((_ tuple.select 0) tuple_360) ((_ tuple.select 0) tuple_359)))))))
(assert (=> (set.exists ((tuple_363 (Tuple Int))) AskPermission true) (and (set.exists ((tuple_366 (Tuple Int))) AskPermission (set.forall ((tuple_367 (Tuple Int))) AskPermission (<= ((_ tuple.select 0) tuple_367) ((_ tuple.select 0) tuple_366)))) (set.exists ((tuple_364 (Tuple Int))) AskPermission (set.forall ((tuple_365 (Tuple Int))) AskPermission (>= ((_ tuple.select 0) tuple_365) ((_ tuple.select 0) tuple_364)))))))
(assert (=> (set.exists ((tuple_368 (Tuple Int))) MoveAtSafeSpeed true) (and (set.exists ((tuple_371 (Tuple Int))) MoveAtSafeSpeed (set.forall ((tuple_372 (Tuple Int))) MoveAtSafeSpeed (<= ((_ tuple.select 0) tuple_372) ((_ tuple.select 0) tuple_371)))) (set.exists ((tuple_369 (Tuple Int))) MoveAtSafeSpeed (set.forall ((tuple_370 (Tuple Int))) MoveAtSafeSpeed (>= ((_ tuple.select 0) tuple_370) ((_ tuple.select 0) tuple_369)))))))
(assert (=> (set.exists ((tuple_373 (Tuple Int))) IncreaseSpeed true) (and (set.exists ((tuple_376 (Tuple Int))) IncreaseSpeed (set.forall ((tuple_377 (Tuple Int))) IncreaseSpeed (<= ((_ tuple.select 0) tuple_377) ((_ tuple.select 0) tuple_376)))) (set.exists ((tuple_374 (Tuple Int))) IncreaseSpeed (set.forall ((tuple_375 (Tuple Int))) IncreaseSpeed (>= ((_ tuple.select 0) tuple_375) ((_ tuple.select 0) tuple_374)))))))
(assert (=> (set.exists ((tuple_378 (Tuple Int))) PreparingRobot true) (and (set.exists ((tuple_381 (Tuple Int))) PreparingRobot (set.forall ((tuple_382 (Tuple Int))) PreparingRobot (<= ((_ tuple.select 0) tuple_382) ((_ tuple.select 0) tuple_381)))) (set.exists ((tuple_379 (Tuple Int))) PreparingRobot (set.forall ((tuple_380 (Tuple Int))) PreparingRobot (>= ((_ tuple.select 0) tuple_380) ((_ tuple.select 0) tuple_379)))))))
(assert (=> (set.exists ((tuple_383 (Tuple Int))) AssignToRobot true) (and (set.exists ((tuple_386 (Tuple Int))) AssignToRobot (set.forall ((tuple_387 (Tuple Int))) AssignToRobot (<= ((_ tuple.select 0) tuple_387) ((_ tuple.select 0) tuple_386)))) (set.exists ((tuple_384 (Tuple Int))) AssignToRobot (set.forall ((tuple_385 (Tuple Int))) AssignToRobot (>= ((_ tuple.select 0) tuple_385) ((_ tuple.select 0) tuple_384)))))))
(assert (=> (set.exists ((tuple_388 (Tuple Int))) AssignLiability true) (and (set.exists ((tuple_391 (Tuple Int))) AssignLiability (set.forall ((tuple_392 (Tuple Int))) AssignLiability (<= ((_ tuple.select 0) tuple_392) ((_ tuple.select 0) tuple_391)))) (set.exists ((tuple_389 (Tuple Int))) AssignLiability (set.forall ((tuple_390 (Tuple Int))) AssignLiability (>= ((_ tuple.select 0) tuple_390) ((_ tuple.select 0) tuple_389)))))))
(assert (=> (set.exists ((tuple_393 (Tuple Int))) ConsiderAppearance true) (and (set.exists ((tuple_396 (Tuple Int))) ConsiderAppearance (set.forall ((tuple_397 (Tuple Int))) ConsiderAppearance (<= ((_ tuple.select 0) tuple_397) ((_ tuple.select 0) tuple_396)))) (set.exists ((tuple_394 (Tuple Int))) ConsiderAppearance (set.forall ((tuple_395 (Tuple Int))) ConsiderAppearance (>= ((_ tuple.select 0) tuple_395) ((_ tuple.select 0) tuple_394)))))))
(assert (=> (set.exists ((tuple_398 (Tuple Int))) ReportIncident true) (and (set.exists ((tuple_401 (Tuple Int))) ReportIncident (set.forall ((tuple_402 (Tuple Int))) ReportIncident (<= ((_ tuple.select 0) tuple_402) ((_ tuple.select 0) tuple_401)))) (set.exists ((tuple_399 (Tuple Int))) ReportIncident (set.forall ((tuple_400 (Tuple Int))) ReportIncident (>= ((_ tuple.select 0) tuple_400) ((_ tuple.select 0) tuple_399)))))))
(assert (=> (set.exists ((tuple_403 (Tuple Int))) MinimizeCobotCollaboration true) (and (set.exists ((tuple_406 (Tuple Int))) MinimizeCobotCollaboration (set.forall ((tuple_407 (Tuple Int))) MinimizeCobotCollaboration (<= ((_ tuple.select 0) tuple_407) ((_ tuple.select 0) tuple_406)))) (set.exists ((tuple_404 (Tuple Int))) MinimizeCobotCollaboration (set.forall ((tuple_405 (Tuple Int))) MinimizeCobotCollaboration (>= ((_ tuple.select 0) tuple_405) ((_ tuple.select 0) tuple_404)))))))
(assert (=> (set.exists ((tuple_408 (Tuple Int))) PrioritizeHumans true) (and (set.exists ((tuple_411 (Tuple Int))) PrioritizeHumans (set.forall ((tuple_412 (Tuple Int))) PrioritizeHumans (<= ((_ tuple.select 0) tuple_412) ((_ tuple.select 0) tuple_411)))) (set.exists ((tuple_409 (Tuple Int))) PrioritizeHumans (set.forall ((tuple_410 (Tuple Int))) PrioritizeHumans (>= ((_ tuple.select 0) tuple_410) ((_ tuple.select 0) tuple_409)))))))
(assert (=> (set.exists ((tuple_413 (Tuple Int))) ActionHumanRandom true) (and (set.exists ((tuple_416 (Tuple Int))) ActionHumanRandom (set.forall ((tuple_417 (Tuple Int))) ActionHumanRandom (<= ((_ tuple.select 0) tuple_417) ((_ tuple.select 0) tuple_416)))) (set.exists ((tuple_414 (Tuple Int))) ActionHumanRandom (set.forall ((tuple_415 (Tuple Int))) ActionHumanRandom (>= ((_ tuple.select 0) tuple_415) ((_ tuple.select 0) tuple_414)))))))
(assert (=> (set.exists ((tuple_418 (Tuple Int))) MoveAwayFromHuman true) (and (set.exists ((tuple_421 (Tuple Int))) MoveAwayFromHuman (set.forall ((tuple_422 (Tuple Int))) MoveAwayFromHuman (<= ((_ tuple.select 0) tuple_422) ((_ tuple.select 0) tuple_421)))) (set.exists ((tuple_419 (Tuple Int))) MoveAwayFromHuman (set.forall ((tuple_420 (Tuple Int))) MoveAwayFromHuman (>= ((_ tuple.select 0) tuple_420) ((_ tuple.select 0) tuple_419)))))))
(assert (set.forall ((tuple_1 (Tuple Int))) time (>= ((_ tuple.select 0) tuple_1) 0)))
(assert (set.forall ((tuple_2 (Tuple Int))) risk (and (<= ((_ tuple.select 0) tuple_2) 2) (>= ((_ tuple.select 0) tuple_2) 0))))
(assert (set.forall ((tuple_3 (Tuple Int))) efficiency (and (<= ((_ tuple.select 0) tuple_3) 2) (>= ((_ tuple.select 0) tuple_3) 0))))
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
(assert (and (set.forall ((tuple_428 (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool))) Measure (set.exists ((tuple_429 (Tuple Int))) efficiency (= ((_ tuple.select 0) tuple_429) ((_ tuple.select 8) tuple_428)))) (and (set.forall ((tuple_426 (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool))) Measure (set.exists ((tuple_427 (Tuple Int))) risk (= ((_ tuple.select 0) tuple_427) ((_ tuple.select 7) tuple_426)))) (set.forall ((tuple_424 (Tuple Int Bool Bool Bool Bool Bool Bool Int Int Bool Bool Bool Bool Bool))) Measure (set.exists ((tuple_425 (Tuple Int))) time (= ((_ tuple.select 0) tuple_425) ((_ tuple.select 0) tuple_424)))))))
(check-sat)
