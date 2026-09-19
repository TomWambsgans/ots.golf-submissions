import Submissions.LowerGenerality3.Proof

namespace OptimalOTS.Challenge.LowerGenerality3

/-- Every admissible, secure algorithm under the paper limits needs at least one compression. -/
theorem candidate :
    AlgorithmVerificationLowerBound paperParams (1 / 2 ^ 128) 1 := by
  apply OptimalOTS.LowerGenerality3.paper_lowerBound_one
  norm_num

end OptimalOTS.Challenge.LowerGenerality3

/--
info: 'OptimalOTS.Challenge.LowerGenerality3.candidate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.Challenge.LowerGenerality3.candidate
