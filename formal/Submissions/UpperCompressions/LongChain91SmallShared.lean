import Submissions.UpperCompressions.LongChain91SmallMoments
import Submissions.UpperCompressions.LongChain91BudgetArithmetic
import Submissions.UpperCompressions.ProofBundle11

/-!
# Shared-clock small-budget core for the cost-91 construction

The stopped pair envelope and the authentication/post-sign clocks share one
physical query budget.  This module records the independent real and ENNReal
closure through the split `B <= 2^86 / 64`; it does not depend on the concrete
key-generation or final-game assembly.
-/

noncomputable section

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical BigOperators

namespace OptimalOTS.WeightedConstruction.LongChain91SmallShared

open LongChain91SmallMoments
open WeightedRealExecution

set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

def smallRate : ℝ :=
  LongChain91BudgetArithmetic.C * (65 / 64) * (967 / 1000) *
    LongChain91BudgetArithmetic.kappa

theorem smallRate_nonneg : 0 ≤ smallRate := by
  unfold smallRate
  exact mul_nonneg
    (mul_nonneg (mul_nonneg LongChain91BudgetArithmetic.C_nonneg
      (by norm_num)) (by norm_num))
    LongChain91BudgetArithmetic.kappa_pos.le

theorem authRate_le_smallRate : kappa / 2 ≤ smallRate := by
  change LongChain91BudgetArithmetic.kappa / 2 ≤ _
  unfold smallRate LongChain91BudgetArithmetic.C
  have hk := LongChain91BudgetArithmetic.kappa_pos.le
  nlinarith

theorem postRate_le_smallRate :
    LongChain91BudgetArithmetic.postRate ≤ smallRate := by
  unfold smallRate LongChain91BudgetArithmetic.postRate
    LongChain91BudgetArithmetic.C
  have hk := LongChain91BudgetArithmetic.kappa_pos.le
  nlinarith

/-- The stopped pair process is charged at the common rate used by the
authentication and post-sign clocks.  Its covariance allowance remains
explicit for the final bad-event budget. -/
theorem small_payoff_actual {α : Type}
    (oa : OracleComp Spec α) (B : ℕ) (hB : CostAtMost oa B)
    (hBN : (B : ℝ) ≤ (2 : ℝ)^86 / 64)
    (c : Cache) (hf : ∀ q : Query, q.1 = 342 → c q = none) :
    realEval (run oa c) (fun out =>
      C * pairEnvelope out.2 +
        smallRate * ((B : ℝ) - (queryCount out.2 : ℝ))) ≤
      smallRate * (B : ℝ) + kappa * (B : ℝ) / 1000 := by
  have h := sharp_stopped_payoff_actual oa B hB
    (budget64_le_budget10 B hBN) c hf smallRate
  have hfactor := factor_65_of_budget64 B hBN
  have hcm :
      C * mean * (1 + ((B : ℝ) - 1) / (2 : ℝ)^86) ≤ smallRate := by
    have h1 : C * mean * (1 + ((B : ℝ) - 1) / (2 : ℝ)^86) ≤
        C * mean * (65 / 64) := mul_le_mul_of_nonneg_left hfactor
      (mul_nonneg LongChain91BudgetArithmetic.C_nonneg mean_nonneg)
    have h2 : C * (65 / 64) * mean ≤
        C * (65 / 64) * ((967 / 1000) * kappa) :=
      mul_le_mul_of_nonneg_left
      LongChain91Security.securityWeights_mean
      (mul_nonneg LongChain91BudgetArithmetic.C_nonneg (by norm_num))
    unfold smallRate
    nlinarith
  rw [max_eq_left hcm] at h
  simpa only [mul_comm (B : ℝ) smallRate] using h

theorem actual_small_shared_real {α : Type}
    (oa : OracleComp Spec α) (B : ℕ)
    (hB : CostAtMost oa B) (hBN : (B : ℝ) ≤ (2 : ℝ)^86 / 64)
    (c : Cache) (hf : ∀ q : Query, q.1 = 342 → c q = none)
    (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hclock : realEval (run oa c)
        (fun out => (queryCount out.2 : ℝ)) + a + t ≤ B) :
    C * realEval (run oa c) (fun out => pairEnvelope out.2) +
        (kappa / 2) * a + LongChain91BudgetArithmetic.postRate * t +
          kappa * (B : ℝ) / 1000 ≤
      (6235189 / 6272000) * kappa * (B : ℝ) := by
  have h := small_payoff_actual oa B hB hBN c hf
  change realEval (run oa c) (fun out =>
      C * pairEnvelope out.2 +
        smallRate * ((B : ℝ) - (queryCount out.2 : ℝ))) ≤ _ at h
  rw [realEval_add, realEval_mul, realEval_mul, realEval_sub,
    realEval_const] at h
  have hshare := mul_le_mul_of_nonneg_left hclock smallRate_nonneg
  have hauth := mul_le_mul_of_nonneg_right authRate_le_smallRate ha
  have hpost := mul_le_mul_of_nonneg_right postRate_le_smallRate ht
  have hid : smallRate * (B : ℝ) + 2 * (kappa * (B : ℝ) / 1000) =
      (6235189 / 6272000) * kappa * (B : ℝ) := by
    simpa only [smallRate] using
      LongChain91BudgetArithmetic.small_coefficient_identity (B : ℝ)
  nlinarith

theorem actual_small_shared_ennreal {α : Type}
    (oa : OracleComp Spec α) (B : ℕ)
    (hB : CostAtMost oa B) (hBN : (B : ℝ) ≤ (2 : ℝ)^86 / 64)
    (c : Cache) (hf : ∀ q : Query, q.1 = 342 → c q = none)
    (a t : ℝ≥0∞)
    (hclock : E (run oa c) (fun out => (queryCount out.2 : ℝ≥0∞)) + a + t ≤ B) :
    ENNReal.ofReal C * E (run oa c)
        (fun out => ENNReal.ofReal (pairEnvelope out.2)) +
      ENNReal.ofReal (kappa / 2) * a +
        ENNReal.ofReal LongChain91BudgetArithmetic.postRate * t +
      ENNReal.ofReal (kappa * (B : ℝ) / 1000) ≤
        ENNReal.ofReal ((6235189 / 6272000) * kappa * (B : ℝ)) := by
  let execution := run oa c
  let Q := realEval execution (fun out => (queryCount out.2 : ℝ))
  let P := realEval execution (fun out => pairEnvelope out.2)
  have hQ0 : 0 ≤ Q := realEval_nonneg execution _
    (fun out => Nat.cast_nonneg _)
  have hP0 : 0 ≤ P := realEval_nonneg execution _
    (fun out => pairEnvelope_nonneg out.2)
  have hQ : E execution (fun out => (queryCount out.2 : ℝ≥0∞)) =
      ENNReal.ofReal Q := by
    simpa only [ENNReal.ofReal_natCast] using
      (ofReal_realEval execution (fun out => (queryCount out.2 : ℝ))
        (fun out => Nat.cast_nonneg _)).symm
  have hP : E execution (fun out => ENNReal.ofReal (pairEnvelope out.2)) =
      ENNReal.ofReal P :=
    (ofReal_realEval execution (fun out => pairEnvelope out.2)
      (fun out => pairEnvelope_nonneg out.2)).symm
  change E execution _ + a + t ≤ B at hclock
  rw [hQ] at hclock
  have haB : a ≤ (B : ℝ≥0∞) :=
    (le_add_self.trans le_self_add).trans hclock
  have htB : t ≤ (B : ℝ≥0∞) := le_add_self.trans hclock
  have haTop : a ≠ ⊤ := ne_top_of_le_ne_top (by simp) haB
  have htTop : t ≠ ⊤ := ne_top_of_le_ne_top (by simp) htB
  have hsum : ENNReal.ofReal Q + a ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, haTop⟩
  have hc := ENNReal.toReal_mono
    (show (B : ℝ≥0∞) ≠ ⊤ by simp) hclock
  rw [ENNReal.toReal_add hsum htTop,
    ENNReal.toReal_add ENNReal.ofReal_ne_top haTop,
    ENNReal.toReal_ofReal hQ0, ENNReal.toReal_natCast] at hc
  have hr := actual_small_shared_real oa B hB hBN c hf
    a.toReal t.toReal ENNReal.toReal_nonneg ENNReal.toReal_nonneg hc
  have hk0 : 0 ≤ kappa / 2 := div_nonneg
    LongChain91BudgetArithmetic.kappa_pos.le (by norm_num)
  have htail : 0 ≤ kappa * (B : ℝ) / 1000 :=
    div_nonneg (mul_nonneg LongChain91BudgetArithmetic.kappa_pos.le
      (Nat.cast_nonneg B)) (by norm_num)
  have hCP : 0 ≤ C * P :=
    mul_nonneg LongChain91BudgetArithmetic.C_nonneg hP0
  have hka : 0 ≤ (kappa / 2) * a.toReal :=
    mul_nonneg hk0 ENNReal.toReal_nonneg
  have hpt : 0 ≤ LongChain91BudgetArithmetic.postRate * t.toReal :=
    mul_nonneg LongChain91BudgetArithmetic.postRate_nonneg
      ENNReal.toReal_nonneg
  have he := ENNReal.ofReal_le_ofReal hr
  change ENNReal.ofReal (C * P + (kappa / 2) * a.toReal +
      LongChain91BudgetArithmetic.postRate * t.toReal +
        kappa * (B : ℝ) / 1000) ≤ _ at he
  rw [ENNReal.ofReal_add (add_nonneg (add_nonneg hCP hka) hpt) htail,
    ENNReal.ofReal_add (add_nonneg hCP hka) hpt,
    ENNReal.ofReal_add hCP hka,
    ENNReal.ofReal_mul LongChain91BudgetArithmetic.C_nonneg,
    ENNReal.ofReal_mul hk0,
    ENNReal.ofReal_mul LongChain91BudgetArithmetic.postRate_nonneg,
    ENNReal.ofReal_toReal haTop, ENNReal.ofReal_toReal htTop] at he
  change ENNReal.ofReal C * E execution
      (fun out => ENNReal.ofReal (pairEnvelope out.2)) + _ + _ + _ ≤ _
  rw [hP]
  exact he

#print axioms small_payoff_actual
#print axioms actual_small_shared_real
#print axioms actual_small_shared_ennreal

end OptimalOTS.WeightedConstruction.LongChain91SmallShared
