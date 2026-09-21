import Submissions.UpperCompressions.LongChain91SecurityData
import Submissions.UpperCompressions.LongChain91CachedRow

/-!
# Exact budget arithmetic for the cost-91 long-chain proof

The execution modules feed this file nonnegative clocks and scalar payoff
bounds.  Everything below is deterministic real arithmetic: it records the
common drift rate, the post-sign rate, and the exact coefficients used by the
small- and large-budget endpoints.
-/

noncomputable section

namespace OptimalOTS.WeightedConstruction.LongChain91BudgetArithmetic

open scoped BigOperators

abbrev kappa : ℝ := Chain18Compact.kappa
abbrev securityWeights := LongChain91Security.securityWeights

/-- Common empirical-kernel envelope. -/
def C : ℝ := 99 / 98

/-- The reference mean plus its `1/100` empirical allowance. -/
def alpha : ℝ := (977 / 1000) * kappa

/-- Authentication followed by the completed-row excess payoff. -/
def postRate : ℝ := kappa / 2 + C * ((471 / 1000) * kappa)

theorem kappa_pos : 0 < kappa := by
  unfold kappa Chain18Compact.kappa
  positivity

theorem C_nonneg : 0 ≤ C := by norm_num [C]

theorem alpha_nonneg : 0 ≤ alpha := by
  unfold alpha
  exact mul_nonneg (by norm_num) kappa_pos.le

theorem postRate_nonneg : 0 ≤ postRate := by
  unfold postRate
  exact add_nonneg (div_nonneg kappa_pos.le (by norm_num))
    (mul_nonneg C_nonneg (mul_nonneg (by norm_num) kappa_pos.le))

/-- The certified `967/1000` mean leaves exactly the requested `1/100`
empirical margin inside `alpha`. -/
theorem mean_margin_le :
    securityWeights.mean + kappa / 100 ≤ alpha := by
  calc
    securityWeights.mean + kappa / 100 ≤
        (967 / 1000) * kappa + kappa / 100 :=
      add_le_add LongChain91Security.securityWeights_mean le_rfl
    _ = alpha := by
      unfold alpha
      ring

/-- Authentication alone is covered by the post-sign rate. -/
theorem authRate_le_postRate : kappa / 2 ≤ postRate := by
  unfold postRate C
  have hk := kappa_pos.le
  nlinarith

/-- The common `C * alpha` rate covers authentication alone. -/
theorem authRate_le_C_alpha : kappa / 2 ≤ C * alpha := by
  unfold C alpha
  have hk := kappa_pos.le
  nlinarith

/-- The same common rate covers the full post-sign continuation. -/
theorem postRate_le_C_alpha : postRate ≤ C * alpha := by
  unfold postRate C alpha
  have hk := kappa_pos.le
  nlinarith

/-- Exact coefficient left after the large-game clock allocation. -/
theorem large_coefficient_identity (K : ℝ) :
    C * alpha * K + C * (kappa * K / 1000) + kappa * K / 1000 =
      (2423 / 2450) * kappa * K := by
  unfold C alpha
  ring

/-- Scalar closure used by the large actual game.  Replay receives the
`alpha*q` drift allowance and a `1/1000` exception allowance; authentication
and post-sign work share the remaining clock. -/
theorem large_scalar_closure (K q a t R : ℝ)
    (_hq : 0 ≤ q) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hclock : q + a + t ≤ K)
    (hR : R ≤ alpha * q + kappa * K / 1000) :
    C * R + (kappa / 2) * a + postRate * t + kappa * K / 1000 ≤
      (2423 / 2450) * kappa * K := by
  have hCr := mul_le_mul_of_nonneg_left hR C_nonneg
  have hA := mul_le_mul_of_nonneg_right authRate_le_C_alpha ha
  have hT := mul_le_mul_of_nonneg_right postRate_le_C_alpha ht
  have hclock' := mul_le_mul_of_nonneg_left hclock
    (mul_nonneg C_nonneg alpha_nonneg)
  have he := large_coefficient_identity K
  nlinarith

/-- The exact coefficient produced by the small-game kernel envelope, its
`65/64` stopping factor, the certified mean, and two `1/1000` allowances. -/
theorem small_coefficient_identity (K : ℝ) :
    C * (65 / 64) * (967 / 1000) * kappa * K +
        2 * (kappa * K / 1000) =
      (6235189 / 6272000) * kappa * K := by
  unfold C
  ring

/-- Monotone form of the small coefficient identity. -/
theorem small_scalar_closure (K R : ℝ) (hK : 0 ≤ K)
    (hR : R ≤ (65 / 64) * securityWeights.mean * K) :
    C * R + 2 * (kappa * K / 1000) ≤
      (6235189 / 6272000) * kappa * K := by
  have hCr := mul_le_mul_of_nonneg_left hR C_nonneg
  have hfactor : 0 ≤ C * (65 / 64) * K := by
    exact mul_nonneg (mul_nonneg C_nonneg (by norm_num)) hK
  have hm := mul_le_mul_of_nonneg_left
    LongChain91Security.securityWeights_mean hfactor
  have he := small_coefficient_identity K
  nlinarith

theorem small_coefficient_lt_one :
    (6235189 : ℝ) / 6272000 < 1 := by norm_num

theorem large_coefficient_lt_one :
    (2423 : ℝ) / 2450 < 1 := by norm_num

theorem small_below_security (K : ℝ) (hK : 0 ≤ K) :
    (6235189 / 6272000) * kappa * K ≤ kappa * K := by
  have hk : 0 ≤ kappa * K := mul_nonneg kappa_pos.le hK
  nlinarith [small_coefficient_lt_one]

theorem large_below_security (K : ℝ) (hK : 0 ≤ K) :
    (2423 / 2450) * kappa * K ≤ kappa * K := by
  have hk : 0 ≤ kappa * K := mul_nonneg kappa_pos.le hK
  nlinarith [large_coefficient_lt_one]

#print axioms mean_margin_le
#print axioms authRate_le_postRate
#print axioms authRate_le_C_alpha
#print axioms postRate_le_C_alpha
#print axioms large_coefficient_identity
#print axioms large_scalar_closure
#print axioms small_coefficient_identity
#print axioms small_scalar_closure
#print axioms small_below_security
#print axioms large_below_security

end OptimalOTS.WeightedConstruction.LongChain91BudgetArithmetic
