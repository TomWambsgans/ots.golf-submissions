import Submissions.UpperCompressions.LongChain91BudgetArithmetic

/-!
# Actual-cache stopped moments for the chain-18 decoder

This module specializes the protected-cache score and pair-score martingales
to the concrete length-342 index domain.  The sharp stopped bound retains its
exact endpoint factor `1 + (B-1)/2^86`; two corollaries record what follows at
the accepted `2^86/10` threshold and at the stronger threshold needed for a
`65/64` endpoint factor.
-/

noncomputable section

namespace OptimalOTS.WeightedConstruction.LongChain91SmallMoments

open OracleSpec OracleComp OracleComp.EvalDist
open WeightedCacheCounts WeightedRow.Weights WeightedRealExecution
open scoped Classical BigOperators ENNReal

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

abbrev M := LongChain91Security.M
abbrev decode : BitVec hashBits → Option (Fin M) :=
  LongChain91Empirical.cacheDecode
abbrev securityWeights := LongChain91Security.securityWeights
abbrev mean : ℝ := securityWeights.mean
abbrev kappa : ℝ := LongChain91BudgetArithmetic.kappa
abbrev C : ℝ := LongChain91BudgetArithmetic.C

def queryCount (c : hashSpec.QueryCache) : ℕ :=
  (seen WideDomains.indexDomain c).card

def counts (c : hashSpec.QueryCache) : Fin M → ℕ :=
  classCounts WideDomains.indexDomain c decode

def score (c : hashSpec.QueryCache) : ℝ :=
  securityWeights.score (counts c)

def pairs (c : hashSpec.QueryCache) : ℝ :=
  securityWeights.pairScore (counts c)

def pairEnvelope (c : hashSpec.QueryCache) : ℝ :=
  score c + 2 * pairs c / (2 : ℝ)^86

theorem mean_nonneg : 0 ≤ mean := by
  unfold mean WeightedRow.Weights.mean
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (securityWeights.p_pos i).le (securityWeights.g_nonneg i)

theorem mean_le_kappa : mean ≤ kappa := by
  calc
    mean ≤ (967 / 1000) * kappa :=
      LongChain91Security.securityWeights_mean
    _ ≤ kappa := by
      have hk := LongChain91BudgetArithmetic.kappa_pos.le
      nlinarith

theorem score_nonneg (c : hashSpec.QueryCache) : 0 ≤ score c := by
  unfold score WeightedRow.Weights.score
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (Nat.cast_nonneg _) (securityWeights.g_nonneg i)

theorem pairs_nonneg (c : hashSpec.QueryCache) : 0 ≤ pairs c := by
  unfold pairs WeightedRow.Weights.pairScore
  exact Finset.sum_nonneg fun i _ => div_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (securityWeights.g_nonneg i))
    (securityWeights.p_pos i).le

theorem pairEnvelope_nonneg (c : hashSpec.QueryCache) :
    0 ≤ pairEnvelope c := by
  unfold pairEnvelope
  exact add_nonneg (score_nonneg c)
    (div_nonneg (mul_nonneg (by norm_num) (pairs_nonneg c)) (by positivity))

theorem scaledPairEnvelope_nonneg (c : hashSpec.QueryCache) :
    0 ≤ C * pairEnvelope c :=
  mul_nonneg LongChain91BudgetArithmetic.C_nonneg (pairEnvelope_nonneg c)

/-! ## Fresh index domain and exact stopped moments -/

theorem index_initial (c : hashSpec.QueryCache)
    (hf : ∀ q : Query, q.1 = 342 → c q = none) :
    queryCount c = 0 ∧ counts c = (fun _ => 0) := by
  have he := WideDomains.fresh_seen_empty c hf
  constructor
  · unfold queryCount
    rw [he, Finset.card_empty]
  · unfold counts classCounts
    rw [he]
    funext i
    simp [WeightedPublicCounts.counts]

/-- All three martingale moments for the real adaptive oracle execution. -/
theorem moments { α : Type } (oa : OracleComp Spec α) (B : ℕ)
    (hB : CostAtMost oa B) (c : hashSpec.QueryCache)
    (hf : ∀ q : Query, q.1 = 342 → c q = none) :
    let run := (simulateQ oracleImpl oa).run c
    realEval run
      (fun out => score out.2 - mean * (queryCount out.2 : ℝ)) = 0 ∧
    realEval run
      (fun out => pairs out.2 - (queryCount out.2 : ℝ) * score out.2 +
        mean * (queryCount out.2 : ℝ) *
          ((queryCount out.2 : ℝ) + 1) / 2) = 0 ∧
    realEval run
      (fun out => (score out.2 - mean * (queryCount out.2 : ℝ))^2) ≤
        (B : ℝ) *
          ((Chain18Compact.L : ℝ) * kappa / 2) * mean := by
  obtain ⟨hq, hk⟩ := index_initial c hf
  exact WeightedProtectedCache.stopped_moments securityWeights
    WideDomains.indexDomain decode LongChain91Empirical.cache_decoder_law
    ((Chain18Compact.L : ℝ) * kappa / 2)
    (by
      exact div_nonneg
        (mul_nonneg (Nat.cast_nonneg _)
          LongChain91BudgetArithmetic.kappa_pos.le) (by norm_num))
    LongChain91Security.referenceWeight_le oa B hB c hq hk

theorem realEval_congr_support { α : Type } (oa : ProbComp α)
    (f g : α → ℝ) (
      h : ∀ a ∈ support oa, f a = g a) :
    realEval oa f = realEval oa g :=
  le_antisymm
    (realEval_mono_of_support oa f g (fun a ha => (h a ha).le))
    (realEval_mono_of_support oa g f (fun a ha => (h a ha).symm.le))

theorem queryCount_le_budget_on_support { α : Type }
    (oa : OracleComp Spec α) (B : ℕ) (hB : CostAtMost oa B)
    (c : hashSpec.QueryCache)
    (hf : ∀ q : Query, q.1 = 342 → c q = none)
    (out : α × hashSpec.QueryCache)
    (hout : out ∈ support ((simulateQ oracleImpl oa).run c)) :
    queryCount out.2 ≤ B := by
  have h := WeightedProtectedCache.count_bound WideDomains.indexDomain
    oa B hB c out hout
  have hq := (index_initial c hf).1
  change queryCount out.2 ≤
    min WideDomains.indexDomain.card (queryCount c + B) at h
  rw [hq, zero_add] at h
  exact h.trans (min_le_right _ _)

/-! ## Sharp and rounded stopped payoffs -/

/-- The exact endpoint factor furnished by the generic stopped theorem.
Only the covariance term uses the `B ≤ 2^86/10` hypothesis. -/
theorem sharp_stopped_payoff_actual { α : Type }
    (oa : OracleComp Spec α) (B : ℕ) (hB : CostAtMost oa B)
    (hBN : (B : ℝ) ≤ (2 : ℝ)^86 / 10)
    (c : hashSpec.QueryCache)
    (hf : ∀ q : Query, q.1 = 342 → c q = none) (d : ℝ) :
    realEval ((simulateQ oracleImpl oa).run c) (fun out =>
      C * pairEnvelope out.2 +
        d * ((B : ℝ) - (queryCount out.2 : ℝ))) ≤
      (B : ℝ) * max d
        (C * mean * (1 + ((B : ℝ) - 1) / (2 : ℝ)^86)) +
          kappa * (B : ℝ) / 1000 := by
  let run := (simulateQ oracleImpl oa).run c
  let τ : α × hashSpec.QueryCache → ℝ := fun out =>
    min (queryCount out.2 : ℝ) (B : ℝ)
  have hτ (out) (ho : out ∈ support run) :
      τ out = (queryCount out.2 : ℝ) := by
    exact min_eq_left (by
      exact_mod_cast queryCount_le_budget_on_support oa B hB c hf out ho)
  obtain ⟨hm1, hm2, hmSq⟩ := moments oa B hB c hf
  have hm1' : realEval run (fun out => score out.2 - mean * τ out) = 0 := by
    rw [realEval_congr_support run _ _ (fun out ho => by rw [hτ out ho])]
    exact hm1
  have hm2' : realEval run (fun out =>
      pairs out.2 - τ out * score out.2 +
        mean * τ out * (τ out + 1) / 2) = 0 := by
    rw [realEval_congr_support run _ _ (fun out ho => by rw [hτ out ho])]
    exact hm2
  have hmSq' : realEval run
      (fun out => (score out.2 - mean * τ out)^2) ≤
        (B : ℝ) * ((Chain18Compact.L : ℝ) * kappa / 2) * mean := by
    rw [realEval_congr_support run _ _ (fun out ho => by rw [hτ out ho])]
    exact hmSq
  have hK : 0 ≤ (B : ℝ) := Nat.cast_nonneg B
  have hG : 0 ≤ (Chain18Compact.L : ℝ) * kappa / 2 :=
    div_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        LongChain91BudgetArithmetic.kappa_pos.le) (by norm_num)
  have hT : 0 < kappa * (2 : ℝ)^86 / 4096 := by
    exact div_pos
      (mul_pos LongChain91BudgetArithmetic.kappa_pos (by positivity))
      (by norm_num)
  have hgmax :
      (Chain18Compact.L : ℝ) * kappa / 2 ≤ (2 : ℝ)^20 * kappa / 2 := by
    norm_num [Chain18Compact.L]
  have hs := WeightedStopping.stopped_payoff
    (realEval run) (realEval_mono run) (realEval_const run 1)
    τ (fun out => score out.2) (fun out => pairs out.2)
    C mean d ((2 : ℝ)^86) (B : ℝ)
    ((B : ℝ) * ((Chain18Compact.L : ℝ) * kappa / 2) * mean)
    (kappa * (2 : ℝ)^86 / 4096)
    LongChain91BudgetArithmetic.C_nonneg mean_nonneg (by positivity) hK hT
    (fun out => le_min (Nat.cast_nonneg _) (Nat.cast_nonneg B))
    (fun out => min_le_right _ _) hm1' hm2' hmSq'
  have hc := WeightedStopping.mixed72_covariance
    C kappa (B : ℝ) ((Chain18Compact.L : ℝ) * kappa / 2) mean
    LongChain91BudgetArithmetic.C_nonneg
    (by norm_num [C, LongChain91BudgetArithmetic.C])
    LongChain91BudgetArithmetic.kappa_pos hK hG mean_nonneg hBN hgmax
    mean_le_kappa
  have h := hs.trans (add_le_add le_rfl hc)
  rw [realEval_congr_support run _ _ (fun out ho => by rw [hτ out ho])] at h
  simpa only [pairEnvelope] using h

/-- At the actual small-game threshold, the accepted generic theorem gives
the endpoint multiplier `11/10`. -/
theorem stopped_core_actual { α : Type }
    (oa : OracleComp Spec α) (B : ℕ) (hB : CostAtMost oa B)
    (hBN : (B : ℝ) ≤ (2 : ℝ)^86 / 10)
    (c : hashSpec.QueryCache)
    (hf : ∀ q : Query, q.1 = 342 → c q = none) :
    realEval ((simulateQ oracleImpl oa).run c)
        (fun out => C * pairEnvelope out.2) ≤
      (B : ℝ) * (11 * C * mean / 10) + kappa * (B : ℝ) / 1000 := by
  have h := sharp_stopped_payoff_actual oa B hB hBN c hf 0
  have hN : 0 < (2 : ℝ)^86 := by positivity
  have hratio : ((B : ℝ) - 1) / (2 : ℝ)^86 ≤ 1 / 10 :=
    (div_le_iff₀ hN).2 (by linarith)
  have hpre :
      C * mean * (1 + ((B : ℝ) - 1) / (2 : ℝ)^86) ≤
        11 * C * mean / 10 := by
    have hm := mul_le_mul_of_nonneg_left hratio
      (mul_nonneg LongChain91BudgetArithmetic.C_nonneg mean_nonneg)
    nlinarith
  have htarget : 0 ≤ 11 * C * mean / 10 := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num)
        LongChain91BudgetArithmetic.C_nonneg) mean_nonneg) (by norm_num)
  have hmax : max 0
      (C * mean * (1 + ((B : ℝ) - 1) / (2 : ℝ)^86)) ≤
        11 * C * mean / 10 := max_le htarget hpre
  have hb := mul_le_mul_of_nonneg_left hmax (Nat.cast_nonneg B)
  have h' : realEval ((simulateQ oracleImpl oa).run c)
      (fun out => C * pairEnvelope out.2) ≤
      (B : ℝ) * max 0
        (C * mean * (1 + ((B : ℝ) - 1) / (2 : ℝ)^86)) +
          kappa * (B : ℝ) / 1000 := by
    simpa only [zero_mul, add_zero] using h
  exact h'.trans (add_le_add hb le_rfl)

/-- If the exact endpoint factor is at most `65/64`, the same actual-cache
proof gives the desired core rate, with its covariance allowance explicit. -/
theorem stopped_core_65_of_factor { α : Type }
    (oa : OracleComp Spec α) (B : ℕ) (hB : CostAtMost oa B)
    (hBN : (B : ℝ) ≤ (2 : ℝ)^86 / 10)
    (hfactor : 1 + ((B : ℝ) - 1) / (2 : ℝ)^86 ≤ 65 / 64)
    (c : hashSpec.QueryCache)
    (hf : ∀ q : Query, q.1 = 342 → c q = none) :
    realEval ((simulateQ oracleImpl oa).run c)
        (fun out => C * pairEnvelope out.2) ≤
      (B : ℝ) * (C * (65 / 64) * mean) +
        kappa * (B : ℝ) / 1000 := by
  have h := sharp_stopped_payoff_actual oa B hB hBN c hf 0
  have hpre :
      C * mean * (1 + ((B : ℝ) - 1) / (2 : ℝ)^86) ≤
        C * (65 / 64) * mean := by
    have hm := mul_le_mul_of_nonneg_left hfactor
      (mul_nonneg LongChain91BudgetArithmetic.C_nonneg mean_nonneg)
    nlinarith
  have htarget : 0 ≤ C * (65 / 64) * mean := by
    exact mul_nonneg
      (mul_nonneg LongChain91BudgetArithmetic.C_nonneg (by norm_num)) mean_nonneg
  have hmax : max 0
      (C * mean * (1 + ((B : ℝ) - 1) / (2 : ℝ)^86)) ≤
        C * (65 / 64) * mean := max_le htarget hpre
  have hb := mul_le_mul_of_nonneg_left hmax (Nat.cast_nonneg B)
  have h' : realEval ((simulateQ oracleImpl oa).run c)
      (fun out => C * pairEnvelope out.2) ≤
      (B : ℝ) * max 0
        (C * mean * (1 + ((B : ℝ) - 1) / (2 : ℝ)^86)) +
          kappa * (B : ℝ) / 1000 := by
    simpa only [zero_mul, add_zero] using h
  exact h'.trans (add_le_add hb le_rfl)

theorem factor_65_of_budget64 (B : ℕ)
    (hBN : (B : ℝ) ≤ (2 : ℝ)^86 / 64) :
    1 + ((B : ℝ) - 1) / (2 : ℝ)^86 ≤ 65 / 64 := by
  have hN : 0 < (2 : ℝ)^86 := by positivity
  have hratio : ((B : ℝ) - 1) / (2 : ℝ)^86 ≤ 1 / 64 :=
    (div_le_iff₀ hN).2 (by linarith)
  linarith

theorem budget64_le_budget10 (B : ℕ)
    (hBN : (B : ℝ) ≤ (2 : ℝ)^86 / 64) :
    (B : ℝ) ≤ (2 : ℝ)^86 / 10 := by
  have hN : 0 ≤ (2 : ℝ)^86 := by positivity
  nlinarith

theorem stopped_core_65_actual { α : Type }
    (oa : OracleComp Spec α) (B : ℕ) (hB : CostAtMost oa B)
    (hBN : (B : ℝ) ≤ (2 : ℝ)^86 / 64)
    (c : hashSpec.QueryCache)
    (hf : ∀ q : Query, q.1 = 342 → c q = none) :
    realEval ((simulateQ oracleImpl oa).run c)
        (fun out => C * pairEnvelope out.2) ≤
      (B : ℝ) * (C * (65 / 64) * mean) +
        kappa * (B : ℝ) / 1000 :=
  stopped_core_65_of_factor oa B hB (budget64_le_budget10 B hBN)
    (factor_65_of_budget64 B hBN) c hf

/-- With one further `1/1000` game allowance, the stronger threshold closes
at the exact small coefficient certified in `LongChain91BudgetArithmetic`. -/
theorem small_coefficient_actual { α : Type }
    (oa : OracleComp Spec α) (B : ℕ) (hB : CostAtMost oa B)
    (hBN : (B : ℝ) ≤ (2 : ℝ)^86 / 64)
    (c : hashSpec.QueryCache)
    (hf : ∀ q : Query, q.1 = 342 → c q = none) :
    realEval ((simulateQ oracleImpl oa).run c)
        (fun out => C * pairEnvelope out.2) + kappa * (B : ℝ) / 1000 ≤
      (6235189 / 6272000) * kappa * (B : ℝ) := by
  have hcore := stopped_core_65_actual oa B hB hBN c hf
  have hfactor : 0 ≤ (B : ℝ) * (C * (65 / 64)) := by
    exact mul_nonneg (Nat.cast_nonneg B)
      (mul_nonneg LongChain91BudgetArithmetic.C_nonneg (by norm_num))
  have hm := mul_le_mul_of_nonneg_left
    LongChain91Security.securityWeights_mean hfactor
  have he := LongChain91BudgetArithmetic.small_coefficient_identity (B : ℝ)
  nlinarith

/-! ## Real/ENNReal transport -/

theorem queryCount_expectation_eq_ofReal { α : Type }
    (oa : OracleComp Spec α) (c : hashSpec.QueryCache) :
    E (run oa c) (fun out => (queryCount out.2 : ℝ≥0∞)) =
      ENNReal.ofReal
        (realEval (run oa c) (fun out => (queryCount out.2 : ℝ))) := by
  simpa only [ENNReal.ofReal_natCast] using
    (ofReal_realEval (run oa c) (fun out => (queryCount out.2 : ℝ))
      (fun out => Nat.cast_nonneg _)).symm

theorem pairEnvelope_expectation_eq_ofReal { α : Type }
    (oa : OracleComp Spec α) (c : hashSpec.QueryCache) :
    E (run oa c) (fun out => ENNReal.ofReal (pairEnvelope out.2)) =
      ENNReal.ofReal
        (realEval (run oa c) (fun out => pairEnvelope out.2)) :=
  (ofReal_realEval (run oa c) (fun out => pairEnvelope out.2)
    (fun out => pairEnvelope_nonneg out.2)).symm

theorem scaledPairEnvelope_expectation_eq_ofReal { α : Type }
    (oa : OracleComp Spec α) (c : hashSpec.QueryCache) :
    E (run oa c) (fun out => ENNReal.ofReal (C * pairEnvelope out.2)) =
      ENNReal.ofReal
        (realEval (run oa c) (fun out => C * pairEnvelope out.2)) :=
  (ofReal_realEval (run oa c) (fun out => C * pairEnvelope out.2)
    (fun out => scaledPairEnvelope_nonneg out.2)).symm

theorem small_coefficient_ennreal { α : Type }
    (oa : OracleComp Spec α) (B : ℕ) (hB : CostAtMost oa B)
    (hBN : (B : ℝ) ≤ (2 : ℝ)^86 / 64)
    (c : hashSpec.QueryCache)
    (hf : ∀ q : Query, q.1 = 342 → c q = none) :
    E (run oa c) (fun out => ENNReal.ofReal (C * pairEnvelope out.2)) +
        ENNReal.ofReal (kappa * (B : ℝ) / 1000) ≤
      ENNReal.ofReal
        ((6235189 / 6272000) * kappa * (B : ℝ)) := by
  have hr := small_coefficient_actual oa B hB hBN c hf
  have hP0 : 0 ≤ realEval (run oa c)
      (fun out => C * pairEnvelope out.2) :=
    realEval_nonneg (run oa c) _ (fun out => scaledPairEnvelope_nonneg out.2)
  have he0 : 0 ≤ kappa * (B : ℝ) / 1000 := by
    exact div_nonneg
      (mul_nonneg LongChain91BudgetArithmetic.kappa_pos.le
        (Nat.cast_nonneg B)) (by norm_num)
  rw [scaledPairEnvelope_expectation_eq_ofReal]
  rw [← ENNReal.ofReal_add hP0 he0]
  exact ENNReal.ofReal_le_ofReal hr

/-- The numerical obstruction at the advertised `2^86/10` threshold: the
generic stopped endpoint is strictly larger than `65/64`. -/
theorem eleven_tenths_not_le_sixtyfive_sixtyfour :
    ¬ (11 / 10 : ℝ) ≤ 65 / 64 := by norm_num

theorem hazard_le_pairEnvelope (m : Message) (c : hashSpec.QueryCache) :
    securityWeights.hazard ((2 : ℝ)^86)
      (seen (WideDomains.rowDomain m) c).card
      (classCounts WideDomains.indexDomain c decode)
      (classCounts (WideDomains.rowDomain m) c decode) ≤ pairEnvelope c := by
  apply securityWeights.hazard_le_score_pair _ (by positivity) _ _ _
  intro i
  exact WeightedCacheCounts.classCounts_mono
    (WideDomains.row_subset m) c decode i

#print axioms moments
#print axioms sharp_stopped_payoff_actual
#print axioms stopped_core_actual
#print axioms stopped_core_65_actual
#print axioms small_coefficient_actual
#print axioms queryCount_expectation_eq_ofReal
#print axioms pairEnvelope_expectation_eq_ofReal
#print axioms small_coefficient_ennreal
#print axioms hazard_le_pairEnvelope

end OptimalOTS.WeightedConstruction.LongChain91SmallMoments
