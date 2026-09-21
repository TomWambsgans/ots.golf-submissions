import Submissions.UpperCompressions.LongChain91Occupancy
import Submissions.UpperCompressions.CollisionCache91
import Submissions.UpperCompressions.LongChain91SecurityData

/-!
# Concrete collision cap for the cost-91 long-chain schedule

The stopped self-collision theorem requires one deterministic jump bound for
all decoder classes.  This module checks that bound against the exact
160-tier table, then connects a good completed nonce table to the real-cache
occupancy predicate used by the stopped process.
-/

noncomputable section

open OracleSpec OracleComp
open scoped Classical BigOperators

namespace OptimalOTS.WeightedConstruction.LongChain91CollisionCap

open LongChain91Security LongChain91Occupancy

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- A uniform upper bound for every capped self-collision increment. -/
def collisionJumpBound : ℝ :=
  332 * (Chain18Compact.L : ℝ) ^ 2 * Chain18Compact.kappa

theorem collisionJumpBound_nonneg : 0 ≤ collisionJumpBound := by
  unfold collisionJumpBound Chain18Compact.kappa
  positivity

/-- Integer cross-multiplication of the desired rational inequality.  All
160 cases reduce to the checked compact-schedule tables. -/
theorem capTier_kernel_numerator (j : Chain18Compact.Tier) :
    2 * capTier j * Chain18Compact.aliases j *
        Chain18Compact.kernelNumerator j ^ 2 * 2 ^ 127 ≤
      332 * Chain18Compact.L ^ 2 * Chain18Compact.R *
        Chain18Compact.KQ ^ 2 := by
  revert j
  decide +kernel

/-- The rounded kernel table obeys the common jump bound. -/
theorem capTier_kernelUpper_le (j : Chain18Compact.Tier) :
    2 * (capTier j : ℝ) * Chain18Compact.probability j *
        Chain18Compact.kernelUpper j ^ 2 ≤ collisionJumpBound := by
  have hnat := capTier_kernel_numerator j
  have hcast :
      ((2 * capTier j * Chain18Compact.aliases j *
          Chain18Compact.kernelNumerator j ^ 2 * 2 ^ 127 : ℕ) : ℝ) ≤
        ((332 * Chain18Compact.L ^ 2 * Chain18Compact.R *
          Chain18Compact.KQ ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hR : 0 < (Chain18Compact.R : ℝ) := by
    norm_num [Chain18Compact.R]
  have hK : 0 < (Chain18Compact.KQ : ℝ) := by
    norm_num [Chain18Compact.KQ]
  have hP : 0 < (2 : ℝ) ^ 127 := by positivity
  have hform :
      2 * (capTier j : ℝ) * Chain18Compact.probability j *
          Chain18Compact.kernelUpper j ^ 2 =
        ((2 * capTier j * Chain18Compact.aliases j *
          Chain18Compact.kernelNumerator j ^ 2 : ℕ) : ℝ) /
          ((Chain18Compact.R : ℝ) * (Chain18Compact.KQ : ℝ) ^ 2) := by
    unfold Chain18Compact.probability Chain18Compact.kernelUpper
    push_cast
    field_simp [hR.ne', hK.ne']
    <;> ring
  rw [hform]
  apply (div_le_iff₀ (mul_pos hR (sq_pos_of_pos hK))).2
  rw [show collisionJumpBound *
      ((Chain18Compact.R : ℝ) * (Chain18Compact.KQ : ℝ) ^ 2) =
      ((332 : ℝ) * (Chain18Compact.L : ℝ) ^ 2 *
        ((Chain18Compact.R : ℝ) * (Chain18Compact.KQ : ℝ) ^ 2)) /
          (2 : ℝ) ^ 127 by
    unfold collisionJumpBound Chain18Compact.kappa
    rw [div_eq_mul_inv]
    ring]
  apply (le_div_iff₀ hP).2
  push_cast at hcast ⊢
  ring_nf at hcast ⊢
  exact hcast

/-- For the concrete weights, collision mass is exactly class probability
times the square of the true finite-difference kernel. -/
theorem security_collisionMass_eq (i : Fin LongChain91Security.M) :
    securityWeights.collisionMass i =
      classProbability i *
        Chain18Compact.actualKernel (LongChain91Schedule.tier i) ^ 2 := by
  rw [WeightedRow.Weights.collisionMass_eq, securityWeights_p,
    securityWeights_g, weight_ratio]

/-- The exact cap selected by `LongChain91Occupancy` supplies the uniform
`hcap` premise of `EqualityCollisionCache91.actual_stopped_x_freedman`. -/
theorem collision_cap (i : Fin LongChain91Security.M) :
    2 * (cap i : ℝ) * securityWeights.collisionMass i ≤
      collisionJumpBound := by
  have hsquare :
      Chain18Compact.actualKernel (LongChain91Schedule.tier i) ^ 2 ≤
        Chain18Compact.kernelUpper (LongChain91Schedule.tier i) ^ 2 :=
    pow_le_pow_left₀
      (Chain18Compact.actualKernel_nonneg (LongChain91Schedule.tier i))
      (Chain18Compact.actualKernel_le (LongChain91Schedule.tier i)) 2
  calc
    2 * (cap i : ℝ) * securityWeights.collisionMass i =
        (2 * (cap i : ℝ) * classProbability i) *
          Chain18Compact.actualKernel (LongChain91Schedule.tier i) ^ 2 := by
      rw [security_collisionMass_eq]
      ring
    _ ≤ (2 * (cap i : ℝ) * classProbability i) *
          Chain18Compact.kernelUpper (LongChain91Schedule.tier i) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare
        (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
          (classProbability_pos i).le)
    _ = 2 * (capTier (LongChain91Schedule.tier i) : ℝ) *
          Chain18Compact.probability (LongChain91Schedule.tier i) *
          Chain18Compact.kernelUpper (LongChain91Schedule.tier i) ^ 2 := by
      rfl
    _ ≤ collisionJumpBound :=
      capTier_kernelUpper_le (LongChain91Schedule.tier i)

/-! ## Completed-table occupancy bridge -/

/-- One completed length-342 table has no overfull message/class row. -/
def CompletedOccupancyGood (cache : hashSpec.QueryCache)
    (g : BitVec (msgBits + 86) → BitVec hashBits) : Prop :=
  ¬ ∃ s : Message × Fin LongChain91Security.M,
    rowOverfull s
      (WeightedReplacement.completedTable (msgBits + 86) cache g)

private theorem classCounts_mono_cache {D B ι : Type}
    [DecidableEq D] [Fintype ι] [DecidableEq ι]
    (A : Finset D) (cache complete : D → Option B)
    (decode : B → Option ι)
    (hsub : ∀ q y, cache q = some y → complete q = some y) (i : ι) :
    WeightedCacheCounts.classCounts A cache decode i ≤
      WeightedCacheCounts.classCounts A complete decode i := by
  unfold WeightedCacheCounts.classCounts WeightedPublicCounts.counts
    WeightedCacheCounts.seen
  apply Finset.card_le_card
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hseen, hdecode⟩
  rcases Finset.mem_filter.mp hseen with ⟨hA, hsome⟩
  cases hc : cache q with
  | none => simp [hc] at hsome
  | some y =>
      have hd : complete q = some y := hsub q y hc
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨hA, ?_⟩, ?_⟩
      · simp [hd]
      · simpa [hc, hd] using hdecode

private theorem classCounts_preload_le
    (m : Message) (cache : hashSpec.QueryCache)
    (g : BitVec (msgBits + 86) → BitVec hashBits)
    (i : Fin LongChain91Security.M) :
    WeightedCacheCounts.classCounts (WideDomains.rowDomain m) cache
        LongChain91Empirical.cacheDecode i ≤
      WeightedCacheCounts.classCounts (WideDomains.rowDomain m)
        ((WeightedReplacement.lengthSlice (msgBits + 86)).preload cache g)
        LongChain91Empirical.cacheDecode i := by
  apply classCounts_mono_cache
  intro q y hq
  exact WeightedReplacement.QuerySlice.preload_some _ _ _ q y hq

private theorem classCounts_preload_row_eq
    (m : Message) (cache : hashSpec.QueryCache)
    (g : BitVec (msgBits + 86) → BitVec hashBits)
    (i : Fin LongChain91Security.M) :
    WeightedCacheCounts.classCounts (WideDomains.rowDomain m)
        ((WeightedReplacement.lengthSlice (msgBits + 86)).preload cache g)
        LongChain91Empirical.cacheDecode i =
      (Finset.univ.filter fun η : BitVec 86 =>
        LongChain91Empirical.cacheDecode
          (WeightedReplacement.completedTable (msgBits + 86) cache g
            (m ++ η)) = some i).card := by
  let complete :=
    (WeightedReplacement.lengthSlice (msgBits + 86)).preload cache g
  have hseen :
      WeightedCacheCounts.seen (WideDomains.rowDomain m) complete =
        WideDomains.rowDomain m := by
    unfold WeightedCacheCounts.seen
    apply Finset.filter_eq_self.mpr
    intro q hq
    obtain ⟨η, rfl⟩ := (WideDomains.mem_rowDomain m q).mp hq
    have hp := WeightedReplacement.length_preload_row 86 m cache g η
    change (complete (WideForest.encQuery (m, η))).isSome = true
    simpa [complete, WideForest.encQuery] using congrArg Option.isSome hp
  unfold WeightedCacheCounts.classCounts
  rw [hseen]
  unfold WeightedPublicCounts.counts
  have himage :
      (WideDomains.rowDomain m).filter
          (fun q => (complete q).bind LongChain91Empirical.cacheDecode = some i) =
        (Finset.univ.filter fun η : BitVec 86 =>
          LongChain91Empirical.cacheDecode
            (WeightedReplacement.completedTable (msgBits + 86) cache g
              (m ++ η)) = some i).image
            (fun η => WideForest.encQuery (m, η)) := by
    ext q
    constructor
    · intro hq
      obtain ⟨hqrow, hqdecode⟩ := Finset.mem_filter.mp hq
      obtain ⟨η, he⟩ := (WideDomains.mem_rowDomain m q).mp hqrow
      subst q
      apply Finset.mem_image.mpr
      refine ⟨η, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      have hp := WeightedReplacement.length_preload_row 86 m cache g η
      change complete (WideForest.encQuery (m, η)) =
        some (WeightedReplacement.cachedRow 86 m cache g η) at hp
      rw [hp] at hqdecode
      simp only [Option.bind_some] at hqdecode
      simpa [WeightedReplacement.cachedRow,
        WeightedReplacement.completedTable] using hqdecode
    · intro hq
      obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hq
      apply Finset.mem_filter.mpr
      refine ⟨(WideDomains.mem_rowDomain m _).mpr ⟨η, rfl⟩, ?_⟩
      have hp := WeightedReplacement.length_preload_row 86 m cache g η
      change complete (WideForest.encQuery (m, η)) =
        some (WeightedReplacement.cachedRow 86 m cache g η) at hp
      rw [hp]
      rw [Option.bind_some]
      have hdecode := (Finset.mem_filter.mp hη).2
      simpa [WeightedReplacement.cachedRow,
        WeightedReplacement.completedTable] using hdecode
  rw [himage, Finset.card_image_of_injective]
  intro η ζ h
  exact WeightedSampling.Availability.nonce_query_inj m h

/-- A good completed table bounds every multiplicity already present in the
actual cache on the chosen message row. -/
theorem completed_occupancyGood
    (cache : hashSpec.QueryCache)
    (g : BitVec (msgBits + 86) → BitVec hashBits)
    (hgood : CompletedOccupancyGood cache g) (m : Message) :
    EqualityCollisionCache91.OccupancyGood (WideDomains.rowDomain m)
      LongChain91Empirical.cacheDecode cap cache := by
  intro i
  calc
    WeightedCacheCounts.classCounts (WideDomains.rowDomain m) cache
        LongChain91Empirical.cacheDecode i ≤
      WeightedCacheCounts.classCounts (WideDomains.rowDomain m)
        ((WeightedReplacement.lengthSlice (msgBits + 86)).preload cache g)
        LongChain91Empirical.cacheDecode i := classCounts_preload_le m cache g i
    _ = (Finset.univ.filter fun η : BitVec 86 =>
        LongChain91Empirical.cacheDecode
          (WeightedReplacement.completedTable (msgBits + 86) cache g
            (m ++ η)) = some i).card :=
      classCounts_preload_row_eq m cache g i
    _ ≤ cap i := by
      have hrow : ¬ rowOverfull (m, i)
          (WeightedReplacement.completedTable (msgBits + 86) cache g) := by
        intro hover
        exact hgood ⟨(m, i), hover⟩
      have hnamed : ¬ cap i ≤ (Finset.univ.filter fun η : BitVec 86 =>
          decodesTo i
            (WeightedReplacement.completedTable (msgBits + 86) cache g
              (rowInput m η))).card := by
        intro hover
        exact hrow ((rowOverfull_iff (m, i) _).2 hover)
      have hn : ¬ cap i ≤ (Finset.univ.filter fun η : BitVec 86 =>
          LongChain91Empirical.cacheDecode
            (WeightedReplacement.completedTable (msgBits + 86) cache g
              (m ++ η)) = some i).card := by
        have hfilters :
            (Finset.univ.filter fun η : BitVec 86 =>
              decodesTo i
                (WeightedReplacement.completedTable (msgBits + 86) cache g
                  (rowInput m η))) =
              (Finset.univ.filter fun η : BitVec 86 =>
                LongChain91Empirical.cacheDecode
                  (WeightedReplacement.completedTable (msgBits + 86) cache g
                    (m ++ η)) = some i) := by
          apply Finset.filter_congr
          intro η hη
          rfl
        have hcards := congrArg Finset.card hfilters
        rw [hcards] at hnamed
        exact hnamed
      omega

#print axioms capTier_kernel_numerator
#print axioms capTier_kernelUpper_le
#print axioms security_collisionMass_eq
#print axioms collision_cap
#print axioms completed_occupancyGood

end OptimalOTS.WeightedConstruction.LongChain91CollisionCap
