import Submissions.UpperCompressions.LongChain91CollisionCap

/-!
# Actual stopped collision bound for the cost-91 long-chain schedule

This file instantiates the equality-collision stopped-process theorem with the
concrete long-chain decoder, row domain, score envelope, and occupancy cap.
It also transfers the simultaneous completed-table occupancy tail back to an
arbitrary adaptive execution from a fresh length-342 cache.
-/

noncomputable section

set_option maxRecDepth 100000

open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical ENNReal

namespace OptimalOTS.WeightedConstruction.LongChain91StoppedCollision

open LongChain91Security LongChain91Occupancy LongChain91CollisionCap

/-- The common pointwise score envelope used by the collision martingale. -/
def collisionScale : ℝ :=
  (Chain18Compact.L : ℝ) * Chain18Compact.kappa / 2

theorem collisionScale_nonneg : 0 ≤ collisionScale := by
  unfold collisionScale Chain18Compact.kappa
  positivity

/-- The stopped self-collision event on one message row. -/
def collisionHit (m : Message) (a v : ℝ) :
    ℕ → hashSpec.QueryCache → Prop :=
  fun _ cache =>
    a ≤ EqualityCollisionCache91.cacheXz securityWeights
      (WideDomains.rowDomain m) LongChain91Empirical.cacheDecode
      collisionScale cache ∧
    EqualityCollisionCache91.cacheXw (WideDomains.rowDomain m)
      collisionJumpBound collisionScale cache ≤ v

/-- Stop before a decoder class in the selected row exceeds its certified
occupancy cap. -/
def occupancyKill (m : Message) : ℕ → hashSpec.QueryCache → Prop :=
  fun _ cache =>
    ¬ EqualityCollisionCache91.OccupancyGood (WideDomains.rowDomain m)
      LongChain91Empirical.cacheDecode cap cache

/-- Concrete specialization of the actual-cache maximal Freedman theorem.
The adversarial program is otherwise arbitrary; only the length-342 part of
the initial public cache must be fresh. -/
theorem actual_stopped_collision_freedman {α : Type}
    (m : Message) (oa : OracleComp Spec α)
    (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none)
    (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    Pr[fun out => out.2.status = WeightedFirstHit.Status.hit |
      (simulateQ (WeightedOracleExecution.stoppedImpl OptimalOTS.oracleImpl
        (collisionHit m a v) (occupancyKill m)) oa).run
          (WeightedFirstHit.classify (collisionHit m a v) (occupancyKill m)
            0 initial)] ≤
      ENNReal.ofReal
        (Real.exp (-a ^ 2 / (2 * (v + collisionJumpBound * a / 3)))) := by
  obtain ⟨hr0, hk0⟩ := LongChain91Empirical.row_initial m initial hfresh
  have hg : ∀ i, securityWeights.g i ≤ collisionScale := by
    intro i
    simpa only [securityWeights_g, collisionScale] using referenceWeight_le i
  have h := EqualityCollisionCache91.actual_stopped_x_freedman
    securityWeights
    (WideDomains.rowDomain m) WideDomains.indexDomain
    (WideDomains.row_subset m)
    LongChain91Empirical.cacheDecode LongChain91Empirical.cache_decoder_law
    cap collisionScale collisionJumpBound collisionScale_nonneg hg
    collisionJumpBound_nonneg collision_cap oa initial hr0 hk0 a v ha hv
  have hhit : collisionHit m a v =
      (fun (_ : ℕ) (cache : hashSpec.QueryCache) =>
        a ≤ EqualityCollisionCache91.cacheXz securityWeights
            (WideDomains.rowDomain m) LongChain91Empirical.cacheDecode
            collisionScale cache ∧
          EqualityCollisionCache91.cacheXw (WideDomains.rowDomain m)
            collisionJumpBound collisionScale cache ≤ v) := by
    funext n cache
    rfl
  have hkill : occupancyKill m =
      (fun (_ : ℕ) (cache : hashSpec.QueryCache) =>
        ¬ EqualityCollisionCache91.OccupancyGood (WideDomains.rowDomain m)
          LongChain91Empirical.cacheDecode cap cache) := by
    funext n cache
    rfl
  rw [hhit, hkill]
  exact h

/-! ## Completed-table tail and actual-cache kill adapters -/

/-- The simultaneous completed-table failure event, kept opaque so posterior
completion arguments do not elaborate the large row predicate repeatedly. -/
def anyRowOverfull
    (table : BitVec (msgBits + 86) → BitVec hashBits) : Prop :=
  ∃ s : Message × Fin LongChain91Security.M, rowOverfull s table

private theorem anyRowOverfull_iff
    (table : BitVec (msgBits + 86) → BitVec hashBits) :
    anyRowOverfull table ↔
      ∃ s : Message × Fin LongChain91Security.M, rowOverfull s table :=
  Iff.rfl

private theorem completed_failure_indicator_eq
    (cache : hashSpec.QueryCache)
    (g : BitVec (msgBits + 86) → BitVec hashBits) :
    (if ¬ CompletedOccupancyGood cache g then (1 : ℝ≥0∞) else 0) =
      (if anyRowOverfull
        (WeightedReplacement.completedTable (msgBits + 86) cache g)
        then 1 else 0) := by
  unfold CompletedOccupancyGood anyRowOverfull
  by_cases h : ∃ s : Message × Fin LongChain91Security.M,
      rowOverfull s
        (WeightedReplacement.completedTable (msgBits + 86) cache g) <;>
    simp only [h, not_true_eq_false, not_false_eq_true, if_false, if_true]

/-- A single completed table is simultaneously occupancy-good for every
message row except with the unconditional `2^-334` tail.  This remains true
after an arbitrary adaptive public computation, averaged over its posterior
completion. -/
theorem completed_occupancy_failure_probability {α : Type}
    (oa : OracleComp Spec α) (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none) :
    E (run oa initial) (fun out =>
      E ($ᵗ (BitVec (msgBits + 86) → BitVec hashBits)) (fun g =>
        if ¬ CompletedOccupancyGood out.2 g then 1 else 0)) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 334 := by
  calc
    _ = E (run oa initial) (fun out =>
        E ($ᵗ (BitVec (msgBits + 86) → BitVec hashBits)) (fun g =>
          if anyRowOverfull
            (WeightedReplacement.completedTable (msgBits + 86) out.2 g)
          then 1 else 0)) := by
      apply congrArg (E (run oa initial))
      funext out
      apply congrArg (E ($ᵗ (BitVec (msgBits + 86) → BitVec hashBits)))
      funext g
      exact completed_failure_indicator_eq out.2 g
    _ ≤ E ($ᵗ (BitVec (msgBits + 86) → BitVec hashBits)) (fun g =>
        if anyRowOverfull g then 1 else 0) :=
      WeightedReplacement.completed_bad_probability_le
        (msgBits + 86) oa initial (fun x => hfresh ⟨342, x⟩ rfl)
        anyRowOverfull
    _ ≤ E ($ᵗ (BitVec (msgBits + 86) → BitVec hashBits)) (fun g =>
        if ∃ s : Message × Fin LongChain91Security.M,
          rowOverfull s g then 1 else 0) := by
      apply E_mono
      intro g
      by_cases h : anyRowOverfull g
      · rw [if_pos h, if_pos ((anyRowOverfull_iff g).mp h)]
      · rw [if_neg h, if_neg (fun hex => h ((anyRowOverfull_iff g).mpr hex))]
    _ ≤ _ := full_table_overfull_probability

/-- The real cache is occupancy-good on every message row whenever one of its
posterior completions is simultaneously good. -/
def AllRowsOccupancyGood (cache : hashSpec.QueryCache) : Prop :=
  ∀ m : Message,
    EqualityCollisionCache91.OccupancyGood (WideDomains.rowDomain m)
      LongChain91Empirical.cacheDecode cap cache

theorem completed_allRowsOccupancyGood
    (cache : hashSpec.QueryCache)
    (g : BitVec (msgBits + 86) → BitVec hashBits)
    (hgood : CompletedOccupancyGood cache g) :
    AllRowsOccupancyGood cache := by
  intro m
  exact completed_occupancyGood cache g hgood m

/-- Strong unconditional adapter: after any adaptive computation from a fresh
length-342 cache, the probability that *some* message row violates the actual
cache occupancy cap is at most `2^-334`. -/
theorem actual_allRows_occupancy_failure_probability {α : Type}
    (oa : OracleComp Spec α) (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none) :
    E (run oa initial) (fun out =>
      if ¬ AllRowsOccupancyGood out.2 then 1 else 0) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 334 := by
  calc
    _ ≤ E (run oa initial) (fun out =>
        E ($ᵗ (BitVec (msgBits + 86) → BitVec hashBits)) (fun g =>
          if ¬ CompletedOccupancyGood out.2 g then 1 else 0)) := by
      apply E_mono
      intro out
      by_cases hrows : AllRowsOccupancyGood out.2
      · simp only [hrows, not_true_eq_false, if_false]
        exact bot_le
      · have hbad : ∀ g : BitVec (msgBits + 86) → BitVec hashBits,
            ¬ CompletedOccupancyGood out.2 g := by
          intro g hcompletion
          exact hrows (completed_allRowsOccupancyGood out.2 g hcompletion)
        have hfun :
            (fun g : BitVec (msgBits + 86) → BitVec hashBits =>
              if ¬ CompletedOccupancyGood out.2 g
              then (1 : ℝ≥0∞) else 0) =
            (fun _ => (1 : ℝ≥0∞)) := by
          funext g
          rw [if_pos (hbad g)]
        rw [if_pos hrows, hfun,
          WeightedReplacement.E_uniform_constant]
    _ ≤ _ := completed_occupancy_failure_probability oa initial hfresh

/-- In particular, a row selected from the program output obeys the same
unconditional kill bound. -/
theorem actual_chosen_row_occupancy_kill_probability {α : Type}
    (oa : OracleComp Spec α) (message : α → Message)
    (initial : hashSpec.QueryCache)
    (hfresh : ∀ q : Query, q.1 = 342 → initial q = none) :
    E (run oa initial) (fun out =>
      if occupancyKill (message out.1) 0 out.2 then 1 else 0) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 334 := by
  calc
    _ ≤ E (run oa initial) (fun out =>
        if ¬ AllRowsOccupancyGood out.2 then 1 else 0) := by
      apply E_mono
      intro out
      by_cases hkill : occupancyKill (message out.1) 0 out.2
      · have hkill' :
            ¬ EqualityCollisionCache91.OccupancyGood
              (WideDomains.rowDomain (message out.1))
              LongChain91Empirical.cacheDecode cap out.2 := by
          simpa only [occupancyKill] using hkill
        have hrows : ¬ AllRowsOccupancyGood out.2 := by
          intro hall
          exact hkill' (hall (message out.1))
        simp only [if_pos hkill, if_pos hrows]
        exact le_rfl
      · simp only [if_neg hkill]
        exact bot_le
    _ ≤ _ := actual_allRows_occupancy_failure_probability oa initial hfresh

#print axioms actual_stopped_collision_freedman
#print axioms completed_occupancy_failure_probability
#print axioms completed_allRowsOccupancyGood
#print axioms actual_allRows_occupancy_failure_probability
#print axioms actual_chosen_row_occupancy_kill_probability

end OptimalOTS.WeightedConstruction.LongChain91StoppedCollision
