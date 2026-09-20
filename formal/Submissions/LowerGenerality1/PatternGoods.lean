import Submissions.LowerGenerality1.Patterns
import Submissions.LowerGenerality1.SignFresh
import Submissions.LowerGenerality1.CostCore

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.PatternAttack

open OptimalOTS.Dag


def goodIndices (S : Scheme) : Finset ℕ :=
  (Finset.univ.filter fun i => 8 ≤ (S.samePattern i).card).image Fin.val

theorem mem_goodIndices (S : Scheme) (i : Fin numCuts) :
    i.val ∈ goodIndices S ↔ 8 ≤ (S.samePattern i).card := by
  simp only [goodIndices, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, hji⟩
    have he : j = i := Fin.ext hji
    simpa only [he] using hj
  · exact fun h => ⟨i, h, rfl⟩

theorem goodIndices_lt (S : Scheme) :
    ∀ n ∈ goodIndices S, n < numCuts := by
  intro n hn
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
  exact i.isLt

attribute [local irreducible] hashBits blockBits pkBits msgBits securityBits maxSignatureBits keygenBudget signBudget nonceBits idxBits numCuts trials

theorem cost_signIdx (S : Scheme)
    (hidx : blockCost (msgBits + nonceBits) = 1) (m : Message) :
    CostAtMost (signIdx m) trials := by
  have h := S.costAtMost_sign hidx (fun _ => 0) m
  rw [sign_eq_map] at h
  exact (costAtMost_map_iff _ _ _).mp h

end OptimalOTS.PatternAttack
