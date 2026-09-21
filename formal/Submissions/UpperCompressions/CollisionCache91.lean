import Submissions.UpperCompressions.EqualityCollision91
import Submissions.UpperCompressions.ProofBundle12

/-!
# Actual-cache bridge for equality replay clocks

The equality collision algebra in `EqualityCollision91` is phrased for two
multiplicity vectors: all exposed index inputs and one distinguished nonce row.
This file connects those vectors to the contract's real memoized random-oracle
cache.  A fresh row query advances both vectors with the same decoded answer; a
fresh index query outside the row advances only the global vector; every cache
hit and every private query leaves both vectors fixed.

The bridge is deliberately generic in the finite decoder.  The chain-18
schedule can instantiate it once its decoder-fiber theorem is available.
-/

noncomputable section

open OracleSpec OracleComp OracleComp.EvalDist
open scoped Classical BigOperators ENNReal

namespace EqualityCollisionCache91

open WeightedCacheCounts WeightedRealExecution
open WeightedRow.Weights WeightedDualCache

set_option maxHeartbeats 1600000

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The four equality-replay clocks carried by global and row multiplicities. -/
structure Clocks where
  diagonal : ℝ
  selfCollision : ℝ
  reverse : ℝ
  forward : ℝ
  deriving DecidableEq

@[ext] theorem Clocks.ext {a b : Clocks}
    (hD : a.diagonal = b.diagonal)
    (hX : a.selfCollision = b.selfCollision)
    (hR : a.reverse = b.reverse)
    (hF : a.forward = b.forward) : a = b := by
  cases a
  cases b
  simp_all

def clocks (w : WeightedRow.Weights ι) (global row : ι → ℕ) : Clocks where
  diagonal := w.D row
  selfCollision := w.X row
  reverse := w.Qrev row
  forward := w.Qfwd global

/-- One joint decoded transition of the four clocks. -/
def stepClocks (w : WeightedRow.Weights ι) (s : Phase)
    (global row : ι → ℕ) (x : Option ι) : Clocks :=
  match s with
  | .idle => clocks w global row
  | .outside =>
      { diagonal := w.D row
        selfCollision := w.X row
        reverse := w.Qrev row
        forward := w.Qfwd global + w.qfwdJump global x }
  | .inside =>
      { diagonal := w.D row + w.dJump x
        selfCollision := w.X row + w.xJump row x
        reverse := w.Qrev row + w.qrevJump row x
        forward := w.Qfwd global + w.qfwdJump global x }

theorem clocks_reverse_eq (w : WeightedRow.Weights ι) (global row : ι → ℕ) :
    (clocks w global row).reverse =
      (clocks w global row).diagonal + (clocks w global row).selfCollision := by
  exact w.Qrev_eq_D_add_X row

theorem stepClocks_reverse_eq (w : WeightedRow.Weights ι) (s : Phase)
    (global row : ι → ℕ) (x : Option ι) :
    (stepClocks w s global row x).reverse =
      (stepClocks w s global row x).diagonal +
        (stepClocks w s global row x).selfCollision := by
  cases s with
  | idle => exact w.Qrev_eq_D_add_X row
  | outside => exact w.Qrev_eq_D_add_X row
  | inside =>
      simp only [stepClocks]
      rw [show w.Qrev row = w.D row + w.X row from w.Qrev_eq_D_add_X row]
      rw [w.qrevJump_eq row x]
      ring

/-- `stepClocks` is exactly the diagonal transition made by the generic dual
cache kernel. -/
theorem after_diagonal (w : WeightedRow.Weights ι) (s : Phase) (r : ℕ)
    (global row : ι → ℕ) (x : Option ι) :
    after (fun _ _ row => w.D row) s r global row x =
      (stepClocks w s global row x).diagonal := by
  cases s with
  | idle => rfl
  | outside => rfl
  | inside => exact w.D_advance row x

theorem after_selfCollision (w : WeightedRow.Weights ι) (s : Phase) (r : ℕ)
    (global row : ι → ℕ) (x : Option ι) :
    after (fun _ _ row => w.X row) s r global row x =
      (stepClocks w s global row x).selfCollision := by
  cases s with
  | idle => rfl
  | outside => rfl
  | inside => exact w.X_advance row x

theorem after_reverse (w : WeightedRow.Weights ι) (s : Phase) (r : ℕ)
    (global row : ι → ℕ) (x : Option ι) :
    after (fun _ _ row => w.Qrev row) s r global row x =
      (stepClocks w s global row x).reverse := by
  cases s with
  | idle => rfl
  | outside => rfl
  | inside => exact w.Qrev_advance row x

theorem after_forward (w : WeightedRow.Weights ι) (s : Phase) (r : ℕ)
    (global row : ι → ℕ) (x : Option ι) :
    after (fun _ global _ => w.Qfwd global) s r global row x =
      (stepClocks w s global row x).forward := by
  cases s with
  | idle => rfl
  | outside => exact w.Qfwd_advance global x
  | inside => exact w.Qfwd_advance global x

/-- `stepClocks` is the whole joint transition made by the generic dual cache
kernel, observed through an arbitrary real payoff. -/
theorem after_payoff_clocks (w : WeightedRow.Weights ι) (payoff : Clocks → ℝ)
    (s : Phase) (r : ℕ) (global row : ι → ℕ) :
    after (fun _ global row => payoff (clocks w global row)) s r global row =
      fun x => payoff (stepClocks w s global row x) := by
  funext x
  cases s with
  | idle => rfl
  | outside =>
      apply congrArg payoff
      apply Clocks.ext
      · rfl
      · rfl
      · rfl
      · exact w.Qfwd_advance global x
  | inside =>
      apply congrArg payoff
      apply Clocks.ext
      · exact w.D_advance row x
      · exact w.X_advance row x
      · exact w.Qrev_advance row x
      · exact w.Qfwd_advance global x

/-- Collision clocks read directly from a real shared-oracle cache. -/
def cacheClocks (w : WeightedRow.Weights ι)
    (A G : Finset OptimalOTS.Query)
    (decode : BitVec OptimalOTS.hashBits → Option ι)
    (cache : OptimalOTS.hashSpec.QueryCache) : Clocks :=
  clocks w (WeightedCacheCounts.classCounts (ι := ι) G cache decode)
    (WeightedCacheCounts.classCounts (ι := ι) A cache decode)

/-- Exact one-query coupling for the actual contract oracle.  The right-hand
side samples one decoder outcome and applies the matching cache phase. -/
theorem actual_clock_law (w : WeightedRow.Weights ι)
    (A G : Finset OptimalOTS.Query) (hAG : A ⊆ G)
    (decode : BitVec OptimalOTS.hashBits → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b = x)).card : ℝ) /
      Fintype.card (BitVec OptimalOTS.hashBits) = w.classMass x)
    (t : OptimalOTS.Spec.Domain) (cache : OptimalOTS.hashSpec.QueryCache)
    (payoff : Clocks → ℝ) :
    realEval ((OptimalOTS.oracleImpl t).run cache)
      (fun out => payoff (cacheClocks w A G decode out.2)) =
    w.expect (fun x => payoff (stepClocks w (protectedPhase A G t cache)
      (WeightedCacheCounts.classCounts (ι := ι) G cache decode)
      (WeightedCacheCounts.classCounts (ι := ι) A cache decode) x)) := by
  have h := actual_query_law w A G hAG decode hfiber t cache
    (fun _ global row => payoff (clocks w global row))
  change realEval ((OptimalOTS.oracleImpl t).run cache)
      (fun out => payoff (clocks w
        (WeightedCacheCounts.classCounts (ι := ι) G out.2 decode)
        (WeightedCacheCounts.classCounts (ι := ι) A out.2 decode))) = _
  rw [h]
  exact congrArg w.expect (after_payoff_clocks w payoff _ _ _ _)

/-- Every supported primitive result has the exact diagonal-clock transition
for some decoded answer. -/
theorem actual_diagonal_support (w : WeightedRow.Weights ι)
    (A G : Finset OptimalOTS.Query) (hAG : A ⊆ G)
    (decode : BitVec OptimalOTS.hashBits → Option ι)
    (t : OptimalOTS.Spec.Domain) (cache : OptimalOTS.hashSpec.QueryCache)
    (out : OptimalOTS.Spec.Range t × OptimalOTS.hashSpec.QueryCache)
    (hout : out ∈ support ((OptimalOTS.oracleImpl t).run cache)) :
    ∃ x : Option ι, (cacheClocks w A G decode out.2).diagonal =
      (stepClocks w (protectedPhase A G t cache)
        (WeightedCacheCounts.classCounts (ι := ι) G cache decode)
        (WeightedCacheCounts.classCounts (ι := ι) A cache decode) x).diagonal := by
  obtain ⟨x, hx⟩ := actual_payoff_support A G hAG decode t cache
    (fun _ _ row => w.D row) out hout
  refine ⟨x, ?_⟩
  change w.D (WeightedCacheCounts.classCounts (ι := ι) A out.2 decode) = _
  rw [hx]
  exact after_diagonal w _ _ _ _ _

/-- Every supported primitive result has the exact self-collision transition
for some decoded answer. -/
theorem actual_selfCollision_support (w : WeightedRow.Weights ι)
    (A G : Finset OptimalOTS.Query) (hAG : A ⊆ G)
    (decode : BitVec OptimalOTS.hashBits → Option ι)
    (t : OptimalOTS.Spec.Domain) (cache : OptimalOTS.hashSpec.QueryCache)
    (out : OptimalOTS.Spec.Range t × OptimalOTS.hashSpec.QueryCache)
    (hout : out ∈ support ((OptimalOTS.oracleImpl t).run cache)) :
    ∃ x : Option ι, (cacheClocks w A G decode out.2).selfCollision =
      (stepClocks w (protectedPhase A G t cache)
        (WeightedCacheCounts.classCounts (ι := ι) G cache decode)
        (WeightedCacheCounts.classCounts (ι := ι) A cache decode) x).selfCollision := by
  obtain ⟨x, hx⟩ := actual_payoff_support A G hAG decode t cache
    (fun _ _ row => w.X row) out hout
  refine ⟨x, ?_⟩
  change w.X (WeightedCacheCounts.classCounts (ι := ι) A out.2 decode) = _
  rw [hx]
  exact after_selfCollision w _ _ _ _ _

/-- Every supported primitive result has the exact reverse-clock transition
for some decoded answer. -/
theorem actual_reverse_support (w : WeightedRow.Weights ι)
    (A G : Finset OptimalOTS.Query) (hAG : A ⊆ G)
    (decode : BitVec OptimalOTS.hashBits → Option ι)
    (t : OptimalOTS.Spec.Domain) (cache : OptimalOTS.hashSpec.QueryCache)
    (out : OptimalOTS.Spec.Range t × OptimalOTS.hashSpec.QueryCache)
    (hout : out ∈ support ((OptimalOTS.oracleImpl t).run cache)) :
    ∃ x : Option ι, (cacheClocks w A G decode out.2).reverse =
      (stepClocks w (protectedPhase A G t cache)
        (WeightedCacheCounts.classCounts (ι := ι) G cache decode)
        (WeightedCacheCounts.classCounts (ι := ι) A cache decode) x).reverse := by
  obtain ⟨x, hx⟩ := actual_payoff_support A G hAG decode t cache
    (fun _ _ row => w.Qrev row) out hout
  refine ⟨x, ?_⟩
  change w.Qrev (WeightedCacheCounts.classCounts (ι := ι) A out.2 decode) = _
  rw [hx]
  exact after_reverse w _ _ _ _ _

/-- Every supported primitive result has the exact forward-clock transition
for some decoded answer. -/
theorem actual_forward_support (w : WeightedRow.Weights ι)
    (A G : Finset OptimalOTS.Query) (hAG : A ⊆ G)
    (decode : BitVec OptimalOTS.hashBits → Option ι)
    (t : OptimalOTS.Spec.Domain) (cache : OptimalOTS.hashSpec.QueryCache)
    (out : OptimalOTS.Spec.Range t × OptimalOTS.hashSpec.QueryCache)
    (hout : out ∈ support ((OptimalOTS.oracleImpl t).run cache)) :
    ∃ x : Option ι, (cacheClocks w A G decode out.2).forward =
      (stepClocks w (protectedPhase A G t cache)
        (WeightedCacheCounts.classCounts (ι := ι) G cache decode)
        (WeightedCacheCounts.classCounts (ι := ι) A cache decode) x).forward := by
  obtain ⟨x, hx⟩ := actual_payoff_support A G hAG decode t cache
    (fun _ global _ => w.Qfwd global) out hout
  refine ⟨x, ?_⟩
  change w.Qfwd (WeightedCacheCounts.classCounts (ι := ι) G out.2 decode) = _
  rw [hx]
  exact after_forward w _ _ _ _ _

/-! The diagonal and forward clocks also chain through complete adaptive
`OracleComp` programs.  These two lemmas use the one-domain cache kernel: `D`
is an exact martingale after subtracting its mean, while `Qfwd` is a
supermartingale after subtracting the same envelope. -/

def cacheDm (w : WeightedRow.Weights ι) (A : Finset OptimalOTS.Query)
    (decode : BitVec OptimalOTS.hashBits → Option ι)
    (cache : OptimalOTS.hashSpec.QueryCache) : ℝ :=
  w.D (WeightedCacheCounts.classCounts A cache decode) -
    w.diagonalMean * (WeightedCacheCounts.seen A cache).card

def cacheQfwdM (w : WeightedRow.Weights ι) (A : Finset OptimalOTS.Query)
    (decode : BitVec OptimalOTS.hashBits → Option ι)
    (cache : OptimalOTS.hashSpec.QueryCache) : ℝ :=
  w.Qfwd (WeightedCacheCounts.classCounts A cache decode) -
    w.diagonalMean * (WeightedCacheCounts.seen A cache).card

theorem actual_D_step_eq (w : WeightedRow.Weights ι)
    (A : Finset OptimalOTS.Query)
    (decode : BitVec OptimalOTS.hashBits → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b = x)).card : ℝ) /
      Fintype.card (BitVec OptimalOTS.hashBits) = w.classMass x)
    (t : OptimalOTS.Spec.Domain) (cache : OptimalOTS.hashSpec.QueryCache) :
    realEval ((OptimalOTS.oracleImpl t).run cache)
      (fun out => cacheDm w A decode out.2) = cacheDm w A decode cache := by
  let r := (WeightedCacheCounts.seen A cache).card
  let row := WeightedCacheCounts.classCounts A cache decode
  have hlaw := WeightedProtectedCache.query_law w A decode hfiber t cache
    (fun r row => w.D row-w.diagonalMean*(r:ℝ))
  change realEval ((OptimalOTS.oracleImpl t).run cache)
      (fun out => w.D (WeightedCacheCounts.classCounts A out.2 decode)-
        w.diagonalMean*((WeightedCacheCounts.seen A out.2).card:ℝ)) =
      w.D row-w.diagonalMean*(r:ℝ)
  rw [hlaw]
  cases hfresh : WeightedDirectCache.protectedFresh A t cache with
  | false =>
      simp only [hfresh, step, Bool.false_eq_true, ite_false, expect_const]
      rfl
  | true =>
      simp only [hfresh, step, ite_true]
      change w.expect (fun x => w.D (advance row x)-w.diagonalMean*((r+1:ℕ):ℝ)) =
        w.D row-w.diagonalMean*(r:ℝ)
      rw [show (fun x => w.D (advance row x)-w.diagonalMean*((r+1:ℕ):ℝ)) =
          (fun x => (w.D row-w.diagonalMean*(r:ℝ))+
            (w.dJump x-w.diagonalMean)) by
        funext x
        rw [w.D_advance]
        push_cast
        ring]
      rw [w.expect_add, w.expect_const, w.expect_sub, w.expect_dJump,
        w.expect_const, sub_self, add_zero]

theorem actual_Qfwd_step_le (w : WeightedRow.Weights ι)
    (A : Finset OptimalOTS.Query)
    (decode : BitVec OptimalOTS.hashBits → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b = x)).card : ℝ) /
      Fintype.card (BitVec OptimalOTS.hashBits) = w.classMass x)
    (t : OptimalOTS.Spec.Domain) (cache : OptimalOTS.hashSpec.QueryCache) :
    realEval ((OptimalOTS.oracleImpl t).run cache)
      (fun out => cacheQfwdM w A decode out.2) ≤ cacheQfwdM w A decode cache := by
  let q := (WeightedCacheCounts.seen A cache).card
  let k := WeightedCacheCounts.classCounts A cache decode
  have hlaw := WeightedProtectedCache.query_law w A decode hfiber t cache
    (fun q k => w.Qfwd k-w.diagonalMean*(q:ℝ))
  change realEval ((OptimalOTS.oracleImpl t).run cache)
      (fun out => w.Qfwd (WeightedCacheCounts.classCounts A out.2 decode)-
        w.diagonalMean*((WeightedCacheCounts.seen A out.2).card:ℝ)) ≤ _
  rw [hlaw]
  cases hfresh : WeightedDirectCache.protectedFresh A t cache with
  | false =>
      simp only [hfresh, step, Bool.false_eq_true, ite_false, expect_const]
      exact le_rfl
  | true =>
      simp only [hfresh, step, ite_true]
      change w.expect (fun x => w.Qfwd (advance k x)-w.diagonalMean*((q+1:ℕ):ℝ)) ≤
        w.Qfwd k-w.diagonalMean*(q:ℝ)
      rw [show (fun x => w.Qfwd (advance k x)-w.diagonalMean*((q+1:ℕ):ℝ)) =
          (fun x => (w.Qfwd k-w.diagonalMean*(q:ℝ))+
            (w.qfwdJump k x-w.diagonalMean)) by
        funext x
        rw [w.Qfwd_advance]
        push_cast
        ring]
      rw [w.expect_add, w.expect_const, w.expect_sub, w.expect_qfwdJump,
        w.expect_const]
      linarith [w.unseenDiagonalMean_le k]

theorem actual_D_martingale {α : Type} (w : WeightedRow.Weights ι)
    (A : Finset OptimalOTS.Query)
    (decode : BitVec OptimalOTS.hashBits → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b = x)).card : ℝ) /
      Fintype.card (BitVec OptimalOTS.hashBits) = w.classMass x)
    (oa : OracleComp OptimalOTS.Spec α) (initial : OptimalOTS.hashSpec.QueryCache) :
    realEval ((simulateQ OptimalOTS.oracleImpl oa).run initial)
      (fun out => cacheDm w A decode out.2) = cacheDm w A decode initial := by
  exact WeightedRealExecution.realEval_simulate_eq OptimalOTS.oracleImpl
    (cacheDm w A decode) (actual_D_step_eq w A decode hfiber) oa initial

theorem actual_Qfwd_supermartingale {α : Type} (w : WeightedRow.Weights ι)
    (A : Finset OptimalOTS.Query)
    (decode : BitVec OptimalOTS.hashBits → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b = x)).card : ℝ) /
      Fintype.card (BitVec OptimalOTS.hashBits) = w.classMass x)
    (oa : OracleComp OptimalOTS.Spec α) (initial : OptimalOTS.hashSpec.QueryCache) :
    realEval ((simulateQ OptimalOTS.oracleImpl oa).run initial)
      (fun out => cacheQfwdM w A decode out.2) ≤ cacheQfwdM w A decode initial := by
  exact WeightedRealExecution.realEval_simulate_le OptimalOTS.oracleImpl
    (cacheQfwdM w A decode) (actual_Qfwd_step_le w A decode hfiber) oa initial

/-! ## The stopped self-collision process -/

/-- Decoded class multiplicities cannot outnumber the finite set of inputs
from which they were obtained.  Rejected decoder outputs account for the
possible strict inequality. -/
theorem counts_sum_le_card {Q : Type} [DecidableEq Q]
    (S : Finset Q) (answer : Q → Option ι) :
    (∑ i : ι, WeightedPublicCounts.counts S answer i) ≤ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [WeightedPublicCounts.counts]
  | @insert q S hq ih =>
      rw [Finset.card_insert_of_notMem hq]
      simp_rw [WeightedPublicCounts.counts_insert_apply S answer q hq]
      rw [Finset.sum_add_distrib]
      have hone : (∑ i : ι, if answer q = some i then 1 else 0) ≤ 1 := by
        cases ha : answer q with
        | none => simp [ha]
        | some j => simp [ha]
      omega

theorem classCounts_sum_le_seen {B : Type} {D : Type} [DecidableEq D]
    (A : Finset D) (cache : D → Option B) (decode : B → Option ι) :
    (∑ i : ι, WeightedCacheCounts.classCounts A cache decode i) ≤
      (WeightedCacheCounts.seen A cache).card := by
  unfold WeightedCacheCounts.classCounts
  exact counts_sum_le_card _ _

/-- Self-collision martingale coordinate after subtracting the deterministic
envelope for the accumulated conditional means `2 r G²`. -/
def xZ (w : WeightedRow.Weights ι) (G : ℝ) (r : ℕ) (row : ι → ℕ) : ℝ :=
  w.X row - G^2 * (r : ℝ) * ((r : ℝ) - 1)

/-- Predictable variance clock paired with `xZ`. -/
def xW (J G : ℝ) (r : ℕ) : ℝ :=
  J * G^2 * (r : ℝ) * ((r : ℝ) - 1)

theorem xZ_advance (w : WeightedRow.Weights ι) (G : ℝ) (r : ℕ)
    (row : ι → ℕ) (x : Option ι) :
    xZ w G (r+1) (advance row x) =
      xZ w G r row + (w.xJump row x - 2*(r:ℝ)*G^2) := by
  unfold xZ
  rw [w.X_advance]
  push_cast
  ring

theorem xW_succ (J G : ℝ) (r : ℕ) :
    xW J G (r+1) = xW J G r + J*(2*(r:ℝ)*G^2) := by
  unfold xW
  push_cast
  ring

/-- Exponential potential used by the stopped process. -/
def xPhi (w : WeightedRow.Weights ι) (θ J G : ℝ) (r : ℕ)
    (row : ι → ℕ) : ℝ :=
  Real.exp (θ*xZ w G r row - θ^2*xW J G r /
    (2*(1-θ*J/3)))

theorem xPhi_advance (w : WeightedRow.Weights ι) (θ J G : ℝ) (r : ℕ)
    (row : ι → ℕ) (x : Option ι) :
    xPhi w θ J G (r+1) (advance row x) =
      xPhi w θ J G r row * Real.exp
        (θ*(w.xJump row x-2*(r:ℝ)*G^2) -
          θ^2*(J*(2*(r:ℝ)*G^2))/(2*(1-θ*J/3))) := by
  unfold xPhi
  rw [xZ_advance, xW_succ]
  rw [← Real.exp_add]
  congr 1
  ring

/-- Occupancy cap for a distinguished row, expressed on the actual cache. -/
def OccupancyGood (A : Finset OptimalOTS.Query)
    (decode : BitVec OptimalOTS.hashBits → Option ι) (u : ι → ℕ)
    (cache : OptimalOTS.hashSpec.QueryCache) : Prop :=
  ∀ i, WeightedCacheCounts.classCounts A cache decode i ≤ u i

/-- The compensated self-collision potential is a supermartingale for one
primitive query of the actual memoized oracle, until the occupancy cap fails. -/
theorem actual_xPhi_step (w : WeightedRow.Weights ι)
    (A Gdom : Finset OptimalOTS.Query) (hAG : A ⊆ Gdom)
    (decode : BitVec OptimalOTS.hashBits → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b = x)).card : ℝ) /
      Fintype.card (BitVec OptimalOTS.hashBits) = w.classMass x)
    (u : ι → ℕ) (G θ J : ℝ)
    (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G)
    (hθ : 0 ≤ θ) (hJ : 0 ≤ J) (hθJ : θ*J < 3)
    (hcap : ∀ i, 2*(u i:ℝ)*w.collisionMass i ≤ J)
    (t : OptimalOTS.Spec.Domain) (cache : OptimalOTS.hashSpec.QueryCache)
    (hgood : OccupancyGood A decode u cache) :
    realEval ((OptimalOTS.oracleImpl t).run cache) (fun out =>
      xPhi w θ J G (WeightedCacheCounts.seen A out.2).card
        (WeightedCacheCounts.classCounts A out.2 decode)) ≤
      xPhi w θ J G (WeightedCacheCounts.seen A cache).card
        (WeightedCacheCounts.classCounts A cache decode) := by
  let r := (WeightedCacheCounts.seen A cache).card
  let row := WeightedCacheCounts.classCounts A cache decode
  have hsumNat : (∑ i : ι, row i) ≤ r := by
    exact classCounts_sum_le_seen A cache decode
  have hsum : (∑ i : ι, (row i : ℝ)) ≤ (r : ℝ) := by
    exact_mod_cast hsumNat
  have hmean : w.expect (w.xJump row) ≤ 2*(r:ℝ)*G^2 :=
    w.expect_xJump_le row (r:ℝ) G hG hg hsum
  have hmgf := w.xJump_upper_compensated_mgf_of_cap row u θ J
    (2*(r:ℝ)*G^2) hθ hJ hθJ hgood hcap hmean
  have hlaw := actual_query_law w A Gdom hAG decode hfiber t cache
    (fun r _ row => xPhi w θ J G r row)
  rw [hlaw]
  cases hs : protectedPhase A Gdom t cache with
  | idle =>
      simp only [hs, after, expect_const]
      exact le_rfl
  | outside =>
      simp only [hs, after, expect_const]
      exact le_rfl
  | inside =>
      simp only [hs, after]
      change w.expect (fun x => xPhi w θ J G (r+1) (advance row x)) ≤
        xPhi w θ J G r row
      rw [show (fun x => xPhi w θ J G (r+1) (advance row x)) =
          (fun x => xPhi w θ J G r row * Real.exp
            (θ*(w.xJump row x-2*(r:ℝ)*G^2) -
              θ^2*(J*(2*(r:ℝ)*G^2))/(2*(1-θ*J/3)))) by
        funext x
        exact xPhi_advance w θ J G r row x]
      rw [w.expect_smul]
      have hm := mul_le_mul_of_nonneg_left hmgf
        (Real.exp_nonneg (θ*xZ w G r row - θ^2*xW J G r/(2*(1-θ*J/3))))
      simpa only [xPhi, mul_one] using hm

/-- Cache specialization of the two stopped-process coordinates. -/
def cacheXz (w : WeightedRow.Weights ι) (A : Finset OptimalOTS.Query)
    (decode : BitVec OptimalOTS.hashBits → Option ι) (G : ℝ)
    (cache : OptimalOTS.hashSpec.QueryCache) : ℝ :=
  xZ w G (WeightedCacheCounts.seen A cache).card
    (WeightedCacheCounts.classCounts A cache decode)

def cacheXw (A : Finset OptimalOTS.Query) (J G : ℝ)
    (cache : OptimalOTS.hashSpec.QueryCache) : ℝ :=
  xW J G (WeightedCacheCounts.seen A cache).card

/-- Maximal Freedman bound for the actual oracle execution, stopped before an
occupancy-cap violation.  The theorem chains the one-query cache law through
the real `OracleComp` syntax; no independent-draw execution is substituted. -/
theorem actual_stopped_x_freedman {α : Type}
    (w : WeightedRow.Weights ι)
    (A Gdom : Finset OptimalOTS.Query) (hAG : A ⊆ Gdom)
    (decode : BitVec OptimalOTS.hashBits → Option ι)
    (hfiber : ∀ x, ((Finset.univ.filter (fun b => decode b = x)).card : ℝ) /
      Fintype.card (BitVec OptimalOTS.hashBits) = w.classMass x)
    (u : ι → ℕ) (G J : ℝ)
    (hG : 0 ≤ G) (hg : ∀ i, w.g i ≤ G) (hJ : 0 ≤ J)
    (hcap : ∀ i, 2*(u i:ℝ)*w.collisionMass i ≤ J)
    (oa : OracleComp OptimalOTS.Spec α)
    (initial : OptimalOTS.hashSpec.QueryCache)
    (hr0 : (WeightedCacheCounts.seen A initial).card = 0)
    (hk0 : WeightedCacheCounts.classCounts A initial decode = fun _ => 0)
    (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    let hit := fun (_ : ℕ) (cache : OptimalOTS.hashSpec.QueryCache) =>
      a ≤ cacheXz w A decode G cache ∧ cacheXw A J G cache ≤ v
    let kill := fun (_ : ℕ) (cache : OptimalOTS.hashSpec.QueryCache) =>
      ¬ OccupancyGood A decode u cache
    Pr[fun out => out.2.status = WeightedFirstHit.Status.hit |
      (simulateQ (WeightedOracleExecution.stoppedImpl OptimalOTS.oracleImpl hit kill) oa).run
        (WeightedFirstHit.classify hit kill 0 initial)] ≤
      ENNReal.ofReal (Real.exp (-a^2/(2*(v+J*a/3)))) := by
  dsimp only
  let hit := fun (_ : ℕ) (cache : OptimalOTS.hashSpec.QueryCache) =>
    a ≤ cacheXz w A decode G cache ∧ cacheXw A J G cache ≤ v
  let kill := fun (_ : ℕ) (cache : OptimalOTS.hashSpec.QueryCache) =>
    ¬ OccupancyGood A decode u cache
  apply WeightedOracleExecution.actual_stopped_freedman
    OptimalOTS.oracleImpl oa
    (fun _ cache => cacheXz w A decode G cache)
    (fun _ cache => cacheXw A J G cache)
    initial a v J ha hv hJ
  · unfold cacheXz xZ
    rw [hr0, hk0]
    simp [WeightedRow.Weights.X]
  · simp [cacheXw, xW, hr0]
  · intro θ hθ hθJ t _ cache _ hnotKill
    have hgood : OccupancyGood A decode u cache := by
      exact Classical.not_not.mp hnotKill
    change expectedValue ((OptimalOTS.oracleImpl t).run cache) (fun out =>
      ENNReal.ofReal (xPhi w θ J G (WeightedCacheCounts.seen A out.2).card
        (WeightedCacheCounts.classCounts A out.2 decode))) ≤
      ENNReal.ofReal (xPhi w θ J G (WeightedCacheCounts.seen A cache).card
        (WeightedCacheCounts.classCounts A cache decode))
    calc
      _ = ENNReal.ofReal (realEval ((OptimalOTS.oracleImpl t).run cache) (fun out =>
          xPhi w θ J G (WeightedCacheCounts.seen A out.2).card
            (WeightedCacheCounts.classCounts A out.2 decode))) :=
        (WeightedRealExecution.ofReal_realEval _ _ (fun _ => by
          unfold xPhi
          exact Real.exp_nonneg _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (actual_xPhi_step w A Gdom hAG decode hfiber
        u G θ J hG hg hθ.le hJ hθJ hcap t cache hgood)
  · intro _ _ hh
    exact hh.1
  · intro _ _ hh
    exact hh.2

#print axioms actual_clock_law
#print axioms actual_D_martingale
#print axioms actual_Qfwd_supermartingale
#print axioms actual_xPhi_step
#print axioms actual_stopped_x_freedman

end EqualityCollisionCache91
