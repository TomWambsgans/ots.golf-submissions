import Submissions.UpperCompressions.LongChain91AuthClosure
import Submissions.UpperCompressions.LongChain91CachedRow

/-!
# Authentication game bridge for the cost-91 long-chain construction

This module isolates the two remaining graph-specific obligations behind
small propositions.  Everything after those obligations is ordinary
potential algebra or the accepted-verifier event decomposition.  It also
closes the same-cut, changed-payload route directly from the concrete
long-chain reconstruction walk.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace OptimalOTS.WeightedConstruction.LongChain91

open OptimalOTS.Dag
open Name

/-! ## Generic authentication-potential algebra -/

theorem sumW_mono {T T' : Finset Rec} (h : T ⊆ T') :
    sumW T ≤ sumW T' :=
  Finset.sum_le_sum_of_subset h

theorem ind_or_le (p r : Prop) : ind (p ∨ r) ≤ ind p + ind r := by
  unfold ind
  by_cases hp : p <;> by_cases hr : r <;> simp [hp, hr]

theorem w_mul_ind_le (p : Prop) [Decidable p] :
    w * ind p ≤ if p then w else 0 := by
  unfold ind
  split_ifs <;> simp

theorem sum_w_mul_le_add_charge (delta : ℝ≥0∞) (T : Finset Rec)
    (a b : Rec → ℝ≥0∞) (h : ∀ xi ∈ T, a xi ≤ b xi + delta) :
    ∑ xi ∈ T, w * a xi ≤
      ∑ xi ∈ T, w * b xi + delta * sumW T := by
  unfold sumW
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun xi hxi => ?_
  rw [mul_comm delta w, ← mul_add]
  exact mul_le_mul_right (h xi hxi) w

/-- A fresh answer can create a hit only at the queried point. -/
theorem hits_avg_le (T : Finset Rec) (f : Rec → Cache)
    (c : Cache) (q : Query) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ xi ∈ T, w * ind (Cache.Hits (c.cacheQuery q u) (f xi)) ≤
      ∑ xi ∈ T, w * ind (Cache.Hits c (f xi)) +
        ∑ xi ∈ T, w * ind ((f xi q).isSome) := by
  rw [avg_sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun xi _ => ?_
  rw [← mul_add]
  refine mul_le_mul_right ?_ w
  calc
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
          ind (Cache.Hits (c.cacheQuery q u) (f xi))
        ≤ ∑ _u : BitVec hashBits,
            (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
              (ind (Cache.Hits c (f xi)) + ind ((f xi q).isSome)) := by
          refine Finset.sum_le_sum fun u _ => mul_le_mul_right ?_ _
          rw [ind_congr (Cache.hits_cacheQuery c (f xi) q u)]
          exact ind_or_le _ _
    _ = _ := sum_inv_card_mul _

theorem spr_avg_le (T : Finset Rec) (c : Cache) (q : Query)
    (hq : c q = none) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ xi ∈ T, w * ind (Spr (c.cacheQuery q u) xi) ≤
      ∑ xi ∈ T, w * ind (Spr c xi) +
        (ε * blockCost q.1) * sumW T := by
  rw [avg_sum_comm]
  exact sum_w_mul_le_add_charge (ε * blockCost q.1) T _ _
    (fun xi _ => spr_charge c xi q hq)

/-! The only missing input to the charge algebra is closure of the concrete
record fibers under resampling the coordinate read by a hidden hash input. -/

def InitialHitsCharge : Prop :=
  ∀ (pk : BitVec 128) (q : Query),
    ∑ xi ∈ fiberA pk, (if (kc xi q).isSome then w else 0) ≤
      ε * sumW (fiberA pk)

def SignedHitsCharge : Prop :=
  ∀ (A : Finset Name), IsCut A → ∀ (dt : Data) (q : Query),
    ∑ xi ∈ fiberB A dt,
        (if (fHid (some A) xi q).isSome then w else 0) ≤
      ε * sumW (fiberB A dt)

theorem hits_charge_A'_of (hbase : InitialHitsCharge) (pk : BitVec 128)
    {T : Finset Rec} (hT : T ⊆ fiberA pk) (q : Query) :
    ∑ xi ∈ T, w * ind ((kc xi q).isSome) ≤
      ε * sumW (fiberA pk) := by
  calc
    ∑ xi ∈ T, w * ind ((kc xi q).isSome)
        ≤ ∑ xi ∈ T, (if (kc xi q).isSome then w else 0) :=
          Finset.sum_le_sum fun _ _ => w_mul_ind_le _
    _ ≤ ∑ xi ∈ fiberA pk, (if (kc xi q).isSome then w else 0) :=
      Finset.sum_le_sum_of_subset hT
    _ ≤ ε * sumW (fiberA pk) := hbase pk q

theorem hits_charge_B'_of (hbase : SignedHitsCharge)
    {Ac : Finset Name} (hAc : IsCut Ac) (dt : Data)
    {T : Finset Rec} (hT : T ⊆ fiberB Ac dt) (q : Query) :
    ∑ xi ∈ T, w * ind ((fHid (some Ac) xi q).isSome) ≤
      ε * sumW (fiberB Ac dt) := by
  calc
    ∑ xi ∈ T, w * ind ((fHid (some Ac) xi q).isSome)
        ≤ ∑ xi ∈ T,
            (if (fHid (some Ac) xi q).isSome then w else 0) :=
          Finset.sum_le_sum fun _ _ => w_mul_ind_le _
    _ ≤ ∑ xi ∈ fiberB Ac dt,
        (if (fHid (some Ac) xi q).isSome then w else 0) :=
      Finset.sum_le_sum_of_subset hT
    _ ≤ ε * sumW (fiberB Ac dt) := hbase Ac hAc dt q

theorem authPotential_charge_of (hbase : SignedHitsCharge)
    {Ac : Finset Name} (hAc : IsCut Ac) (dt : Data)
    {T : Finset Rec} (hT : T ⊆ fiberB Ac dt)
    (c : Cache) (q : Query) (hq : c q = none) :
    (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
      authPotential T (some Ac) (c.cacheQuery q u)) ≤
      authPotential T (some Ac) c +
        authRate * sumW (fiberB Ac dt) * queryCost (.inr q) := by
  simp only [authPotential_eq, mul_add, Finset.sum_add_distrib]
  have hh := (hits_avg_le T (fHid (some Ac)) c q).trans
    (add_le_add_right (hits_charge_B'_of hbase hAc dt hT q) _)
  have hs := (spr_avg_le T c q hq).trans
    (add_le_add_right
      (mul_le_mul_right (sumW_mono hT) (ε * blockCost q.1)) _)
  have hc := mul_le_mul_right (authentication_charge_budget q)
    (sumW (fiberB Ac dt))
  calc
    _ ≤ ((∑ xi ∈ T,
          w * ind (Cache.Hits c (fHid (some Ac) xi))) +
          ε * sumW (fiberB Ac dt)) +
        ((∑ xi ∈ T, w * ind (Spr c xi)) +
          (ε * blockCost q.1) * sumW (fiberB Ac dt)) :=
      add_le_add hh hs
    _ = ((∑ xi ∈ T,
          w * ind (Cache.Hits c (fHid (some Ac) xi))) +
          ∑ xi ∈ T, w * ind (Spr c xi)) +
        (ε + ε * blockCost q.1) * sumW (fiberB Ac dt) := by
      ring
    _ ≤ _ := by
      apply add_le_add_right
      simpa only [authRate, queryCost, mul_assoc, mul_comm, mul_left_comm]
        using hc

/-! ## Coordinate resampling -/

/-- The direct chain occupying the low (third) input of upper ternary node
`u`.  Its final hash output supplies the low 129 bits of the upper input. -/
def upperLastChain (u : Fin 10) : Fin 66 :=
  if hu : u.val < 8 then ⟨54 + u.val, by omega⟩
  else ⟨62 + 2 * (u.val - 8) + 1, by omega⟩

theorem midChild_two (u : Fin 10) :
    midChild u 2 = Name.cv (upperLastChain u) 17 := by
  unfold midChild upperLastChain
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega

/-- The independent record coordinate whose low 129 bits determine the low
129 bits of a hash input. -/
def coordOf : Name → Name
  | .ch k t => if h : t.val = 0 then .src k else .ch k ⟨t.val - 1, by omega⟩
  | .sh j => .ch (Name.lowerChain j 2) 17
  | .mh u => .ch (upperLastChain u) 17
  | .rh => .mh 9
  | n => n

def updSrc (xi : Rec) (k : Fin 66) (b : BitVec 129) : Rec :=
  (Function.update xi.1 (Name.src k).fin
    (b.cast (graph_len_fin (Name.src k)).symm), xi.2)

def updHash (xi : Rec) (s : Name) (b : BitVec 256) : Rec :=
  (xi.1, Function.update xi.2 s.fin b)

theorem updHash_snd_self (xi : Rec) (s : Name) (b : BitVec 256) :
    (updHash xi s b).2 s.fin = b :=
  Function.update_self _ _ _

theorem updHash_snd_ne (xi : Rec) (s : Name) (b : BitVec 256)
    {n : Name} (h : n ≠ s) : (updHash xi s b).2 n.fin = xi.2 n.fin := by
  simp only [updHash]
  exact Function.update_of_ne (fun e => h (Name.fin_injective e)) _ _

theorem updSrc_snd (xi : Rec) (k : Fin 66) (b : BitVec 129) :
    (updSrc xi k b).2 = xi.2 := rfl

theorem updSrc_fst_self (xi : Rec) (k : Fin 66) (b : BitVec 129) :
    (updSrc xi k b).1 (Name.src k).fin =
      b.cast (graph_len_fin (Name.src k)).symm :=
  Function.update_self _ _ _

theorem val_updSrc_self (xi : Rec) (k : Fin 66) (b : BitVec 129) :
    val (updSrc xi k b) (Name.src k) = b := by
  rw [val_src, updSrc_fst_self]
  exact cast_cast_eq _ _ _

theorem coordOf_ne_rh (h : Name) (hh : h.cost ≠ 0) : coordOf h ≠ Name.rh := by
  cases h <;> simp_all [Name.cost, coordOf] <;> split_ifs <;> simp

theorem lowWord_cat3_game (x y z : BitVec 129) :
    lowWord (cat3 x y z) = z := by
  unfold cat3
  rw [lowWord_cast]
  unfold lowWord
  rw [BitVec.setWidth_append, dif_pos le_rfl, BitVec.setWidth_eq]

theorem lowWord_cat10_game (a : Fin 10 → BitVec 129) :
    lowWord (cat10 a) = a 9 := by
  unfold cat10
  rw [lowWord_cast]
  unfold lowWord
  rw [BitVec.setWidth_append, dif_pos le_rfl, BitVec.setWidth_eq]

theorem lowWord_tw_append_game {n : ℕ} (hn : 129 ≤ n)
    (a : BitVec 16) (x : BitVec n) : lowWord (a ++ x) = lowWord x := by
  unfold lowWord
  rw [BitVec.setWidth_append, dif_pos hn]

theorem lowWord_of_tw_eq_game {a : BitVec 16} {x : BitVec 129}
    {u : BitVec 145} (e : a ++ x = u) : lowWord u = x := by
  subst u
  exact (lowWord_tw_append_game le_rfl a x).trans (lowWord_eq_self x)

theorem lowWord_of_tw_cat3_eq_game {a : BitVec 16}
    {x y z : BitVec 129} {u : BitVec 403}
    (e : a ++ cat3 x y z = u) : lowWord u = z := by
  subst u
  exact (lowWord_tw_append_game (n := 387) (by norm_num) a _).trans
    (lowWord_cat3_game x y z)

theorem lowWord_of_tw_cat10_eq_game {a : BitVec 16}
    {b : Fin 10 → BitVec 129} {u : BitVec 1306}
    (e : a ++ cat10 b = u) : lowWord u = b 9 := by
  subst u
  exact (lowWord_tw_append_game (n := 1290) (by norm_num) a _).trans
    (lowWord_cat10_game b)

theorem card_filter_le_of_imp_game (p : BitVec 256 → Prop)
    [DecidablePred p] (a : BitVec 129)
    (hp : ∀ b, p b → lowWord b = a) :
    (Finset.univ.filter p).card ≤ 2 ^ 127 :=
  le_trans (Finset.card_le_card fun b hb => Finset.mem_filter.2
    ⟨Finset.mem_univ _, hp b (Finset.mem_filter.1 hb).2⟩)
    (WideForest.card_filter_lowWord_le a)

/-- Resampling `coordOf h` leaves at most 127 unconstrained answer bits in a
fixed input to hash node `h`. -/
theorem card_updHash_input_le {h p : Name}
    (hp : hashParent h = some p) (xi : Rec)
    (hs : ∀ k, coordOf h ≠ Name.src k) (u : BitVec p.len) :
    (Finset.univ.filter fun b : BitVec 256 =>
      val (updHash xi (coordOf h) b) p = u).card ≤ 2 ^ 127 := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    subst hp
  · rename_i k t
    have ht : ¬ t.val = 0 := fun ht => hs k (by simp [coordOf, ht])
    have hc : coordOf (Name.ch k t) =
        Name.ch k ⟨t.val - 1, by omega⟩ := by simp [coordOf, ht]
    rw [hc]
    refine card_filter_le_of_imp_game _ (lowWord u) fun b hb => ?_
    rw [val_ci] at hb
    have hz := lowWord_of_tw_eq_game hb
    have hprev : prev k t = Name.cv k ⟨t.val - 1, by omega⟩ := by
      simp [prev, ht]
    rw [hprev, val_cv, updHash_snd_self] at hz
    exact (lowWord_lowWord b).symm.trans hz.symm
  · rename_i j
    refine card_filter_le_of_imp_game _ (lowWord u) fun b hb => ?_
    rw [val_sc] at hb
    have hz := lowWord_of_tw_cat3_eq_game hb
    simp [coordOf, updHash_snd_self, lowWord_lowWord] at hz
    exact hz.symm
  · rename_i uidx
    refine card_filter_le_of_imp_game _ (lowWord u) fun b hb => ?_
    rw [val_mc] at hb
    have hz := lowWord_of_tw_cat3_eq_game hb
    rw [midChild_two, val_cv] at hz
    simp [coordOf, updHash_snd_self, lowWord_lowWord] at hz
    exact hz.symm
  · refine card_filter_le_of_imp_game _ (lowWord u) fun b hb => ?_
    rw [val_rc] at hb
    have hz := lowWord_of_tw_cat10_eq_game hb
    simp [coordOf, updHash_snd_self, lowWord_lowWord] at hz
    exact hz.symm

theorem card_updSrc_input_le {h p : Name}
    (hp : hashParent h = some p) (xi : Rec) {k : Fin 66}
    (hs : coordOf h = Name.src k) (u : BitVec p.len) :
    (Finset.univ.filter fun b : BitVec 129 =>
      val (updSrc xi k b) p = u).card ≤ 1 := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    subst hp <;> simp only [coordOf] at hs
  · rename_i k' t
    by_cases ht : t.val = 0
    · rw [dif_pos ht] at hs
      obtain rfl : k = k' := (Name.src.inj hs).symm
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      have hprev : prev k t = Name.src k := by simp [prev, ht]
      rw [val_ci] at ha hb
      rw [hprev, val_updSrc_self] at ha hb
      have he := (bv_append_inj (ha.trans hb.symm)).2
      exact eq_of_lowWord_eq rfl he
    · rw [dif_neg ht] at hs
      exact absurd hs (by simp)
  all_goals exact absurd hs (by simp)

/-! ## Closed record fibers and the initial charge -/

def ClosedAt (S : Finset Rec) (s : Name) : Prop :=
  match s with
  | .src k => ∀ xi ∈ S, ∀ b : BitVec 129, updSrc xi k b ∈ S
  | _ => ∀ xi ∈ S, ∀ b : BitVec 256, updHash xi s b ∈ S

theorem closedAt_src (S : Finset Rec) (k : Fin 66) :
    ClosedAt S (Name.src k) ↔
      ∀ xi ∈ S, ∀ b : BitVec 129, updSrc xi k b ∈ S := by
  rfl

theorem closedAt_of_ne_src (S : Finset Rec) {s : Name}
    (hs : ∀ k, s ≠ Name.src k) :
    ClosedAt S s ↔
      ∀ xi ∈ S, ∀ b : BitVec 256, updHash xi s b ∈ S := by
  cases s <;> simp_all [ClosedAt]

theorem bv_cast_cast_game {n m : ℕ} (h₁ : n = m) (h₂ : m = n)
    (x : BitVec n) : (x.cast h₁).cast h₂ = x := by
  subst m
  rfl

theorem updHash_updHash (xi : Rec) (s : Name) (b : BitVec 256) :
    updHash (updHash xi s b) s (xi.2 s.fin) = xi :=
  Prod.ext rfl (funext fun v => by
    show Function.update (Function.update xi.2 s.fin b) s.fin
      (xi.2 s.fin) v = xi.2 v
    by_cases hv : v = s.fin
    · subst hv
      exact Function.update_self ..
    · exact (Function.update_of_ne hv _ _).trans
        (Function.update_of_ne hv _ _))

theorem updSrc_updSrc (xi : Rec) (k : Fin 66) (b : BitVec 129) :
    updSrc (updSrc xi k b) k
      ((xi.1 (Name.src k).fin).cast (graph_len_fin _)) = xi :=
  Prod.ext (funext fun v => by
    show Function.update
      (Function.update xi.1 (Name.src k).fin (b.cast _))
      (Name.src k).fin
      (((xi.1 (Name.src k).fin).cast (graph_len_fin _)).cast
        (graph_len_fin _).symm) v = xi.1 v
    by_cases hv : v = (Name.src k).fin
    · subst hv
      exact (Function.update_self ..).trans (bv_cast_cast_game _ _ _)
    · exact (Function.update_of_ne hv _ _).trans
        (Function.update_of_ne hv _ _)) rfl

theorem fst_updSrc_self (xi : Rec) (k : Fin 66) (b : BitVec 129) :
    ((updSrc xi k b).1 (Name.src k).fin).cast (graph_len_fin _) = b := by
  rw [updSrc_fst_self]
  exact bv_cast_cast_game _ _ _

theorem sum_updHash (S : Finset Rec) (s : Name)
    (_hs : ∀ k, s ≠ Name.src k)
    (hS : ∀ xi ∈ S, ∀ b : BitVec 256, updHash xi s b ∈ S)
    (f : Rec → ℝ≥0∞) :
    ∑ xi ∈ S, f xi = ∑ xi ∈ S,
      (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
        ∑ b, f (updHash xi s b) := by
  have key : ∑ xi ∈ S, ∑ b, f (updHash xi s b) =
      ∑ xi ∈ S, ∑ _b : BitVec 256, f xi := by
    calc
      ∑ xi ∈ S, ∑ b, f (updHash xi s b) =
          ∑ p ∈ S ×ˢ (Finset.univ : Finset (BitVec 256)),
            f (updHash p.1 s p.2) :=
        (Finset.sum_product' S Finset.univ
          (fun xi b => f (updHash xi s b))).symm
      _ = ∑ p ∈ S ×ˢ (Finset.univ : Finset (BitVec 256)), f p.1 := by
        refine Finset.sum_nbij'
          (fun p => (updHash p.1 s p.2, p.1.2 s.fin))
          (fun p => (updHash p.1 s p.2, p.1.2 s.fin)) ?_ ?_ ?_ ?_ ?_
        · intro p hp
          rw [Finset.mem_product] at hp ⊢
          exact ⟨hS _ hp.1 _, Finset.mem_univ _⟩
        · intro p hp
          rw [Finset.mem_product] at hp ⊢
          exact ⟨hS _ hp.1 _, Finset.mem_univ _⟩
        · intro p _
          exact Prod.ext (updHash_updHash _ _ _) (updHash_snd_self _ _ _)
        · intro p _
          exact Prod.ext (updHash_updHash _ _ _) (updHash_snd_self _ _ _)
        · intro p _
          rfl
      _ = ∑ xi ∈ S, ∑ _b : BitVec 256, f xi :=
        Finset.sum_product' S Finset.univ (fun xi _ => f xi)
  have hc0 : (Fintype.card (BitVec 256) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hct : (Fintype.card (BitVec 256) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  rw [← Finset.mul_sum, key]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← mul_assoc,
    ENNReal.inv_mul_cancel hc0 hct, one_mul]

theorem sum_updSrc (S : Finset Rec) (k : Fin 66)
    (hS : ∀ xi ∈ S, ∀ b : BitVec 129, updSrc xi k b ∈ S)
    (f : Rec → ℝ≥0∞) :
    ∑ xi ∈ S, f xi = ∑ xi ∈ S,
      (Fintype.card (BitVec 129) : ℝ≥0∞)⁻¹ *
        ∑ b, f (updSrc xi k b) := by
  have key : ∑ xi ∈ S, ∑ b, f (updSrc xi k b) =
      ∑ xi ∈ S, ∑ _b : BitVec 129, f xi := by
    calc
      ∑ xi ∈ S, ∑ b, f (updSrc xi k b) =
          ∑ p ∈ S ×ˢ (Finset.univ : Finset (BitVec 129)),
            f (updSrc p.1 k p.2) :=
        (Finset.sum_product' S Finset.univ
          (fun xi b => f (updSrc xi k b))).symm
      _ = ∑ p ∈ S ×ˢ (Finset.univ : Finset (BitVec 129)), f p.1 := by
        refine Finset.sum_nbij'
          (fun p => (updSrc p.1 k p.2,
            (p.1.1 (Name.src k).fin).cast (graph_len_fin _)))
          (fun p => (updSrc p.1 k p.2,
            (p.1.1 (Name.src k).fin).cast (graph_len_fin _))) ?_ ?_ ?_ ?_ ?_
        · intro p hp
          rw [Finset.mem_product] at hp ⊢
          exact ⟨hS _ hp.1 _, Finset.mem_univ _⟩
        · intro p hp
          rw [Finset.mem_product] at hp ⊢
          exact ⟨hS _ hp.1 _, Finset.mem_univ _⟩
        · intro p _
          exact Prod.ext (updSrc_updSrc _ _ _) (fst_updSrc_self _ _ _)
        · intro p _
          exact Prod.ext (updSrc_updSrc _ _ _) (fst_updSrc_self _ _ _)
        · intro p _
          rfl
      _ = ∑ xi ∈ S, ∑ _b : BitVec 129, f xi :=
        Finset.sum_product' S Finset.univ (fun xi _ => f xi)
  have hc0 : (Fintype.card (BitVec 129) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hct : (Fintype.card (BitVec 129) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  rw [← Finset.mul_sum, key]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← mul_assoc,
    ENNReal.inv_mul_cancel hc0 hct, one_mul]

theorem card_bitVec_ennreal_game (n : ℕ) :
    (Fintype.card (BitVec n) : ℝ≥0∞) = 2 ^ n := by simp

theorem sum_input_eq_le {h p : Name} (hp : hashParent h = some p)
    (S : Finset Rec) (hS : ClosedAt S (coordOf h))
    (u : BitVec p.len) :
    ∑ xi ∈ S, (if val xi p = u then w else 0) ≤
      ε * ∑ _xi ∈ S, w := by
  rw [Finset.mul_sum]
  by_cases hsrc : ∃ k, coordOf h = Name.src k
  · obtain ⟨k, hk⟩ := hsrc
    rw [hk, closedAt_src] at hS
    rw [sum_updSrc S k hS
      (fun xi => if val xi p = u then w else 0)]
    refine Finset.sum_le_sum fun xi _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hle := card_updSrc_input_le hp xi hk u
    have hle' : ((Finset.univ.filter fun b : BitVec 129 =>
        val (updSrc xi k b) p = u).card : ℝ≥0∞) ≤ 1 := by
      exact_mod_cast hle
    calc
      (Fintype.card (BitVec 129) : ℝ≥0∞)⁻¹ *
          (((Finset.univ.filter fun b : BitVec 129 =>
            val (updSrc xi k b) p = u).card : ℝ≥0∞) * w)
          ≤ (Fintype.card (BitVec 129) : ℝ≥0∞)⁻¹ * (1 * w) := by
            gcongr
      _ = ε * w := by
        rw [one_mul, card_bitVec_ennreal_game, ε]
  · push Not at hsrc
    rw [closedAt_of_ne_src S hsrc] at hS
    rw [sum_updHash S (coordOf h) hsrc hS
      (fun xi => if val xi p = u then w else 0)]
    refine Finset.sum_le_sum fun xi _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hle := card_updHash_input_le hp xi hsrc u
    have hle' : ((Finset.univ.filter fun b : BitVec 256 =>
        val (updHash xi (coordOf h) b) p = u).card : ℝ≥0∞) ≤
          2 ^ 127 := by
      exact_mod_cast hle
    calc
      (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
          (((Finset.univ.filter fun b : BitVec 256 =>
            val (updHash xi (coordOf h) b) p = u).card : ℝ≥0∞) * w)
          ≤ (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
            (2 ^ 127 * w) := by
              gcongr
      _ = ε * w := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc] using
          congrArg (fun z : ℝ≥0∞ => z * w) inv_card_bitVec_mul_two_pow

theorem pkOf_updHash (xi : Rec) {s : Name} (hs : s ≠ Name.rh)
    (b : BitVec 256) : pkOf (updHash xi s b) = pkOf xi := by
  exact congrArg lowPk (updHash_snd_ne xi s b (Ne.symm hs))

theorem pkOf_updSrc (xi : Rec) (k : Fin 66) (b : BitVec 129) :
    pkOf (updSrc xi k b) = pkOf xi := by
  unfold pkOf
  rw [updSrc_snd]

theorem fiberA_closedAt (pk : BitVec 128) {s : Name}
    (hs : s ≠ Name.rh) : ClosedAt (fiberA pk) s := by
  by_cases hsrc : ∃ k, s = Name.src k
  · obtain ⟨k, rfl⟩ := hsrc
    rw [closedAt_src]
    simp only [fiberA, Finset.mem_filter, Finset.mem_univ, true_and]
    intro xi hxi b
    rw [pkOf_updSrc]
    exact hxi
  · push Not at hsrc
    rw [closedAt_of_ne_src _ hsrc]
    simp only [fiberA, Finset.mem_filter, Finset.mem_univ, true_and]
    intro xi hxi b
    rw [pkOf_updHash _ hs]
    exact hxi

/-- The concrete pre-sign fiber satisfies the raw hidden-input charge. -/
theorem initialHitsCharge : InitialHitsCharge := by
  intro pk q
  by_cases hex : ∃ h p, hashParent h = some p ∧
      ∃ xi₀ : Rec, q = pointOf xi₀ h p
  · obtain ⟨h, p, hp, xi₀, rfl⟩ := hex
    have key : ∀ xi : Rec,
        (kc xi (pointOf xi₀ h p)).isSome ↔ val xi p = val xi₀ p := by
      intro xi
      rw [kc_isSome_iff]
      constructor
      · rintro ⟨h', p', hp', e⟩
        obtain rfl := pointOf_inj_left hp hp' e
        rw [hp] at hp'
        obtain rfl := Option.some.inj hp'
        exact (pointOf_inj_input e).symm
      · intro hv
        exact ⟨h, p, hp, by simp only [pointOf, hv]⟩
    have hcost : h.cost ≠ 0 := cost_ne_zero_of_hashParent hp
    calc
      ∑ xi ∈ fiberA pk,
          (if (kc xi (pointOf xi₀ h p)).isSome then w else 0) =
          ∑ xi ∈ fiberA pk, (if val xi p = val xi₀ p then w else 0) := by
        refine Finset.sum_congr rfl fun xi _ => ?_
        by_cases hv : val xi p = val xi₀ p <;> simp [key, hv]
      _ ≤ _ := sum_input_eq_le hp _
        (fiberA_closedAt pk (coordOf_ne_rh h hcost)) _
  · have hz : ∀ xi : Rec, ¬ (kc xi q).isSome := by
      intro xi hk
      rw [kc_isSome_iff] at hk
      obtain ⟨h, p, hp, e⟩ := hk
      exact hex ⟨h, p, hp, xi, e⟩
    have hsum : ∑ xi ∈ fiberA pk,
        (if (kc xi q).isSome then w else 0) = 0 :=
      Finset.sum_eq_zero fun xi _ => if_neg (hz xi)
    exact hsum.le.trans _root_.zero_le

/-! ## Locality of record coordinates -/

/-- The independent record coordinate directly underlying a 129-bit value
node.  The fallback cases are irrelevant to the locality lemmas. -/
def valueCoord : Name → Name
  | .src k => .src k
  | .cv k t => .ch k t
  | .sv j => .sh j
  | .mv u => .mh u
  | n => n

/-- The hash-output node directly underlying a non-source value node. -/
def hashOf : Name → Option Name
  | .cv k t => some (.ch k t)
  | .sv j => some (.sh j)
  | .mv u => some (.mh u)
  | _ => none

theorem child_hashOf {v h : Name} (hh : hashOf v = some h) :
    child h = some v := by
  cases v <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;>
    subst h <;> rfl

theorem hashOf_midChild (u : Fin 10) (a : Fin 3) :
    hashOf (midChild u a) = some (valueCoord (midChild u a)) := by
  unfold midChild
  split_ifs <;> rfl

/-- Record coordinates read by the honest value at a node. -/
def deps : Name → Finset Name
  | .src k => {.src k}
  | .ci k t =>
      if h : t.val = 0 then {.src k}
      else {.ch k ⟨t.val - 1, by omega⟩}
  | .ch k t => {.ch k t}
  | .cv k t => {.ch k t}
  | .sc j =>
      {.ch (Name.lowerChain j 0) 17,
       .ch (Name.lowerChain j 1) 17,
       .ch (Name.lowerChain j 2) 17}
  | .sh j => {.sh j}
  | .sv j => {.sh j}
  | .mc u =>
      {valueCoord (midChild u 0), valueCoord (midChild u 1),
       valueCoord (midChild u 2)}
  | .mh u => {.mh u}
  | .mv u => {.mh u}
  | .rc => Finset.univ.image Name.mh
  | .rh => {.rh}

theorem deps_ci_zero (k : Fin 66) (t : Fin 18) (ht : t.val = 0) :
    deps (Name.ci k t) = {Name.src k} := by
  simp [deps, ht]

theorem deps_ci_succ (k : Fin 66) (t : Fin 18) (ht : ¬ t.val = 0) :
    deps (Name.ci k t) = {Name.ch k ⟨t.val - 1, by omega⟩} := by
  simp [deps, ht]

theorem val_updHash_value {xi : Rec} {s v : Name} (b : BitVec 256)
    (hv : v.len = 129) (hs : s ≠ valueCoord v) :
    val (updHash xi s b) v = val xi v := by
  cases v with
  | src k => rw [val_src, val_src]; rfl
  | cv k t =>
      rw [val_cv, val_cv, updHash_snd_ne _ _ _]
      exact Ne.symm hs
  | sv j =>
      rw [val_sv, val_sv, updHash_snd_ne _ _ _]
      exact Ne.symm hs
  | mv u =>
      rw [val_mv, val_mv, updHash_snd_ne _ _ _]
      exact Ne.symm hs
  | ci k t | ch k t | sc k | sh k | mc k | mh k | rc | rh =>
      simp [Name.len] at hv

theorem val_updSrc_src_of_ne (xi : Rec) (k : Fin 66) (b : BitVec 129)
    {k' : Fin 66} (h : k ≠ k') :
    val (updSrc xi k b) (Name.src k') = val xi (Name.src k') := by
  have he : (updSrc xi k b).1 (Name.src k').fin =
      xi.1 (Name.src k').fin :=
    Function.update_of_ne
      (fun e => h (Name.src.inj (Name.fin_injective e)).symm) _ _
  rw [val_src, val_src, he]

theorem val_updSrc_midChild (xi : Rec) (k : Fin 66) (b : BitVec 129)
    (u : Fin 10) (a : Fin 3) :
    val (updSrc xi k b) (midChild u a) = val xi (midChild u a) := by
  have hh := hashOf_midChild u a
  generalize hn : midChild u a = n at hh ⊢
  cases n <;> simp_all [hashOf, val_cv, val_sv, val_mv, updSrc_snd] <;> rfl

theorem val_updHash_of_not_mem_deps (xi : Rec) (s : Name)
    (b : BitVec 256) (n : Name) (h : s ∉ deps n) :
    val (updHash xi s b) n = val xi n := by
  cases n with
  | src k => rw [val_src, val_src]; rfl
  | ci k t =>
      by_cases ht : t.val = 0
      · have hprev : prev k t = Name.src k := by simp [prev, ht]
        rw [val_ci, val_ci, hprev]
        exact congrArg (fun z => tw (Name.ch k t) ++ lowWord z)
          (val_updHash_value b rfl (by
            rw [deps_ci_zero k t ht, Finset.mem_singleton] at h
            simpa [valueCoord] using h))
      · rw [deps_ci_succ k t ht, Finset.mem_singleton] at h
        have hprev : prev k t = Name.cv k ⟨t.val - 1, by omega⟩ := by
          simp [prev, ht]
        rw [val_ci, val_ci, hprev]
        exact congrArg (fun z => tw (Name.ch k t) ++ lowWord z)
          (val_updHash_value b rfl (by simpa [valueCoord] using h))
  | ch k t =>
      simp only [deps, Finset.mem_singleton] at h
      rw [val_ch, val_ch, updHash_snd_ne _ _ _ (Ne.symm h)]
  | cv k t =>
      simp only [deps, Finset.mem_singleton] at h
      rw [val_cv, val_cv, updHash_snd_ne _ _ _ (Ne.symm h)]
  | sc j =>
      simp only [deps, Finset.mem_insert, Finset.mem_singleton, not_or] at h
      obtain ⟨h0, h1, h2⟩ := h
      rw [val_sc, val_sc,
        updHash_snd_ne _ _ _ (Ne.symm h0),
        updHash_snd_ne _ _ _ (Ne.symm h1),
        updHash_snd_ne _ _ _ (Ne.symm h2)]
  | sh j =>
      simp only [deps, Finset.mem_singleton] at h
      rw [val_sh, val_sh, updHash_snd_ne _ _ _ (Ne.symm h)]
  | sv j =>
      simp only [deps, Finset.mem_singleton] at h
      rw [val_sv, val_sv, updHash_snd_ne _ _ _ (Ne.symm h)]
  | mc u =>
      simp only [deps, Finset.mem_insert, Finset.mem_singleton, not_or] at h
      obtain ⟨h0, h1, h2⟩ := h
      rw [val_mc, val_mc,
        val_updHash_value b (midChild_len u 0) h0,
        val_updHash_value b (midChild_len u 1) h1,
        val_updHash_value b (midChild_len u 2) h2]
  | mh u =>
      simp only [deps, Finset.mem_singleton] at h
      rw [val_mh, val_mh, updHash_snd_ne _ _ _ (Ne.symm h)]
  | mv u =>
      simp only [deps, Finset.mem_singleton] at h
      rw [val_mv, val_mv, updHash_snd_ne _ _ _ (Ne.symm h)]
  | rc =>
      simp only [deps, Finset.mem_image, Finset.mem_univ, true_and,
        not_exists] at h
      rw [val_rc, val_rc]
      exact congrArg (fun a => tw Name.rh ++ cat10 a)
        (funext fun u => by rw [updHash_snd_ne _ _ _ (h u)])
  | rh =>
      simp only [deps, Finset.mem_singleton] at h
      rw [val_rh, val_rh, updHash_snd_ne _ _ _ (Ne.symm h)]

theorem val_updSrc_of_not_mem_deps (xi : Rec) (k : Fin 66)
    (b : BitVec 129) (n : Name) (h : Name.src k ∉ deps n) :
    val (updSrc xi k b) n = val xi n := by
  cases n with
  | src k' =>
      simp only [deps, Finset.mem_singleton, Name.src.injEq] at h
      exact val_updSrc_src_of_ne xi k b h
  | ci k' t =>
      by_cases ht : t.val = 0
      · rw [deps_ci_zero k' t ht, Finset.mem_singleton,
          Name.src.injEq] at h
        have hprev : prev k' t = Name.src k' := by simp [prev, ht]
        rw [val_ci, val_ci, hprev]
        exact congrArg (fun z => tw (Name.ch k' t) ++ lowWord z)
          (val_updSrc_src_of_ne xi k b h)
      · have hprev : prev k' t = Name.cv k' ⟨t.val - 1, by omega⟩ := by
          simp [prev, ht]
        rw [val_ci, val_ci, hprev]
        exact congrArg (fun z => tw (Name.ch k' t) ++ lowWord z)
          (by rw [val_cv, val_cv, updSrc_snd])
  | ch k' t => rw [val_ch, val_ch, updSrc_snd]
  | cv k' t => rw [val_cv, val_cv, updSrc_snd]
  | sc j => rw [val_sc, val_sc, updSrc_snd]
  | sh j => rw [val_sh, val_sh, updSrc_snd]
  | sv j => rw [val_sv, val_sv, updSrc_snd]
  | mc u =>
      rw [val_mc, val_mc, val_updSrc_midChild, val_updSrc_midChild,
        val_updSrc_midChild]
  | mh u => rw [val_mh, val_mh, updSrc_snd]
  | mv u => rw [val_mv, val_mv, updSrc_snd]
  | rc => rw [val_rc, val_rc, updSrc_snd]
  | rh => rw [val_rh, val_rh, updSrc_snd]

/-! ## Cut antichains in the concrete one-child graph -/

/-- All nodes on the unique source-to-root branch of `k`, including the
deterministic and hash nodes omitted by `OnPath`. -/
def Branch (k : Fin 66) : Name → Prop
  | .src k' | .ci k' _ | .ch k' _ | .cv k' _ => k' = k
  | .sc j | .sh j | .sv j => lowerOfChain k = some j
  | .mc u | .mh u | .mv u => upperOfChain k = u
  | .rc | .rh => True

theorem branch_child {k : Fin 66} {n p : Name}
    (hn : Branch k n) (hc : child n = some p) : Branch k p := by
  cases n with
  | src k' =>
      simp only [Branch] at hn
      subst k'
      simp only [Name.child, Option.some.injEq] at hc
      subst p
      rfl
  | ci k' t =>
      simp only [Branch] at hn
      subst k'
      simp only [Name.child, Option.some.injEq] at hc
      subst p
      rfl
  | ch k' t =>
      simp only [Branch] at hn
      subst k'
      simp only [Name.child, Option.some.injEq] at hc
      subst p
      rfl
  | cv k' t =>
      simp only [Branch] at hn
      subst k'
      simp only [Name.child] at hc
      split_ifs at hc with ht
      · cases hl : lowerOfChain k with
        | none =>
            simp only [hl, Option.some.injEq] at hc
            subst p
            rfl
        | some j =>
            simp only [hl, Option.some.injEq] at hc
            subst p
            exact hl
      · simp only [Option.some.injEq] at hc
        subst p
        rfl
  | sc j =>
      simp only [Branch] at hn
      simp only [Name.child, Option.some.injEq] at hc
      subst p
      exact hn
  | sh j =>
      simp only [Branch] at hn
      simp only [Name.child, Option.some.injEq] at hc
      subst p
      exact hn
  | sv j =>
      simp only [Branch] at hn
      simp only [Name.child, Option.some.injEq] at hc
      subst p
      exact upperOfChain_eq_upperOfLower hn
  | mc u =>
      simp only [Branch] at hn
      simp only [Name.child, Option.some.injEq] at hc
      subst p
      exact hn
  | mh u =>
      simp only [Branch] at hn
      simp only [Name.child, Option.some.injEq] at hc
      subst p
      exact hn
  | mv u =>
      simp only [Name.child, Option.some.injEq] at hc
      subst p
      trivial
  | rc =>
      simp only [Name.child, Option.some.injEq] at hc
      subst p
      trivial
  | rh => simp [Name.child] at hc

theorem branch_above {k : Fin 66} {m n : Name}
    (hn : Branch k n) (h : Above m n) : Branch k m := by
  induction h with
  | child hc => exact branch_child hn hc
  | step hc _ ih => exact ih (branch_child hn hc)

theorem onPath_iff_branch_of_len {k : Fin 66} {n : Name}
    (hn : n.len = 129) : OnPath k n ↔ Branch k n := by
  cases n <;> simp_all [OnPath, Branch, Name.len, eq_comm]

theorem upperOfChain_surjective (u : Fin 10) :
    ∃ k : Fin 66, upperOfChain k = u := by
  by_cases hu : u.val < 9
  · refine ⟨⟨54 + u.val, by omega⟩, ?_⟩
    apply Fin.ext
    unfold upperOfChain
    simp only [Fin.val_mk]
    split_ifs
    · omega
    · change 54 + u.val - 54 = u.val
      omega
    · change 8 = u.val
      omega
    · omega
  · have hu9 : u.val = 9 := by omega
    refine ⟨64, ?_⟩
    apply Fin.ext
    simp [upperOfChain, hu9]

theorem exists_onPath_of_len129 {n : Name} (hn : n.len = 129) :
    ∃ k : Fin 66, OnPath k n := by
  cases n with
  | src k => exact ⟨k, by simp [OnPath]⟩
  | cv k t => exact ⟨k, by simp [OnPath]⟩
  | sv j =>
      have hj := j.isLt
      refine ⟨Name.lowerChain j 0, ?_⟩
      simp [OnPath, Name.lowerChain, lowerOfChain]
      omega
  | mv u =>
      obtain ⟨k, hk⟩ := upperOfChain_surjective u
      exact ⟨k, (onPath_mv_iff k u).2 hk.symm⟩
  | ci k t | ch k t | sc k | sh k | mc k | mh k | rc | rh =>
      simp [Name.len] at hn

theorem height_lt_of_above {m n : Name} (h : Above m n) :
    height m < height n := by
  induction h with
  | child hc =>
      have hh := height_child hc
      omega
  | step hc _ ih =>
      have hh := height_child hc
      omega

/-- The source-path uniqueness field of `IsCut` implies the usual tree
antichain statement needed by the authentication walk. -/
theorem cut_mem_clearAbove {A : Finset Name} (hA : IsCut A)
    {a : Name} (ha : a ∈ A) : ∀ m, Above m a → m ∉ A := by
  have halen : a.len = 129 := hA.values a ha
  obtain ⟨k, hka⟩ := exists_onPath_of_len129 halen
  intro m hma hmA
  have hmlen : m.len = 129 := hA.values m hmA
  have hba : Branch k a := (onPath_iff_branch_of_len halen).1 hka
  have hbm : Branch k m := branch_above hba hma
  have hkm : OnPath k m := (onPath_iff_branch_of_len hmlen).2 hbm
  have heq : m = a := hA.unique_on_path k a ha hka m hmA hkm
  subst m
  have hlt := height_lt_of_above hma
  omega

/-! ## Hidden-coordinate locality after signing -/

def HiddenCoord (A : Finset Name) (s : Name) : Prop :=
  ¬ Evaluated A s ∧ s ∉ A ∧
    ∀ a ∈ A, hashOf a ≠ some s

theorem len_of_hashParent {h p : Name} (hp : hashParent h = some p) :
    h.len = 256 := by
  cases h <;> simp_all [hashParent, Name.len]

theorem child_upperLastChain (u : Fin 10) :
    child (Name.cv (upperLastChain u) 17) = some (Name.mc u) := by
  rw [← midChild_two u]
  exact child_midChild u 2

theorem coordOf_below {h p : Name} (hp : hashParent h = some p) :
    child (coordOf h) = some p ∨
      ∃ m, child (coordOf h) = some m ∧ child m = some p := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    subst hp
  · rename_i k t
    simp only [coordOf]
    split_ifs with ht
    · have ht' : t = 0 := Fin.ext ht
      subst t
      exact Or.inl rfl
    · have hc := child_prev k t
      have hprev : prev k t = Name.cv k ⟨t.val - 1, by omega⟩ := by
        simp [prev, ht]
      rw [hprev] at hc
      exact Or.inr ⟨Name.cv k ⟨t.val - 1, by omega⟩, rfl, hc⟩
  · rename_i j
    exact Or.inr ⟨Name.cv (Name.lowerChain j 2) 17, rfl,
      child_lowerChain j 2⟩
  · rename_i u
    exact Or.inr ⟨Name.cv (upperLastChain u) 17, rfl,
      child_upperLastChain u⟩
  · exact Or.inr ⟨Name.mv 9, rfl, rfl⟩

theorem above_coordOf {h p : Name} (hp : hashParent h = some p) :
    Above h (coordOf h) := by
  have hc := child_hashParent hp
  rcases coordOf_below hp with e | ⟨m, e₁, e₂⟩
  · exact Above.step e (Above.child hc)
  · exact Above.step e₁ (Above.step e₂ (Above.child hc))

theorem evaluated_of_child_res {A : Finset Name} {s n : Name}
    (hc : child s = some n) (hsA : s ∉ A)
    (hn : Evaluated A n) : Evaluated A s := by
  apply (clearEvaluated_iff A s).1
  have hnC := (clearEvaluated_iff A n).2 hn
  refine ⟨hsA, fun m hm => ?_⟩
  rw [above_of_child hc] at hm
  rcases hm with rfl | hm
  · exact hnC.1
  · exact hnC.2 m hm

theorem coordOf_hiddenCoord {A : Finset Name} (hA : IsCut A)
    {h p : Name} (hp : hashParent h = some p)
    (hh : ¬ Evaluated A h) : HiddenCoord A (coordOf h) := by
  have hhA : h ∉ A := fun hm => by
    have hv := hA.values h hm
    rw [len_of_hashParent hp] at hv
    omega
  obtain ⟨a, haA, hah⟩ : ∃ a ∈ A, Above a h := by
    by_contra hcon
    push Not at hcon
    apply hh
    apply (clearEvaluated_iff A h).1
    exact ⟨hhA, fun m hm hmA => hcon m hmA hm⟩
  have hhs : Above h (coordOf h) := above_coordOf hp
  have has : Above a (coordOf h) := hah.trans hhs
  refine ⟨?_, ?_, ?_⟩
  · intro he
    have heC := (clearEvaluated_iff A _).2 he
    exact heC.2 a has haA
  · intro hsA
    exact (cut_mem_clearAbove hA hsA a has) haA
  · intro a' ha' he
    have hc : child (coordOf h) = some a' := child_hashOf he
    rw [above_of_child hc] at hhs
    rcases hhs with rfl | hhs
    · exact hhA ha'
    · exact (cut_mem_clearAbove hA ha' a (hah.trans hhs)) haA

theorem mem_deps_cases {s n : Name} (h : s ∈ deps n) :
    s = n ∨ hashOf n = some s ∨
      (∃ m, hashOf m = some s ∧ child m = some n) ∨
      (child s = some n ∧ n.len ≠ 129) := by
  cases n with
  | src k =>
      simp only [deps, Finset.mem_singleton] at h
      exact Or.inl h
  | ci k t =>
      by_cases ht : t.val = 0
      · rw [deps_ci_zero k t ht, Finset.mem_singleton] at h
        subst s
        exact Or.inr (Or.inr (Or.inr
          ⟨by simpa [prev, ht] using child_prev k t, by simp [Name.len]⟩))
      · rw [deps_ci_succ k t ht, Finset.mem_singleton] at h
        subst s
        exact Or.inr (Or.inr (Or.inl
          ⟨prev k t, by simp [prev, ht, hashOf], child_prev k t⟩))
  | ch k t =>
      simp only [deps, Finset.mem_singleton] at h
      exact Or.inl h
  | cv k t =>
      simp only [deps, Finset.mem_singleton] at h
      subst s
      exact Or.inr (Or.inl rfl)
  | sc j =>
      simp only [deps, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inl
          ⟨Name.cv (Name.lowerChain j 0) 17, rfl, child_lowerChain j 0⟩))
      · exact Or.inr (Or.inr (Or.inl
          ⟨Name.cv (Name.lowerChain j 1) 17, rfl, child_lowerChain j 1⟩))
      · exact Or.inr (Or.inr (Or.inl
          ⟨Name.cv (Name.lowerChain j 2) 17, rfl, child_lowerChain j 2⟩))
  | sh j =>
      simp only [deps, Finset.mem_singleton] at h
      exact Or.inl h
  | sv j =>
      simp only [deps, Finset.mem_singleton] at h
      subst s
      exact Or.inr (Or.inl rfl)
  | mc u =>
      simp only [deps, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h | h
      · subst s
        exact Or.inr (Or.inr (Or.inl
          ⟨midChild u 0, hashOf_midChild u 0, child_midChild u 0⟩))
      · subst s
        exact Or.inr (Or.inr (Or.inl
          ⟨midChild u 1, hashOf_midChild u 1, child_midChild u 1⟩))
      · subst s
        exact Or.inr (Or.inr (Or.inl
          ⟨midChild u 2, hashOf_midChild u 2, child_midChild u 2⟩))
  | mh u =>
      simp only [deps, Finset.mem_singleton] at h
      exact Or.inl h
  | mv u =>
      simp only [deps, Finset.mem_singleton] at h
      subst s
      exact Or.inr (Or.inl rfl)
  | rc =>
      simp only [deps, Finset.mem_image, Finset.mem_univ, true_and] at h
      obtain ⟨u, rfl⟩ := h
      exact Or.inr (Or.inr (Or.inl ⟨Name.mv u, rfl, rfl⟩))
  | rh =>
      simp only [deps, Finset.mem_singleton] at h
      exact Or.inl h

theorem len_child_of_hashOf {m s n : Name}
    (hm : hashOf m = some s) (hc : child m = some n) :
    n.len ≠ 129 := by
  cases m <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hm
  case cv k t =>
    subst s
    simp only [Name.child] at hc
    by_cases ht : t.val = 17
    · rw [dif_pos ht] at hc
      cases hl : lowerOfChain k with
      | none =>
          rw [hl] at hc
          simp only [Option.some.injEq] at hc
          subst n
          simp [Name.len]
      | some j =>
          rw [hl] at hc
          simp only [Option.some.injEq] at hc
          subst n
          simp [Name.len]
    · rw [dif_neg ht] at hc
      simp only [Option.some.injEq] at hc
      subst n
      simp [Name.len]
  case sv j =>
    subst s
    simp only [Name.child, Option.some.injEq] at hc
    subst n
    simp [Name.len]
  case mv u =>
    subst s
    simp only [Name.child, Option.some.injEq] at hc
    subst n
    simp [Name.len]

theorem not_mem_deps_of_hiddenCoord {A : Finset Name} (hA : IsCut A)
    {s n : Name} (hs : HiddenCoord A s)
    (hn : Evaluated A n ∨ n ∈ A) : s ∉ deps n := by
  intro hd
  obtain ⟨hsE, hsA, hsH⟩ := hs
  rcases mem_deps_cases hd with rfl | hh | ⟨m, hm, hc⟩ | ⟨hc, hl⟩
  · rcases hn with hn | hn
    · exact hsE hn
    · exact hsA hn
  · rcases hn with hn | hn
    · exact hsE (evaluated_of_child_res (child_hashOf hh) hsA hn)
    · exact hsH n hn hh
  · have hcs : child s = some m := child_hashOf hm
    rcases hn with hn | hn
    · by_cases hmA : m ∈ A
      · exact hsH m hmA hm
      · exact hsE (evaluated_of_child_res hcs hsA
          (evaluated_of_child_res hc hmA hn))
    · exact len_child_of_hashOf hm hc (hA.values n hn)
  · rcases hn with hn | hn
    · exact hsE (evaluated_of_child_res hc hsA hn)
    · exact hl (hA.values n hn)

theorem hiddenCoord_ne_rh {A : Finset Name} {s : Name}
    (hs : HiddenCoord A s) : s ≠ Name.rh := by
  rintro rfl
  apply hs.1
  apply (clearEvaluated_iff A Name.rh).1
  exact ⟨hs.2.1, fun m hm => absurd hm (not_above_rh m)⟩

theorem encode_congr_game (G : Graph) (B : Finset (Fin G.size))
    {x x' : G.Assignment} (h : ∀ v ∈ B, x v = x' v) :
    G.encode B x = G.encode B x' := by
  unfold Graph.encode
  refine List.flatMap_congr fun v hv => ?_
  rw [List.mem_filter, decide_eq_true_iff] at hv
  rw [h v hv.2]

theorem evalRec_fin_congr {xi xi' : Rec} {a : Name}
    (h : val xi a = val xi' a) :
    graph.evalRec xi a.fin = graph.evalRec xi' a.fin := by
  unfold val at h
  simpa using congrArg (BitVec.cast (graph_len_fin a).symm) h

theorem revealed_updHash {A : Finset Name} (hA : IsCut A)
    (xi : Rec) {s : Name} (hs : HiddenCoord A s) (b : BitVec 256) :
    revealed A (updHash xi s b) = revealed A xi := by
  unfold revealed
  apply encode_congr_game
  intro v hv
  obtain ⟨a, rfl⟩ : ∃ a : Name, a.fin = v :=
    ⟨Name.ofFin v, Name.fin_ofFin v⟩
  have haA : a ∈ A := (mem_fins_embedding A a).1 hv
  exact evalRec_fin_congr
    (val_updHash_of_not_mem_deps xi s b a
      (not_mem_deps_of_hiddenCoord hA hs (Or.inr haA)))

theorem revealed_updSrc {A : Finset Name} (hA : IsCut A)
    (xi : Rec) {k : Fin 66} (hs : HiddenCoord A (Name.src k))
    (b : BitVec 129) : revealed A (updSrc xi k b) = revealed A xi := by
  unfold revealed
  apply encode_congr_game
  intro v hv
  obtain ⟨a, rfl⟩ : ∃ a : Name, a.fin = v :=
    ⟨Name.ofFin v, Name.fin_ofFin v⟩
  have haA : a ∈ A := (mem_fins_embedding A a).1 hv
  exact evalRec_fin_congr
    (val_updSrc_of_not_mem_deps xi k b a
      (not_mem_deps_of_hiddenCoord hA hs (Or.inr haA)))

theorem evaluated_or_mem_of_child {A : Finset Name} {p h : Name}
    (hc : child p = some h) (he : Evaluated A h) :
    Evaluated A p ∨ p ∈ A := by
  by_cases hpA : p ∈ A
  · exact Or.inr hpA
  · exact Or.inl (evaluated_of_child_res hc hpA he)

theorem pointOf_updHash {A : Finset Name} (hA : IsCut A)
    (xi : Rec) {s : Name} (hs : HiddenCoord A s) (b : BitVec 256)
    {h p : Name} (hp : hashParent h = some p) (he : Evaluated A h) :
    pointOf (updHash xi s b) h p = pointOf xi h p := by
  unfold pointOf
  rw [val_updHash_of_not_mem_deps _ _ _ _
    (not_mem_deps_of_hiddenCoord hA hs
      (evaluated_or_mem_of_child (child_hashParent hp) he))]

theorem pointOf_updSrc {A : Finset Name} (hA : IsCut A)
    (xi : Rec) {k : Fin 66} (hs : HiddenCoord A (Name.src k))
    (b : BitVec 129) {h p : Name} (hp : hashParent h = some p)
    (he : Evaluated A h) :
    pointOf (updSrc xi k b) h p = pointOf xi h p := by
  unfold pointOf
  rw [val_updSrc_of_not_mem_deps _ _ _ _
    (not_mem_deps_of_hiddenCoord hA hs
      (evaluated_or_mem_of_child (child_hashParent hp) he))]

theorem kc_pointOf (xi : Rec) {h p : Name}
    (hp : hashParent h = some p) :
    kc xi (pointOf xi h p) = some (xi.2 h.fin) :=
  (kc_apply_iff xi _ _).2 ⟨h, p, hp, rfl, rfl⟩

theorem fExp_updHash {A : Finset Name} (hA : IsCut A)
    (xi : Rec) {s : Name} (hs : HiddenCoord A s) (b : BitVec 256) :
    fExp (some A) (updHash xi s b) = fExp (some A) xi := by
  funext q
  have hpt : ∀ h p, hashParent h = some p → Exposed (some A) h →
      pointOf (updHash xi s b) h p = pointOf xi h p :=
    fun h p hp he => pointOf_updHash hA xi hs b hp
      ((exposed_some_iff_evaluated A h).1 he)
  have hcond : (∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧
      q = pointOf (updHash xi s b) h p) ↔
      ∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧
        q = pointOf xi h p := by
    constructor
    · rintro ⟨h, p, hp, he, hq⟩
      exact ⟨h, p, hp, he, hq.trans (hpt h p hp he)⟩
    · rintro ⟨h, p, hp, he, hq⟩
      exact ⟨h, p, hp, he, hq.trans (hpt h p hp he).symm⟩
  simp only [fExp]
  by_cases hq : ∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧
      q = pointOf xi h p
  · rw [if_pos (hcond.2 hq), if_pos hq]
    obtain ⟨h, p, hp, he, rfl⟩ := hq
    have hne : h ≠ s := fun e => hs.1
      (e ▸ (exposed_some_iff_evaluated A h).1 he)
    rw [kc_pointOf xi hp, ← hpt h p hp he, kc_pointOf _ hp,
      updHash_snd_ne _ _ _ hne]
  · rw [if_neg (fun h' => hq (hcond.1 h')), if_neg hq]

theorem fExp_updSrc {A : Finset Name} (hA : IsCut A)
    (xi : Rec) {k : Fin 66} (hs : HiddenCoord A (Name.src k))
    (b : BitVec 129) :
    fExp (some A) (updSrc xi k b) = fExp (some A) xi := by
  funext q
  have hpt : ∀ h p, hashParent h = some p → Exposed (some A) h →
      pointOf (updSrc xi k b) h p = pointOf xi h p :=
    fun h p hp he => pointOf_updSrc hA xi hs b hp
      ((exposed_some_iff_evaluated A h).1 he)
  have hcond : (∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧
      q = pointOf (updSrc xi k b) h p) ↔
      ∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧
        q = pointOf xi h p := by
    constructor
    · rintro ⟨h, p, hp, he, hq⟩
      exact ⟨h, p, hp, he, hq.trans (hpt h p hp he)⟩
    · rintro ⟨h, p, hp, he, hq⟩
      exact ⟨h, p, hp, he, hq.trans (hpt h p hp he).symm⟩
  simp only [fExp]
  by_cases hq : ∃ h p, hashParent h = some p ∧ Exposed (some A) h ∧
      q = pointOf xi h p
  · rw [if_pos (hcond.2 hq), if_pos hq]
    obtain ⟨h, p, hp, he, rfl⟩ := hq
    rw [kc_pointOf xi hp, ← hpt h p hp he, kc_pointOf _ hp, updSrc_snd]
  · rw [if_neg (fun h' => hq (hcond.1 h')), if_neg hq]

theorem dataOf_updHash {A : Finset Name} (hA : IsCut A)
    (xi : Rec) {s : Name} (hs : HiddenCoord A s) (b : BitVec 256) :
    dataOf A (updHash xi s b) = dataOf A xi := by
  simp only [dataOf, pkOf_updHash _ (hiddenCoord_ne_rh hs),
    revealed_updHash hA _ hs, fExp_updHash hA _ hs]

theorem dataOf_updSrc {A : Finset Name} (hA : IsCut A)
    (xi : Rec) {k : Fin 66} (hs : HiddenCoord A (Name.src k))
    (b : BitVec 129) : dataOf A (updSrc xi k b) = dataOf A xi := by
  simp only [dataOf, pkOf_updSrc, revealed_updSrc hA _ hs,
    fExp_updSrc hA _ hs]

theorem fiberB_closedAt {A : Finset Name} (hA : IsCut A) (dt : Data)
    {s : Name} (hs : HiddenCoord A s) : ClosedAt (fiberB A dt) s := by
  by_cases hsrc : ∃ k, s = Name.src k
  · obtain ⟨k, rfl⟩ := hsrc
    rw [closedAt_src]
    simp only [fiberB, Finset.mem_filter, Finset.mem_univ, true_and]
    intro xi hxi b
    rw [dataOf_updSrc hA _ hs]
    exact hxi
  · push Not at hsrc
    rw [closedAt_of_ne_src _ hsrc]
    simp only [fiberB, Finset.mem_filter, Finset.mem_univ, true_and]
    intro xi hxi b
    rw [dataOf_updHash hA _ hs]
    exact hxi

/-- The concrete post-sign public-data fiber satisfies the raw hidden-input
charge used by `authPotential_charge`. -/
theorem signedHitsCharge : SignedHitsCharge := by
  intro A hA dt q
  by_cases hex : ∃ h p, hashParent h = some p ∧ ¬ Evaluated A h ∧
      ∃ xi₀ : Rec, q = pointOf xi₀ h p
  · obtain ⟨h, p, hp, hh, xi₀, rfl⟩ := hex
    have key : ∀ xi : Rec,
        (fHid (some A) xi (pointOf xi₀ h p)).isSome ↔
          val xi p = val xi₀ p := by
      intro xi
      rw [fHid_isSome_some_iff]
      constructor
      · rintro ⟨h', p', hp', _, e⟩
        obtain rfl := pointOf_inj_left hp hp' e
        rw [hp] at hp'
        obtain rfl := Option.some.inj hp'
        exact (pointOf_inj_input e).symm
      · intro hv
        exact ⟨h, p, hp, hh, by simp only [pointOf, hv]⟩
    calc
      ∑ xi ∈ fiberB A dt,
          (if (fHid (some A) xi (pointOf xi₀ h p)).isSome then w else 0) =
          ∑ xi ∈ fiberB A dt,
            (if val xi p = val xi₀ p then w else 0) := by
        refine Finset.sum_congr rfl fun xi _ => ?_
        by_cases hv : val xi p = val xi₀ p <;> simp [key, hv]
      _ ≤ _ := sum_input_eq_le hp _
        (fiberB_closedAt hA dt (coordOf_hiddenCoord hA hp hh)) _
  · have hz : ∀ xi : Rec, ¬ (fHid (some A) xi q).isSome := by
      intro xi hk
      rw [fHid_isSome_some_iff] at hk
      obtain ⟨h, p, hp, hh, e⟩ := hk
      exact hex ⟨h, p, hp, hh, xi, e⟩
    have hsum : ∑ xi ∈ fiberB A dt,
        (if (fHid (some A) xi q).isSome then w else 0) = 0 :=
      Finset.sum_eq_zero fun xi _ => if_neg (hz xi)
    exact hsum.le.trans _root_.zero_le

theorem hits_charge_A' (pk : BitVec 128) {T : Finset Rec}
    (hT : T ⊆ fiberA pk) (q : Query) :
    ∑ xi ∈ T, w * ind ((kc xi q).isSome) ≤ ε * sumW (fiberA pk) :=
  hits_charge_A'_of initialHitsCharge pk hT q

theorem hits_charge_B' {A : Finset Name} (hA : IsCut A) (dt : Data)
    {T : Finset Rec} (hT : T ⊆ fiberB A dt) (q : Query) :
    ∑ xi ∈ T, w * ind ((fHid (some A) xi q).isSome) ≤
      ε * sumW (fiberB A dt) :=
  hits_charge_B'_of signedHitsCharge hA dt hT q

theorem authPotential_charge {A : Finset Name} (hA : IsCut A) (dt : Data)
    {T : Finset Rec} (hT : T ⊆ fiberB A dt)
    (c : Cache) (q : Query) (hq : c q = none) :
    (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
      authPotential T (some A) (c.cacheQuery q u)) ≤
      authPotential T (some A) c +
        authRate * sumW (fiberB A dt) * queryCost (.inr q) :=
  authPotential_charge_of signedHitsCharge hA dt hT c q hq

theorem clearEvaluated_child_of_clearAbove {A : Finset Name}
    {a p : Name} (ha : ∀ m, Above m a → m ∉ A)
    (hc : child a = some p) : ClearEvaluated A p := by
  exact ⟨ha p (Above.child hc),
    fun m hm => ha m (Above.step hc hm)⟩

/-! ## Starting the authentication walk at a disclosed value -/

theorem up_from_cut {A : Finset Name} (hA : IsCut A)
    {xi : Rec} {d : Cache} {given y : graph.Assignment}
    (hy : graph.ReconEqs d (fins A) given y)
    (hacc : lowPk (yv y Name.rh) = pkOf xi)
    {a : Name} (ha : a ∈ A) (hne : yv y a ≠ val xi a) : Spr d xi := by
  have hclear := cut_mem_clearAbove hA ha
  have halen := hA.values a ha
  cases a with
  | src k =>
      have hc : child (Name.src k) = some (Name.ci k 0) := rfl
      have hpC := clearEvaluated_child_of_clearAbove hclear hc
      have hpE := (clearEvaluated_iff A _).1 hpC
      apply up hy hacc hpC rfl
      intro heq
      rw [yv_ci hy hpE, val_ci] at heq
      apply hne
      exact eq_of_lowWord_eq (show (Name.src k).len = 129 by rfl)
        (bv_append_inj heq).2
  | cv k t =>
      by_cases ht : t.val = 17
      · have ht' : t = 17 := Fin.ext ht
        subst t
        cases hl : lowerOfChain k with
        | some j =>
            have hc : child (Name.cv k 17) = some (Name.sc j) := by
              simp [Name.child, hl]
            have hpC := clearEvaluated_child_of_clearAbove hclear hc
            have hpE := (clearEvaluated_iff A _).1 hpC
            apply up hy hacc hpC rfl
            intro heq
            rw [yv_sc hy hpE, val_sc'] at heq
            obtain ⟨h0, h1, h2⟩ := cat3_inj (bv_append_inj heq).2
            obtain ⟨b, hb⟩ := lowerChain_witness hl
            fin_cases b
            · subst k
              apply hne
              have hz : ((fun i : Fin 3 => i) ⟨0, by omega⟩) =
                  (0 : Fin 3) := by apply Fin.ext; rfl
              rw [hz]
              exact h0
            · subst k
              apply hne
              have ho : ((fun i : Fin 3 => i) ⟨1, by omega⟩) =
                  (1 : Fin 3) := by apply Fin.ext; rfl
              rw [ho]
              exact h1
            · subst k
              apply hne
              have ht : ((fun i : Fin 3 => i) ⟨2, by omega⟩) =
                  (2 : Fin 3) := by apply Fin.ext; rfl
              rw [ht]
              exact h2
        | none =>
            have hc : child (Name.cv k 17) =
                some (Name.mc (upperOfChain k)) := by
              simp [Name.child, hl]
            have hpC := clearEvaluated_child_of_clearAbove hclear hc
            have hpE := (clearEvaluated_iff A _).1 hpC
            apply up hy hacc hpC rfl
            intro heq
            rw [yv_mc hy hpE, val_mc] at heq
            obtain ⟨h0, h1, h2⟩ := cat3_inj (bv_append_inj heq).2
            obtain ⟨b, hb⟩ := direct_midChild_witness hl
            fin_cases b
            · apply hne
              apply eq_of_lowWord_eq
                (show (Name.cv k 17).len = 129 by rfl)
              have hb' : midChild (upperOfChain k) 0 = Name.cv k 17 := by
                simpa using hb
              exact transport_lowWord_eq hb' h0
            · apply hne
              apply eq_of_lowWord_eq
                (show (Name.cv k 17).len = 129 by rfl)
              have hb' : midChild (upperOfChain k) 1 = Name.cv k 17 := by
                simpa using hb
              exact transport_lowWord_eq hb' h1
            · apply hne
              apply eq_of_lowWord_eq
                (show (Name.cv k 17).len = 129 by rfl)
              have hb' : midChild (upperOfChain k) 2 = Name.cv k 17 := by
                simpa using hb
              exact transport_lowWord_eq hb' h2
      · have hc : child (Name.cv k t) =
            some (Name.ci k ⟨t.val + 1, by omega⟩) := by
          simp [Name.child, ht]
        have hpC := clearEvaluated_child_of_clearAbove hclear hc
        have hpE := (clearEvaluated_iff A _).1 hpC
        apply up hy hacc hpC rfl
        intro heq
        rw [yv_ci hy hpE, val_ci] at heq
        have hp := (bv_append_inj heq).2
        apply hne
        rw [prev_succ k t (by omega)] at hp
        exact eq_of_lowWord_eq (show (Name.cv k t).len = 129 by rfl) hp
  | sv j =>
      have hc : child (Name.sv j) =
          some (Name.mc (upperOfLower j)) := rfl
      have hpC := clearEvaluated_child_of_clearAbove hclear hc
      have hpE := (clearEvaluated_iff A _).1 hpC
      apply up hy hacc hpC rfl
      intro heq
      rw [yv_mc hy hpE, val_mc] at heq
      obtain ⟨h0, h1, h2⟩ := cat3_inj (bv_append_inj heq).2
      obtain ⟨b, hb⟩ := lower_midChild_witness j
      fin_cases b
      · apply hne
        apply eq_of_lowWord_eq (show (Name.sv j).len = 129 by rfl)
        have hb' : midChild (upperOfLower j) 0 = Name.sv j := by
          simpa using hb
        exact transport_lowWord_eq hb' h0
      · apply hne
        apply eq_of_lowWord_eq (show (Name.sv j).len = 129 by rfl)
        have hb' : midChild (upperOfLower j) 1 = Name.sv j := by
          simpa using hb
        exact transport_lowWord_eq hb' h1
      · apply hne
        apply eq_of_lowWord_eq (show (Name.sv j).len = 129 by rfl)
        have hb' : midChild (upperOfLower j) 2 = Name.sv j := by
          simpa using hb
        exact transport_lowWord_eq hb' h2
  | mv u =>
      have hc : child (Name.mv u) = some Name.rc := rfl
      have hpC := clearEvaluated_child_of_clearAbove hclear hc
      have hpE := (clearEvaluated_iff A _).1 hpC
      apply up hy hacc hpC rfl
      intro heq
      rw [yv_rc hy hpE, val_rc'] at heq
      exact hne (congrFun (cat10_inj (bv_append_inj heq).2) u)
  | ci k t | ch k t | sc k | sh k | mc k | mh k | rc | rh =>
      simp [Name.len] at halen

/-! ## Same-class payload authentication -/

theorem encode_congr (G : Graph) (A : Finset (Fin G.size))
    {x x' : G.Assignment} (h : ∀ v ∈ A, x v = x' v) :
    G.encode A x = G.encode A x' := by
  unfold Graph.encode
  refine List.flatMap_congr fun v hv => ?_
  rw [List.mem_filter, decide_eq_true_iff] at hv
  rw [h v hv.2]

/-- A forged payload for the signed class differs at a disclosed value, and
that difference reaches a spurious graph binding. -/
theorem events_same {A : Finset Name} (hA : IsCut A)
    {xi : Rec} {d : Cache} {x' : List Bool} {y : graph.Assignment}
    (hy : graph.ReconEqs d (fins A) (graph.decode (fins A) x') y)
    (hacc : lowPk (yv y Name.rh) = pkOf xi)
    (hlen : x'.length = graph.revealBits (fins A))
    (hne : x' ≠ graph.encode (fins A) (graph.evalRec xi)) : Spr d xi := by
  have hex : ∃ a ∈ A,
      graph.decode (fins A) x' a.fin ≠ graph.evalRec xi a.fin := by
    by_contra hcon
    push Not at hcon
    apply hne
    rw [← graph.encode_decode (fins A) x' hlen]
    apply encode_congr
    intro v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
    exact hcon a ha
  obtain ⟨a, ha, hne'⟩ := hex
  apply up_from_cut hA hy hacc ha
  intro heq
  apply hne'
  rw [yv_mem hy ha] at heq
  unfold val at heq
  exact cast_injective _ heq

/-! ## Accepted-run decomposition with one explicit cross-cut seam -/

/-- The graph-specific statement still needed for distinct schedule classes.
It is separated so the accepted-game endgame does not depend on how the cut
comparison proof is eventually organized. -/
def CrossCutAuthentication : Prop :=
  ∀ (xi : Rec) (signedClass i : Fin M) (d : Cache)
    (given y : graph.Assignment),
    i ≠ signedClass →
    graph.ReconEqs d (fins (setsName i)) given y →
    lowPk (yv y Name.rh) = pkOf xi →
      Spr d xi ∨
        Cache.Hits d (fHid (some (setsName signedClass)) xi)

/-- Given the cross-cut authentication lemma, every accepted verification is
honest for the signed class or reaches one of the two authentication events. -/
theorem accepted_class_cases (hcross : CrossCutAuthentication)
    (xi : Rec) (signedClass : Fin M) (m : Message)
    (sigma : WeightedScheme.Signature) (c d : Cache)
    (h : (true, d) ∈ support (run (scheme.verify (pkOf xi) m sigma) c)) :
    ∃ answer, d (encQuery (m, sigma.1)) = some answer ∧
      ∃ i : Fin M, LongChain91Schedule.decode answer = some i ∧
        ((i = signedClass ∧
            sigma.2 = graph.encode (fins (setsName signedClass))
              (graph.evalRec xi)) ∨
          Spr d xi ∨
          Cache.Hits d (fHid (some (setsName signedClass)) xi)) := by
  obtain ⟨_, hh⟩ :=
    WeightedScheme.verify_support scheme (pkOf xi) m sigma c (true, d) h
  obtain ⟨answer, ha, i, hi, hlen, y, hy, hpk⟩ := hh rfl
  refine ⟨answer, ha, i, hi, ?_⟩
  have hacc := accepted_lowPk xi y hpk
  by_cases hic : i = signedClass
  · subst i
    by_cases hpayload : sigma.2 =
        graph.encode (fins (setsName signedClass)) (graph.evalRec xi)
    · exact Or.inl ⟨rfl, hpayload⟩
    · exact Or.inr (Or.inl
        (events_same (isCut_of_mem_family (setsName_mem signedClass))
          hy hacc hlen hpayload))
  · exact Or.inr (hcross xi signedClass i d _ y hic hy hacc)

/-- Public name for the cached-row alternate-input event.  This is
definitionally the predicate used by its replay bound. -/
abbrev AlternateClass (c : Cache) (signedInput : EncInput)
    (i : Fin M) : Prop :=
  LongChain91CachedRow.alternateClass c signedInput i

/-- Acceptance of a pair different from the signed pair reaches graph
authentication badness or the cached-row alternate-class event. -/
theorem accepted_strong_event (hcross : CrossCutAuthentication)
    (xi : Rec) (signedClass : Fin M) (signedInput : EncInput)
    (m : Message) (sigma : WeightedScheme.Signature) (c d : Cache)
    (h : (true, d) ∈ support (run (scheme.verify (pkOf xi) m sigma) c))
    (hne : (m, sigma) ≠ (signedInput.1,
      (signedInput.2,
        graph.encode (fins (setsName signedClass)) (graph.evalRec xi)))) :
    Spr d xi ∨ Cache.Hits d (fHid (some (setsName signedClass)) xi) ∨
      AlternateClass d signedInput signedClass := by
  obtain ⟨answer, ha, i, hi, he | hs | hh⟩ :=
    accepted_class_cases hcross xi signedClass m sigma c d h
  · obtain ⟨rfl, hpayload⟩ := he
    right
    right
    refine ⟨(m, sigma.1), ?_, answer, ha, hi⟩
    intro heq
    apply hne
    have hm : m = signedInput.1 :=
      congrArg (fun u : EncInput => u.1) heq
    have hn : sigma.1 = signedInput.2 :=
      congrArg (fun u : EncInput => u.2) heq
    exact Prod.ext hm (Prod.ext hn hpayload)
  · exact Or.inl hs
  · exact Or.inr (Or.inl hh)

#print axioms authPotential_charge
#print axioms events_same
#print axioms accepted_class_cases
#print axioms accepted_strong_event

end OptimalOTS.WeightedConstruction.LongChain91
