import Submissions.UpperCompressions.LongChain91Auth

/-!
# Authentication-event closure for the cost-91 long-chain graph

This module follows a differing reconstructed value upward through the two
ternary aggregation layers.  At a hash node the walk either obtains the
spurious binding event `Spr`, or the differing low 129 bits propagate to the
next value node.  The public root uses its exact low-128-bit endpoint.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace OptimalOTS.WeightedConstruction.LongChain91

open OptimalOTS.Dag
open Name

/-! ## Distance to the root and visited nodes -/

def chainBase (k : Fin 66) : ℕ :=
  if (lowerOfChain k).isSome then 8 else 5

def height : Name → ℕ
  | Name.src k => chainBase k + 54
  | Name.ci k t => chainBase k + 2 + 3 * (17 - t.val)
  | Name.ch k t => chainBase k + 1 + 3 * (17 - t.val)
  | Name.cv k t => chainBase k + 3 * (17 - t.val)
  | Name.sc _ => 7
  | Name.sh _ => 6
  | Name.sv _ => 5
  | Name.mc _ => 4
  | Name.mh _ => 3
  | Name.mv _ => 2
  | Name.rc => 1
  | Name.rh => 0

theorem height_child {m n : Name} (h : child n = some m) :
    height m + 1 = height n := by
  cases n with
  | src k =>
      simp only [Name.child, Option.some.injEq] at h
      subst m
      simp [height]
  | ci k t =>
      simp only [Name.child, Option.some.injEq] at h
      subst m
      simp [height]
      omega
  | ch k t =>
      simp only [Name.child, Option.some.injEq] at h
      subst m
      simp [height]
      omega
  | cv k t =>
      simp only [Name.child] at h
      split_ifs at h with ht
      · cases hl : lowerOfChain k with
        | none =>
            simp only [hl, Option.some.injEq] at h
            subst m
            simp [height, chainBase, hl]
            omega
        | some j =>
            simp only [hl, Option.some.injEq] at h
            subst m
            simp [height, chainBase, hl]
            omega
      · simp only [Option.some.injEq] at h
        subst m
        simp [height]
        omega
  | sc j | sh j | sv j =>
      simp only [Name.child, Option.some.injEq] at h
      subst m
      simp [height]
  | mc u | mh u | mv u =>
      simp only [Name.child, Option.some.injEq] at h
      subst m
      simp [height]
  | rc =>
      simp only [Name.child, Option.some.injEq] at h
      subst m
      simp [height]
  | rh => simp [Name.child] at h

theorem child_eq_none {n : Name} (h : child n = none) : n = Name.rh := by
  cases n <;> simp only [Name.child, reduceCtorEq] at h
  case cv k t => split_ifs at h <;> split at h <;> contradiction
  case rh => rfl

/-- The concrete one-child graph characterization of reconstruction visits. -/
theorem visited_iff_clear (A : Finset Name) (n : Name) :
    graph.Visited (fins A) n.fin ↔ ∀ m, Above m n → m ∉ A := by
  constructor
  · exact visited_no_above A
  · suffices ∀ k, ∀ n, height n = k →
        (∀ m, Above m n → m ∉ A) → graph.Visited (fins A) n.fin from
      this _ n rfl
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro n hn hA
      rcases hc : child n with _ | p
      · rw [child_eq_none hc]
        exact Graph.Visited.root
      · have hp : p ∉ A := hA p (Above.child hc)
        have hvp : graph.Visited (fins A) p.fin :=
          ih (height p) (by rw [← hn, ← height_child hc]; omega)
            p rfl (fun m hm => hA m (Above.step hc hm))
        exact Graph.Visited.parent hvp
          (fun h => hp ((mem_fins_embedding A p).mp h))
          ((mem_graph_parents_iff n p).mpr hc)

def ClearEvaluated (A : Finset Name) (n : Name) : Prop :=
  n ∉ A ∧ ∀ m, Above m n → m ∉ A

theorem clearEvaluated_iff (A : Finset Name) (n : Name) :
    ClearEvaluated A n ↔ Evaluated A n := by
  unfold ClearEvaluated Evaluated
  rw [nameEmbedding_apply]
  rw [visited_iff_clear]
  tauto

theorem clearEvaluated_child {A : Finset Name} {n p : Name}
    (hn : ClearEvaluated A n) (hc : child n = some p) :
    ClearEvaluated A p := by
  refine ⟨hn.2 p (Above.child hc), fun m hm => ?_⟩
  exact hn.2 m (Above.step hc hm)

/-! ## Reconstruction equations by concrete name -/

def yv (y : graph.Assignment) (n : Name) : BitVec n.len :=
  (y n.fin).cast (graph_len_fin n)

theorem sigma_cast {a b : ℕ} (h : a = b) (x : BitVec a) :
    (⟨a, x⟩ : Σ k : ℕ, BitVec k) = ⟨b, x.cast h⟩ := by
  subst h
  rfl

theorem lowPk_cast_eq {a b : ℕ} (h : a = b) (x : BitVec a) :
    lowPk (x.cast h) = lowPk x := by
  subst h
  rfl

theorem lowWord_cast_eq {a b : ℕ} (h : a = b) (x : BitVec a) :
    lowWord (x.cast h) = lowWord x := by
  subst h
  rfl

theorem lowWord_129 (x : BitVec 129) : lowWord x = x := BitVec.setWidth_eq x

theorem eq_of_lowWord_eq {n : ℕ} (hn : n = 129) {x y : BitVec n}
    (h : lowWord x = lowWord y) : x = y := by
  subst n
  simpa only [lowWord_eq_self] using h

theorem lowWord_eq_cast {m : ℕ} (h : m = 129) (x : BitVec m) :
    lowWord x = x.cast h := by
  subst h
  exact BitVec.setWidth_eq x

theorem cast_injective {n m : ℕ} (h : n = m) {x y : BitVec n}
    (e : x.cast h = y.cast h) : x = y := by
  subst h
  simpa using e

theorem bv_append_inj {n m : ℕ} {x x' : BitVec n} {y y' : BitVec m}
    (h : x ++ y = x' ++ y') : x = x' ∧ y = y' := by
  have key : ∀ i, (x ++ y).getLsbD i = (x' ++ y').getLsbD i :=
    fun i => by rw [h]
  simp only [BitVec.getLsbD_append] at key
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hh := key (i + m)
    simp only [show ¬ (i + m < m) by omega, if_false,
      Nat.add_sub_cancel] at hh
    exact hh
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hh := key i
    simpa [hi] using hh

theorem cat3_inj {a b c a' b' c' : BitVec 129}
    (h : cat3 a b c = cat3 a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  unfold cat3 at h
  obtain ⟨h12, h3⟩ := bv_append_inj (cast_injective _ h)
  obtain ⟨h1, h2⟩ := bv_append_inj h12
  exact ⟨h1, h2, h3⟩

theorem cat10_inj {a b : Fin 10 → BitVec 129} (h : cat10 a = cat10 b) :
    a = b := by
  unfold cat10 at h
  obtain ⟨hprefix8, h9⟩ := bv_append_inj (cast_injective _ h)
  obtain ⟨hprefix7, h8⟩ := bv_append_inj hprefix8
  obtain ⟨hprefix6, h7⟩ := bv_append_inj hprefix7
  obtain ⟨hprefix5, h6⟩ := bv_append_inj hprefix6
  obtain ⟨hprefix4, h5⟩ := bv_append_inj hprefix5
  obtain ⟨hprefix3, h4⟩ := bv_append_inj hprefix4
  obtain ⟨hprefix2, h3⟩ := bv_append_inj hprefix3
  obtain ⟨hprefix1, h2⟩ := bv_append_inj hprefix2
  obtain ⟨h0, h1⟩ := bv_append_inj hprefix1
  funext u
  fin_cases u <;> assumption

theorem graph_kind_hash {h p : Name} (hp : hashParent h = some p) :
    ∃ (hlt : p.fin < h.fin) (hl : graph.len h.fin = hashBits),
      graph.kind h.fin = .hash p.fin hlt hl := by
  rw [graph_kind_fin]
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    subst hp <;> exact ⟨_, _, rfl⟩

theorem graph_kind_det {n : Name} (hc : n.cost = 0)
    (hs : ∀ k, n ≠ Name.src k) :
    ∃ hlt hf, graph.kind n.fin =
      .det (Name.parentFins n) hlt
        (fun x => (detVal n x).cast (graph_len_fin n).symm) hf := by
  rw [graph_kind_fin]
  cases n
  · exact absurd rfl (hs _)
  all_goals first | exact ⟨_, _, rfl⟩ | (simp [Name.cost] at hc)

section Recon

variable {A : Finset Name} {d : Cache} {given y : graph.Assignment}

theorem yv_mem (hy : graph.ReconEqs d (fins A) given y)
    {n : Name} (hn : n ∈ A) :
    yv y n = (given n.fin).cast (graph_len_fin n) := by
  unfold yv
  rw [(hy n.fin).1 ((mem_fins_embedding A n).mpr hn)]

theorem recon_evaluated (hy : graph.ReconEqs d (fins A) given y)
    {n : Name} (he : Evaluated A n) :
    (∀ p hp hl, graph.kind n.fin = .hash p hp hl →
        ∃ w, d ⟨graph.len p, y p⟩ = some w ∧ y n.fin = w.cast hl.symm) ∧
      (∀ ps hlt f hf, graph.kind n.fin = .det ps hlt f hf → y n.fin = f y) ∧
      (graph.kind n.fin = .source → y n.fin = 0) := by
  exact (hy n.fin).2.2
    (fun h => he.2 ((mem_fins_embedding A n).mp h)) he.1

theorem yv_hash (hy : graph.ReconEqs d (fins A) given y)
    {h p : Name} (hp : hashParent h = some p) (he : Evaluated A h) :
    ∃ w, d ⟨p.len, yv y p⟩ = some w ∧
      lowWord w = lowWord (yv y h) := by
  obtain ⟨hlt, hl, hk⟩ := graph_kind_hash hp
  obtain ⟨w, hw, hyw⟩ := (recon_evaluated hy he).1 _ _ _ hk
  refine ⟨w, ?_, ?_⟩
  · rw [sigma_cast (graph_len_fin p) (y p.fin)] at hw
    exact hw
  · unfold yv
    rw [lowWord_cast_eq, hyw, lowWord_cast_eq]

theorem yv_hash_lowPk (hy : graph.ReconEqs d (fins A) given y)
    {h p : Name} (hp : hashParent h = some p) (he : Evaluated A h) :
    ∃ w, d ⟨p.len, yv y p⟩ = some w ∧ lowPk w = lowPk (yv y h) := by
  obtain ⟨hlt, hl, hk⟩ := graph_kind_hash hp
  obtain ⟨w, hw, hyw⟩ := (recon_evaluated hy he).1 _ _ _ hk
  refine ⟨w, ?_, ?_⟩
  · rw [sigma_cast (graph_len_fin p) (y p.fin)] at hw
    exact hw
  · unfold yv
    rw [lowPk_cast_eq, hyw, lowPk_cast_eq]

theorem yv_det (hy : graph.ReconEqs d (fins A) given y)
    {n : Name} (he : Evaluated A n) (hc : n.cost = 0)
    (hs : ∀ k, n ≠ Name.src k) : yv y n = detVal n y := by
  obtain ⟨hlt, hf, hk⟩ := graph_kind_det hc hs
  have hv := (recon_evaluated hy he).2.1 _ _ _ _ hk
  unfold yv
  rw [hv]
  exact cast_cast_eq _ _ _

theorem yv_cv (hy : graph.ReconEqs d (fins A) given y)
    {k : Fin 66} {t : Fin 18} (he : Evaluated A (Name.cv k t)) :
    yv y (Name.cv k t) = lowWord (yv y (Name.ch k t)) := by
  rw [yv_det hy he rfl (by simp)]
  show lowWord (y _) = _
  unfold yv
  rw [lowWord_cast_eq]

theorem yv_sv (hy : graph.ReconEqs d (fins A) given y)
    {j : Fin 18} (he : Evaluated A (Name.sv j)) :
    yv y (Name.sv j) = lowWord (yv y (Name.sh j)) := by
  rw [yv_det hy he rfl (by simp)]
  show lowWord (y _) = _
  unfold yv
  rw [lowWord_cast_eq]

theorem yv_mv (hy : graph.ReconEqs d (fins A) given y)
    {u : Fin 10} (he : Evaluated A (Name.mv u)) :
    yv y (Name.mv u) = lowWord (yv y (Name.mh u)) := by
  rw [yv_det hy he rfl (by simp)]
  show lowWord (y _) = _
  unfold yv
  rw [lowWord_cast_eq]

theorem yv_ci (hy : graph.ReconEqs d (fins A) given y)
    {k : Fin 66} {t : Fin 18} (he : Evaluated A (Name.ci k t)) :
    yv y (Name.ci k t) =
      tw (Name.ch k t) ++ lowWord (yv y (prev k t)) := by
  rw [yv_det hy he rfl (by simp)]
  show tw (Name.ch k t) ++ lowWord (y (prev k t).fin) = _
  unfold yv
  rw [lowWord_cast_eq]

theorem yv_sc (hy : graph.ReconEqs d (fins A) given y)
    {j : Fin 18} (he : Evaluated A (Name.sc j)) :
    yv y (Name.sc j) = tw (Name.sh j) ++ cat3
      (yv y (Name.cv (Name.lowerChain j 0) 17))
      (yv y (Name.cv (Name.lowerChain j 1) 17))
      (yv y (Name.cv (Name.lowerChain j 2) 17)) := by
  rw [yv_det hy he rfl (by simp)]
  show tw (Name.sh j) ++ cat3 (lowWord (y _)) (lowWord (y _))
      (lowWord (y _)) = _
  refine congrArg (fun z => tw (Name.sh j) ++ z) ?_
  congr 1 <;> exact lowWord_eq_cast (graph_len_fin _) _

theorem yv_mc (hy : graph.ReconEqs d (fins A) given y)
    {u : Fin 10} (he : Evaluated A (Name.mc u)) :
    yv y (Name.mc u) = tw (Name.mh u) ++ cat3
      (lowWord (yv y (midChild u 0))) (lowWord (yv y (midChild u 1)))
      (lowWord (yv y (midChild u 2))) := by
  rw [yv_det hy he rfl (by simp)]
  show tw (Name.mh u) ++ cat3 (lowWord (y _)) (lowWord (y _))
      (lowWord (y _)) = _
  refine congrArg (fun z => tw (Name.mh u) ++ z) ?_
  congr 1 <;> (unfold yv; rw [lowWord_cast_eq])

theorem yv_rc (hy : graph.ReconEqs d (fins A) given y)
    (he : Evaluated A Name.rc) :
    yv y Name.rc = tw Name.rh ++ cat10 fun u => yv y (Name.mv u) := by
  rw [yv_det hy he rfl (by simp)]
  show tw Name.rh ++ cat10 (fun u => lowWord (y (Name.mv u).fin)) = _
  exact congrArg (fun z => tw Name.rh ++ cat10 z)
    (funext fun u => lowWord_eq_cast (graph_len_fin (Name.mv u)) _)

end Recon

/-! ## Value propagation through the two ternary layers -/

theorem cost_hashParent {h p : Name} (hp : hashParent h = some p) :
    p.cost = 0 := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    subst hp <;> rfl

theorem hashParent_ne_src {h p : Name} (hp : hashParent h = some p)
    (k : Fin 66) : p ≠ Name.src k := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    subst hp <;> intro e <;> nomatch e

theorem bindingValue_ch (k : Fin 66) (t : Fin 18) (w : BitVec 256) :
    bindingValue (Name.ch k t) w = lowWord w := by
  simp [bindingValue, bindingWidth, lowWord]

theorem bindingValue_sh (j : Fin 18) (w : BitVec 256) :
    bindingValue (Name.sh j) w = lowWord w := by
  simp [bindingValue, bindingWidth, lowWord]

theorem bindingValue_mh (u : Fin 10) (w : BitVec 256) :
    bindingValue (Name.mh u) w = lowWord w := by
  simp [bindingValue, bindingWidth, lowWord]

theorem transport_lowWord_eq {ξ : Rec} {y : graph.Assignment} {a b : Name}
    (hab : a = b)
    (h : lowWord (yv y a) = lowWord (val ξ a)) :
    lowWord (yv y b) = lowWord (val ξ b) := by
  subst b
  exact h

theorem tagNat_yv {A : Finset Name} {d : Cache}
    {given y : graph.Assignment} (hy : graph.ReconEqs d (fins A) given y)
    {h p : Name} (hp : hashParent h = some p) (he : Evaluated A p) :
    tagNat ⟨p.len, yv y p⟩ = h.idx := by
  rw [yv_det hy he (cost_hashParent hp) (hashParent_ne_src hp)]
  exact tagNat_detVal_of_hashParent hp y

theorem val_sc' (ξ : Rec) (j : Fin 18) :
    val ξ (Name.sc j) = tw (Name.sh j) ++ cat3
      (val ξ (Name.cv (Name.lowerChain j 0) 17))
      (val ξ (Name.cv (Name.lowerChain j 1) 17))
      (val ξ (Name.cv (Name.lowerChain j 2) 17)) := by
  rw [val_sc, val_cv, val_cv, val_cv]

theorem val_rc' (ξ : Rec) :
    val ξ Name.rc = tw Name.rh ++ cat10 (fun u => val ξ (Name.mv u)) := by
  rw [val_rc]
  exact congrArg (fun z => tw Name.rh ++ cat10 z)
    (funext fun u => (val_mv ξ u).symm)

theorem prev_succ (k : Fin 66) (t : Fin 18) (ht : t.val < 17) :
    prev k ⟨t.val + 1, by omega⟩ = Name.cv k t := by
  simp [prev]

theorem lowerChain_witness {k : Fin 66} {j : Fin 18}
    (h : lowerOfChain k = some j) :
    ∃ a : Fin 3, Name.lowerChain j a = k := by
  revert k j
  decide +kernel

theorem direct_midChild_witness {k : Fin 66}
    (h : lowerOfChain k = none) :
    ∃ a : Fin 3, midChild (upperOfChain k) a = Name.cv k 17 := by
  revert k
  decide +kernel

theorem lower_midChild_witness (j : Fin 18) :
    ∃ a : Fin 3, midChild (upperOfLower j) a = Name.sv j := by
  revert j
  decide +kernel

/-! ## The authentication walk -/

/-- A differing deterministic value on the live reconstruction path forces a
spurious graph binding.  The proof traverses both ternary levels explicitly. -/
theorem up {A : Finset Name} {ξ : Rec} {d : Cache}
    {given y : graph.Assignment} (hy : graph.ReconEqs d (fins A) given y)
    (hacc : lowPk (yv y Name.rh) = pkOf ξ) {v : Name}
    (hv : ClearEvaluated A v) (hcost : v.cost = 0)
    (hne : yv y v ≠ val ξ v) : Spr d ξ := by
  suffices ∀ n, ∀ v, height v = n → ClearEvaluated A v → v.cost = 0 →
      yv y v ≠ val ξ v → Spr d ξ from this _ v rfl hv hcost hne
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hn hv hcost hne
    have ih' : ∀ v', height v' < height v → ClearEvaluated A v' →
        v'.cost = 0 → yv y v' ≠ val ξ v' → Spr d ξ :=
      fun v' hlt => ih (height v') (by omega) v' rfl
    have hashStep {h p : Name} (hp : hashParent h = some p)
        (hc : child p = some h) (hpv : p = v) : Spr d ξ := by
      subst p
      have hhC : ClearEvaluated A h := clearEvaluated_child hv hc
      have hhE : Evaluated A h := (clearEvaluated_iff A h).1 hhC
      have hvE : Evaluated A v := (clearEvaluated_iff A v).1 hv
      have htag : tagNat ⟨v.len, yv y v⟩ = h.idx := tagNat_yv hy hp hvE
      cases h with
      | ch k t =>
          simp only [hashParent, Option.some.injEq] at hp
          subst v
          have hp₀ : hashParent (Name.ch k t) = some (Name.ci k t) := rfl
          obtain ⟨w, hd, hw⟩ := yv_hash hy hp₀ hhE
          by_cases hsp : lowWord w = lowWord (ξ.2 (Name.ch k t).fin)
          · exact ⟨Name.ch k t, Name.ci k t, hp₀,
              yv y (Name.ci k t), hne, htag, w, hd,
              (bindingValue_ch k t w).trans
                (hsp.trans (bindingValue_ch k t _).symm)⟩
          · have hzC : ClearEvaluated A (Name.cv k t) :=
              clearEvaluated_child hhC rfl
            have hzE : Evaluated A (Name.cv k t) :=
              (clearEvaluated_iff A _).1 hzC
            refine ih' (Name.cv k t) ?_ hzC rfl ?_
            · have h₁ := height_child hc
              have h₂ := height_child
                (show child (Name.ch k t) = some (Name.cv k t) by rfl)
              omega
            · intro heq
              apply hsp
              exact hw.trans ((yv_cv hy hzE).symm.trans
                (heq.trans (val_cv ξ k t)))
      | sh j =>
          simp only [hashParent, Option.some.injEq] at hp
          subst v
          have hp₀ : hashParent (Name.sh j) = some (Name.sc j) := rfl
          obtain ⟨w, hd, hw⟩ := yv_hash hy hp₀ hhE
          by_cases hsp : lowWord w = lowWord (ξ.2 (Name.sh j).fin)
          · exact ⟨Name.sh j, Name.sc j, hp₀, yv y (Name.sc j),
              hne, htag, w, hd, (bindingValue_sh j w).trans
                (hsp.trans (bindingValue_sh j _).symm)⟩
          · have hzC : ClearEvaluated A (Name.sv j) :=
              clearEvaluated_child hhC rfl
            have hzE : Evaluated A (Name.sv j) :=
              (clearEvaluated_iff A _).1 hzC
            refine ih' (Name.sv j) ?_ hzC rfl ?_
            · have h₁ := height_child hc
              have h₂ := height_child
                (show child (Name.sh j) = some (Name.sv j) by rfl)
              omega
            · intro heq
              apply hsp
              exact hw.trans ((yv_sv hy hzE).symm.trans
                (heq.trans (val_sv ξ j)))
      | mh u =>
          simp only [hashParent, Option.some.injEq] at hp
          subst v
          have hp₀ : hashParent (Name.mh u) = some (Name.mc u) := rfl
          obtain ⟨w, hd, hw⟩ := yv_hash hy hp₀ hhE
          by_cases hsp : lowWord w = lowWord (ξ.2 (Name.mh u).fin)
          · exact ⟨Name.mh u, Name.mc u, hp₀, yv y (Name.mc u),
              hne, htag, w, hd, (bindingValue_mh u w).trans
                (hsp.trans (bindingValue_mh u _).symm)⟩
          · have hzC : ClearEvaluated A (Name.mv u) :=
              clearEvaluated_child hhC rfl
            have hzE : Evaluated A (Name.mv u) :=
              (clearEvaluated_iff A _).1 hzC
            refine ih' (Name.mv u) ?_ hzC rfl ?_
            · have h₁ := height_child hc
              have h₂ := height_child
                (show child (Name.mh u) = some (Name.mv u) by rfl)
              omega
            · intro heq
              apply hsp
              exact hw.trans ((yv_mv hy hzE).symm.trans
                (heq.trans (val_mv ξ u)))
      | rh =>
          simp only [hashParent, Option.some.injEq] at hp
          subst v
          have hp₀ : hashParent Name.rh = some Name.rc := rfl
          obtain ⟨w, hd, hw⟩ := yv_hash_lowPk hy hp₀ hhE
          refine ⟨Name.rh, Name.rc, hp₀, yv y Name.rc, hne, htag,
            w, hd, ?_⟩
          change lowPk w = pkOf ξ
          exact hw.trans hacc
      | src k => simp [hashParent] at hp
      | ci k t => simp [hashParent] at hp
      | cv k t => simp [hashParent] at hp
      | sc j => simp [hashParent] at hp
      | sv j => simp [hashParent] at hp
      | mc u => simp [hashParent] at hp
      | mv u => simp [hashParent] at hp
      | rc => simp [hashParent] at hp
    cases v with
    | src k =>
        have hc : child (Name.src k) = some (Name.ci k 0) := rfl
        have hcC := clearEvaluated_child hv hc
        have hcE := (clearEvaluated_iff A _).1 hcC
        refine ih' (Name.ci k 0) (by have hh := height_child hc; omega)
          hcC rfl ?_
        intro heq
        rw [yv_ci hy hcE, val_ci] at heq
        have hp := (bv_append_inj heq).2
        apply hne
        exact eq_of_lowWord_eq (show (Name.src k).len = 129 by rfl) hp
    | ci k t => exact hashStep rfl rfl rfl
    | ch k t => exact absurd hcost (by simp [Name.cost])
    | cv k t =>
        by_cases ht : t.val = 17
        · have ht' : t = 17 := Fin.ext ht
          subst t
          cases hl : lowerOfChain k with
          | some j =>
              have hc : child (Name.cv k 17) = some (Name.sc j) := by
                simp [Name.child, hl]
              have hcC := clearEvaluated_child hv hc
              have hcE := (clearEvaluated_iff A _).1 hcC
              obtain ⟨a, ha⟩ := lowerChain_witness hl
              refine ih' (Name.sc j) (by have hh := height_child hc; omega)
                hcC rfl ?_
              intro heq
              rw [yv_sc hy hcE, val_sc'] at heq
              obtain ⟨h0, h1, h2⟩ := cat3_inj (bv_append_inj heq).2
              fin_cases a
              · subst k
                apply hne
                have hz : ((fun i : Fin 3 => i) ⟨0, by omega⟩) =
                    (0 : Fin 3) := by
                  apply Fin.ext
                  rfl
                rw [hz]
                exact h0
              · subst k
                apply hne
                have ho : ((fun i : Fin 3 => i) ⟨1, by omega⟩) =
                    (1 : Fin 3) := by
                  apply Fin.ext
                  rfl
                rw [ho]
                exact h1
              · subst k
                apply hne
                have ht : ((fun i : Fin 3 => i) ⟨2, by omega⟩) =
                    (2 : Fin 3) := by
                  apply Fin.ext
                  rfl
                rw [ht]
                exact h2
          | none =>
              have hc : child (Name.cv k 17) = some (Name.mc (upperOfChain k)) := by
                simp [Name.child, hl]
              have hcC := clearEvaluated_child hv hc
              have hcE := (clearEvaluated_iff A _).1 hcC
              obtain ⟨a, ha⟩ := direct_midChild_witness hl
              refine ih' (Name.mc (upperOfChain k))
                (by have hh := height_child hc; omega) hcC rfl ?_
              intro heq
              rw [yv_mc hy hcE, val_mc] at heq
              obtain ⟨h0, h1, h2⟩ := cat3_inj (bv_append_inj heq).2
              fin_cases a
              · apply hne
                apply eq_of_lowWord_eq
                  (show (Name.cv k 17).len = 129 by rfl)
                have ha' : midChild (upperOfChain k) 0 = Name.cv k 17 := by
                  simpa using ha
                exact transport_lowWord_eq ha' h0
              · apply hne
                apply eq_of_lowWord_eq
                  (show (Name.cv k 17).len = 129 by rfl)
                have ha' : midChild (upperOfChain k) 1 = Name.cv k 17 := by
                  simpa using ha
                exact transport_lowWord_eq ha' h1
              · apply hne
                apply eq_of_lowWord_eq
                  (show (Name.cv k 17).len = 129 by rfl)
                have ha' : midChild (upperOfChain k) 2 = Name.cv k 17 := by
                  simpa using ha
                exact transport_lowWord_eq ha' h2
        · have hc : child (Name.cv k t) =
              some (Name.ci k ⟨t.val + 1, by omega⟩) := by
            simp [Name.child, ht]
          have hcC := clearEvaluated_child hv hc
          have hcE := (clearEvaluated_iff A _).1 hcC
          refine ih' _ (by have hh := height_child hc; omega) hcC rfl ?_
          intro heq
          rw [yv_ci hy hcE, val_ci] at heq
          have hp := (bv_append_inj heq).2
          apply hne
          rw [prev_succ k t (by omega)] at hp
          exact eq_of_lowWord_eq (show (Name.cv k t).len = 129 by rfl) hp
    | sc j => exact hashStep rfl rfl rfl
    | sh j => exact absurd hcost (by simp [Name.cost])
    | sv j =>
        have hc : child (Name.sv j) = some (Name.mc (upperOfLower j)) := rfl
        have hcC := clearEvaluated_child hv hc
        have hcE := (clearEvaluated_iff A _).1 hcC
        obtain ⟨a, ha⟩ := lower_midChild_witness j
        refine ih' _ (by have hh := height_child hc; omega) hcC rfl ?_
        intro heq
        rw [yv_mc hy hcE, val_mc] at heq
        obtain ⟨h0, h1, h2⟩ := cat3_inj (bv_append_inj heq).2
        fin_cases a
        · apply hne
          apply eq_of_lowWord_eq (show (Name.sv j).len = 129 by rfl)
          have ha' : midChild (upperOfLower j) 0 = Name.sv j := by
            simpa using ha
          exact transport_lowWord_eq ha' h0
        · apply hne
          apply eq_of_lowWord_eq (show (Name.sv j).len = 129 by rfl)
          have ha' : midChild (upperOfLower j) 1 = Name.sv j := by
            simpa using ha
          exact transport_lowWord_eq ha' h1
        · apply hne
          apply eq_of_lowWord_eq (show (Name.sv j).len = 129 by rfl)
          have ha' : midChild (upperOfLower j) 2 = Name.sv j := by
            simpa using ha
          exact transport_lowWord_eq ha' h2
    | mc u => exact hashStep rfl rfl rfl
    | mh u => exact absurd hcost (by simp [Name.cost])
    | mv u =>
        have hc : child (Name.mv u) = some Name.rc := rfl
        have hcC := clearEvaluated_child hv hc
        have hcE := (clearEvaluated_iff A _).1 hcC
        refine ih' Name.rc (by have hh := height_child hc; omega)
          hcC rfl ?_
        intro heq
        rw [yv_rc hy hcE, val_rc'] at heq
        exact hne (congrFun (cat10_inj (bv_append_inj heq).2) u)
    | rc => exact hashStep rfl rfl rfl
    | rh => exact absurd hcost (by simp [Name.cost])

/-! ## Terminal no-signature authentication event -/

theorem not_mem_of_cut_len_ne {A : Finset Name} (hA : IsCut A)
    {n : Name} (hn : n.len ≠ 129) : n ∉ A := by
  intro hm
  exact hn (hA.values n hm)

/-- If no disclosure set has been fixed, every accepting reconstruction either
uses a spurious hash image or queries the honest root-hash input. -/
theorem events_none {A : Finset Name} (hA : IsCut A) {ξ : Rec} {d : Cache}
    {given y : graph.Assignment} (hy : graph.ReconEqs d (fins A) given y)
    (hacc : lowPk (yv y Name.rh) = pkOf ξ) :
    Spr d ξ ∨ Cache.Hits d (kc ξ) := by
  have hrA : Name.rh ∉ A :=
    not_mem_of_cut_len_ne hA (by simp [Name.len])
  have hrcA : Name.rc ∉ A :=
    not_mem_of_cut_len_ne hA (by simp [Name.len])
  have hrC : ClearEvaluated A Name.rh :=
    ⟨hrA, fun m hm => absurd hm (not_above_rh m)⟩
  have hrE : Evaluated A Name.rh := (clearEvaluated_iff A Name.rh).1 hrC
  obtain ⟨w, hd, -⟩ := yv_hash hy (h := Name.rh) (p := Name.rc) rfl hrE
  by_cases hne : yv y Name.rc = val ξ Name.rc
  · right
    refine ⟨⟨Name.rc.len, yv y Name.rc⟩, ?_, by rw [hd]; rfl⟩
    rw [kc_isSome_iff]
    exact ⟨Name.rh, Name.rc, rfl, by rw [hne]; rfl⟩
  · left
    apply up hy hacc (v := Name.rc) ?_ rfl hne
    refine ⟨hrcA, fun m hm => ?_⟩
    rw [above_of_child (show child Name.rc = some Name.rh by rfl)] at hm
    rcases hm with rfl | hm
    · exact hrA
    · exact absurd hm (not_above_rh m)

/-- The concrete verifier's public-key check is the low 128-bit endpoint of
the reconstructed root value. -/
theorem accepted_lowPk (ξ : Rec) (y : graph.Assignment)
    (h : scheme.publicKey y = pkOf ξ) :
    lowPk (yv y Name.rh) = pkOf ξ := by
  unfold yv
  rw [lowPk_cast_eq]
  exact h

/-- Every accepting verification in the failed-signature branch reaches one
of the two authentication events charged by `authPotential _ none`. -/
theorem accepted_none_event (ξ : Rec) (m : Message)
    (σ : WeightedScheme.Signature) (c d : Cache)
    (h : (true, d) ∈ support (run (scheme.verify (pkOf ξ) m σ) c)) :
    Spr d ξ ∨ Cache.Hits d (kc ξ) := by
  obtain ⟨_, hh⟩ :=
    WeightedScheme.verify_support scheme (pkOf ξ) m σ c (true, d) h
  obtain ⟨_w, _hw, i, _hi, _hlen, y, hy, hpk⟩ := hh rfl
  exact events_none (isCut_of_mem_family (setsName_mem i)) hy
    (accepted_lowPk ξ y hpk)

/-- Pointwise indicator domination at an accepting terminal verifier state. -/
theorem accepted_none_indicator (ξ : Rec) (m : Message)
    (σ : WeightedScheme.Signature) (c d : Cache)
    (h : (true, d) ∈ support (run (scheme.verify (pkOf ξ) m σ) c)) :
    (1 : ℝ≥0∞) ≤ ind (Cache.Hits d (kc ξ)) + ind (Spr d ξ) := by
  rcases accepted_none_event ξ m σ c d h with hs | hh
  · rw [show ind (Spr d ξ) = 1 by simp [ind, hs]]
    exact le_add_self
  · rw [show ind (Cache.Hits d (kc ξ)) = 1 by simp [ind, hh]]
    exact le_self_add

/-- The concrete terminal expectation bound used by both actual-game budget
branches: verifier success is dominated by the two authentication indicators. -/
theorem accepted_none_expected (ξ : Rec) (m : Message)
    (σ : WeightedScheme.Signature) (c : Cache) :
    E (run (scheme.verify (pkOf ξ) m σ) c)
        (fun p => if p.1 = true then 1 else 0) ≤
      E (run (scheme.verify (pkOf ξ) m σ) c)
        (fun p => ind (Cache.Hits p.2 (kc ξ)) + ind (Spr p.2 ξ)) := by
  apply expectedValue_mono_of_support
  rintro ⟨b, d⟩ hd
  cases b
  · simp
  · exact accepted_none_indicator ξ m σ c d hd

#print axioms visited_iff_clear
#print axioms yv_hash
#print axioms up
#print axioms accepted_none_event
#print axioms accepted_none_expected

end OptimalOTS.WeightedConstruction.LongChain91
