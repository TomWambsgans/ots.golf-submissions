import Submissions.UpperCompressions.LongChain91Dag
import Submissions.UpperCompressions.ProofBundle03

/-!
# Concrete cut bridge for the cost-90 long-chain graph

This module connects the combinatorial cuts in `LongChain91Geometry` to the
protected `Dag.Graph` interface.  The cost proof uses a direct charging
argument: every evaluated chain hash belongs to the suffix selected by its
chain position, every evaluated lower or upper hash is charged to the
corresponding expanded frontier node, and the root costs three compressions.
-/

open OracleSpec OracleComp ENNReal
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace OptimalOTS.WeightedConstruction.LongChain91

open OptimalOTS.Dag
open Name

/-! ## Names and graph sets -/

/-- The name/index equivalence, viewed at the graph's definitional size. -/
def graphNameEquiv : Name ≃ Fin graph.size :=
  Name.nameEquiv

def nameEmbedding : Name ↪ Fin graph.size :=
  graphNameEquiv.toEmbedding

@[simp] theorem nameEmbedding_apply (n : Name) : nameEmbedding n = n.fin := rfl

/-- Map a set of concrete names to the corresponding graph vertices. -/
def fins (A : Finset Name) : Finset (Fin graph.size) :=
  A.map nameEmbedding

@[simp] theorem mem_fins_embedding (A : Finset Name) (n : Name) :
    nameEmbedding n ∈ fins A ↔ n ∈ A :=
  Finset.mem_map' nameEmbedding

/-- Graph parent membership is exactly the concrete one-child relation. -/
theorem mem_graph_parents_iff (m n : Name) :
    m.fin ∈ (graph.kind n.fin).parents ↔ child m = some n := by
  rw [graph_parents_fin]
  exact (Finset.mem_map' _).trans (Name.mem_parents_iff m n)

/-! ## The one-child ancestry relation -/

/-- `Above m n` means that following `child` from `n` reaches `m` after at
least one step. -/
inductive Above : Name → Name → Prop
  | child {m n : Name} : child n = some m → Above m n
  | step {m n p : Name} : child n = some p → Above m p → Above m n

theorem Above.trans {a b c : Name} (h₁ : Above a b) (h₂ : Above b c) : Above a c := by
  revert h₁
  induction h₂ with
  | child h => intro h₁; exact Above.step h h₁
  | step h _ ih => intro h₁; exact Above.step h (ih h₁)

theorem above_of_child {m n p : Name} (h : child n = some p) :
    Above m n ↔ m = p ∨ Above m p := by
  constructor
  · intro ha
    cases ha with
    | child h' => rw [h, Option.some.injEq] at h'; exact Or.inl h'.symm
    | step h' ha' => rw [h, Option.some.injEq] at h'; subst h'; exact Or.inr ha'
  · rintro (rfl | ha)
    · exact Above.child h
    · exact Above.step h ha

theorem not_above_rh (m : Name) : ¬ Above m .rh := by
  intro h
  cases h with
  | child h' => simp [Name.child] at h'
  | step h' _ => simp [Name.child] at h'

/-- A visited node has no strictly higher disclosed ancestor.  This is the
only direction of the generic tree characterization needed for the upper
bound and source-coverage obligations. -/
theorem visited_no_above (A : Finset Name) {n : Name}
    (hv : graph.Visited (fins A) (nameEmbedding n)) : ∀ m, Above m n → m ∉ A := by
  have hv' : graph.Visited (fins A) n.fin := by
    simpa only [nameEmbedding_apply] using hv
  have key : ∀ v, graph.Visited (fins A) v →
      ∀ n : Name, n.fin = v → ∀ m, Above m n → m ∉ A := by
    intro v hv
    induction hv with
    | root =>
        intro n hn m hm
        have hr : n = .rh := Name.fin_injective hn
        subst hr
        exact absurd hm (not_above_rh m)
    | parent hw hwA hv ih =>
        rename_i w v
        intro n hn m hm hmA
        subst hn
        obtain ⟨w', rfl⟩ : ∃ w' : Name, w'.fin = w :=
          ⟨Name.ofFin w, Name.fin_ofFin w⟩
        have hc : child n = some w' := (mem_graph_parents_iff n w').mp hv
        rw [above_of_child hc] at hm
        rcases hm with rfl | hm
        · exact hwA (by
            simpa only [nameEmbedding_apply] using
              (mem_fins_embedding A m).mpr hmA)
        · exact ih w' rfl m hm hmA
  exact key _ hv' n rfl

/-! ## Explicit path witnesses -/

/-- Reflexive ancestry, convenient when advancing through a chain. -/
def AtOrAbove (m n : Name) : Prop := m = n ∨ Above m n

theorem AtOrAbove.refl (n : Name) : AtOrAbove n n := Or.inl rfl

theorem AtOrAbove.ofAbove {m n : Name} (h : Above m n) : AtOrAbove m n := Or.inr h

theorem AtOrAbove.trans {a b c : Name} (h₁ : AtOrAbove a b)
    (h₂ : AtOrAbove b c) : AtOrAbove a c := by
  rcases h₁ with rfl | h₁
  · exact h₂
  rcases h₂ with rfl | h₂
  · exact Or.inr h₁
  · exact Or.inr (h₁.trans h₂)

theorem above_cv_succ (k : Fin 66) (t : Fin 18) (ht : t.val < 17) :
    Above (.cv k ⟨t.val + 1, by omega⟩) (.cv k t) := by
  have h₁ : child (.cv k t) = some (.ci k ⟨t.val + 1, by omega⟩) := by
    simp only [Name.child]
    rw [dif_neg (by omega)]
  have h₂ : Above (.ch k ⟨t.val + 1, by omega⟩)
      (.ci k ⟨t.val + 1, by omega⟩) := Above.child rfl
  have h₃ : Above (.cv k ⟨t.val + 1, by omega⟩)
      (.ch k ⟨t.val + 1, by omega⟩) := Above.child rfl
  exact h₃.trans (h₂.trans (Above.child h₁))

/-- Later chain values are at or above earlier chain values. -/
theorem atOrAbove_cv_of_le (k : Fin 66) (t s : Fin 18) (h : t.val ≤ s.val) :
    AtOrAbove (.cv k s) (.cv k t) := by
  by_cases heq : t = s
  · subst s
    exact AtOrAbove.refl _
  · have hlt : t.val < s.val := by
      have hne : t.val ≠ s.val := fun hv => heq (Fin.ext hv)
      omega
    let t' : Fin 18 := ⟨t.val + 1, by omega⟩
    have hr : AtOrAbove (.cv k s) (.cv k t') :=
      atOrAbove_cv_of_le k t' s (by dsimp [t']; omega)
    exact hr.trans (AtOrAbove.ofAbove (above_cv_succ k t (by omega)))
termination_by s.val - t.val
decreasing_by omega

theorem above_mc_cv_last (k : Fin 66) :
    Above (.mc (upperOfChain k)) (.cv k 17) := by
  cases hl : lowerOfChain k with
  | none =>
      exact Above.child (by simp [Name.child, hl])
  | some j =>
      have hu : upperOfChain k = upperOfLower j := upperOfChain_eq_upperOfLower hl
      have h₁ : Above (.sc j) (.cv k 17) := Above.child (by simp [Name.child, hl])
      have h₂ : Above (.sh j) (.sc j) := Above.child rfl
      have h₃ : Above (.sv j) (.sh j) := Above.child rfl
      have h₄ : Above (.mc (upperOfLower j)) (.sv j) := Above.child rfl
      rw [hu]
      exact h₄.trans (h₃.trans (h₂.trans h₁))

theorem above_mv_mc (u : Fin 10) : Above (.mv u) (.mc u) := by
  exact (Above.child (show child (.mh u) = some (.mv u) by rfl)).trans
    (Above.child (show child (.mc u) = some (.mh u) by rfl))

theorem above_mv_cv (k : Fin 66) (t : Fin 18) :
    Above (.mv (upperOfChain k)) (.cv k t) := by
  have hlast : Above (.mv (upperOfChain k)) (.cv k 17) :=
    (above_mv_mc _).trans (above_mc_cv_last k)
  have hr := atOrAbove_cv_of_le k t (17 : Fin 18) (by omega)
  rcases hr with h | h
  · simpa only [h] using hlast
  · exact hlast.trans h

theorem above_mv_ch (k : Fin 66) (t : Fin 18) :
    Above (.mv (upperOfChain k)) (.ch k t) :=
  (above_mv_cv k t).trans (Above.child rfl)

theorem above_sv_cv_last {k : Fin 66} {j : Fin 18}
    (hl : lowerOfChain k = some j) : Above (.sv j) (.cv k 17) := by
  have h₁ : Above (.sc j) (.cv k 17) := Above.child (by simp [Name.child, hl])
  have h₂ : Above (.sh j) (.sc j) := Above.child rfl
  have h₃ : Above (.sv j) (.sh j) := Above.child rfl
  exact h₃.trans (h₂.trans h₁)

theorem above_sv_ch {k : Fin 66} {j : Fin 18} (t : Fin 18)
    (hl : lowerOfChain k = some j) : Above (.sv j) (.ch k t) := by
  have hlast := above_sv_cv_last hl
  have hr := atOrAbove_cv_of_le k t (17 : Fin 18) (by omega)
  have hcv : Above (.cv k t) (.ch k t) := Above.child rfl
  rcases hr with h | h
  · have ht : Above (.sv j) (.cv k t) := by simpa only [h] using hlast
    exact ht.trans hcv
  · exact hlast.trans (h.trans hcv)

theorem above_chainNode_ch {k : Fin 66} {p : Fin 19} (t : Fin 18)
    (hpt : t.val < p.val) : Above (chainNode k p) (.ch k t) := by
  have hp0 : p.val ≠ 0 := by omega
  let s : Fin 18 := ⟨p.val - 1, by omega⟩
  have hr : AtOrAbove (.cv k s) (.cv k t) :=
    atOrAbove_cv_of_le k t s (by dsimp [s]; omega)
  have hcv : Above (.cv k t) (.ch k t) := Above.child rfl
  have hout : Above (.cv k s) (.ch k t) := by
    rcases hr with h | h
    · rw [h]
      exact hcv
    · exact h.trans hcv
  simpa [chainNode, hp0, s] using hout

theorem above_cv_src (k : Fin 66) (t : Fin 18) : Above (.cv k t) (.src k) := by
  have hzero : Above (.cv k 0) (.src k) := by
    exact (Above.child (show child (.ch k 0) = some (.cv k 0) by rfl)).trans
      ((Above.child (show child (.ci k 0) = some (.ch k 0) by rfl)).trans
        (Above.child (show child (.src k) = some (.ci k 0) by rfl)))
  have hr := atOrAbove_cv_of_le k 0 t (by omega)
  rcases hr with h | h
  · rw [h]
    exact hzero
  · exact h.trans hzero

theorem above_sv_src {k : Fin 66} {j : Fin 18} (hl : lowerOfChain k = some j) :
    Above (.sv j) (.src k) :=
  (above_sv_cv_last hl).trans (above_cv_src k 17)

theorem above_mv_src (k : Fin 66) : Above (.mv (upperOfChain k)) (.src k) :=
  (above_mv_cv k 0).trans
    ((Above.child (show child (.ch k 0) = some (.cv k 0) by rfl)).trans
      ((Above.child (show child (.ci k 0) = some (.ch k 0) by rfl)).trans
        (Above.child (show child (.src k) = some (.ci k 0) by rfl))))

theorem onPath_eq_source_or_above {k : Fin 66} {n : Name} (h : OnPath k n) :
    n = .src k ∨ Above n (.src k) := by
  rcases h with rfl | ⟨t, rfl⟩ | ⟨j, hl, rfl⟩ | rfl
  · exact Or.inl rfl
  · exact Or.inr (above_cv_src k t)
  · exact Or.inr (above_sv_src hl)
  · exact Or.inr (above_mv_src k)

theorem cutOf_covers_sources (c : Choice) (k : Fin 66) :
    .src k ∈ cutOf c ∨ ∃ m ∈ cutOf c, Above m (.src k) := by
  have hm := selected_mem_cutOf c k
  rcases onPath_eq_source_or_above (selected_onPath c k) with h | h
  · exact Or.inl (h ▸ hm)
  · exact Or.inr ⟨selected c k, hm, h⟩

/-! ## Graph obligations -/

theorem root_not_mem_cutOf (c : Choice) : graph.root ∉ fins (cutOf c) := by
  have hroot : graph.root = nameEmbedding Name.rh := by
    change Name.rh.fin = nameEmbedding Name.rh
    exact (nameEmbedding_apply _).symm
  rw [hroot, mem_fins_embedding]
  intro hr
  have hv := cutOf_values c .rh hr
  simp [Name.len] at hv

theorem no_hidden_source_cutOf (c : Choice) :
    ∀ v, graph.Visited (fins (cutOf c)) v → v ∉ fins (cutOf c) →
      ¬ (graph.kind v).IsSource := by
  intro v hv hvA hs
  obtain ⟨n, rfl⟩ : ∃ n : Name, n.fin = v := ⟨Name.ofFin v, Name.fin_ofFin v⟩
  obtain ⟨k, rfl⟩ := (graph_isSource_fin n).mp hs
  rcases cutOf_covers_sources c k with hs | ⟨m, hm, ha⟩
  · exact hvA (by
      simpa only [nameEmbedding_apply] using
        (mem_fins_embedding (cutOf c) (.src k)).mpr hs)
  · exact (visited_no_above (cutOf c) hv m ha) hm

/-! ## Disclosure size -/

/-- The A and B parts of an arbitrary set of upper vertices. -/
def splitA (U : Finset (Fin 10)) : Finset (Fin 8) :=
  Finset.univ.filter fun i => aNode i ∈ U

def splitB (U : Finset (Fin 10)) : Finset (Fin 2) :=
  Finset.univ.filter fun i => bNode i ∈ U

@[simp] theorem mem_splitA (U : Finset (Fin 10)) (i : Fin 8) :
    i ∈ splitA U ↔ aNode i ∈ U := by simp [splitA]

@[simp] theorem mem_splitB (U : Finset (Fin 10)) (i : Fin 2) :
    i ∈ splitB U ↔ bNode i ∈ U := by simp [splitB]

theorem upperFrom_split (U : Finset (Fin 10)) :
    upperFrom (splitA U) (splitB U) = U := by
  ext u
  by_cases hu : u.val < 8
  · let i : Fin 8 := ⟨u.val, hu⟩
    have hui : aNode i = u := by apply Fin.ext; rfl
    rw [← hui, aNode_mem_upperFrom]
    simp
  · let i : Fin 2 := ⟨u.val - 8, by omega⟩
    have hui : bNode i = u := by
      apply Fin.ext
      simp [bNode, i]
      omega
    rw [← hui, bNode_mem_upperFrom]
    simp

@[simp] theorem lowerA_mem_lowerAvail (A : Finset (Fin 8))
    (B : Finset (Fin 2)) (x : Fin 8 × Fin 2) :
    lowerA x ∈ lowerAvail A B ↔ x.1 ∈ A := by
  simp only [lowerAvail, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨y, hy, heq⟩ | ⟨i, hi, heq⟩)
    · have hxy : y = x := lowerA_injective heq
      subst y
      exact (Finset.mem_product.mp hy).1
    · have hv := congrArg Fin.val heq
      simp [lowerA, lowerB] at hv
      omega
  · intro hx
    exact Or.inl ⟨x, Finset.mem_product.mpr ⟨hx, Finset.mem_univ _⟩, rfl⟩

@[simp] theorem lowerB_mem_lowerAvail (A : Finset (Fin 8))
    (B : Finset (Fin 2)) (i : Fin 2) :
    lowerB i ∈ lowerAvail A B ↔ i ∈ B := by
  simp only [lowerAvail, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨x, hx, heq⟩ | ⟨j, hj, heq⟩)
    · have hv := congrArg Fin.val heq
      simp [lowerA, lowerB] at hv
      omega
    · exact lowerB_injective heq ▸ hj
  · intro hi
    exact Or.inr ⟨i, hi, rfl⟩

@[simp] theorem upperOfLower_lowerA (x : Fin 8 × Fin 2) :
    upperOfLower (lowerA x) = aNode x.1 := by
  apply Fin.ext
  unfold upperOfLower
  rw [dif_pos (by simp [lowerA]; omega)]
  simp [lowerA, aNode]
  omega

@[simp] theorem upperOfLower_lowerB (i : Fin 2) :
    upperOfLower (lowerB i) = bNode i := by
  apply Fin.ext
  simp [upperOfLower, lowerB, bNode]
  omega

theorem lowerAvail_split (U : Finset (Fin 10)) :
    lowerAvail (splitA U) (splitB U) = availableLower U := by
  ext j
  by_cases hj : j.val < 16
  · let i : Fin 8 := ⟨j.val / 2, by omega⟩
    let r : Fin 2 := ⟨j.val % 2, by omega⟩
    have heq : lowerA (i, r) = j := by
      apply Fin.ext
      simp [lowerA, i, r]
      omega
    rw [← heq, lowerA_mem_lowerAvail, mem_availableLower,
      upperOfLower_lowerA, mem_splitA]
  · let i : Fin 2 := ⟨j.val - 16, by omega⟩
    have heq : lowerB i = j := by
      apply Fin.ext
      simp [lowerB, i]
      omega
    rw [← heq, lowerB_mem_lowerAvail, mem_availableLower,
      upperOfLower_lowerB, mem_splitB]

/-- Cardinality of the cut, before inserting the frontier arithmetic. -/
theorem card_cutOf_parts (c : Choice) :
    (cutOf c).card = (upperStops c.frontier).card +
      (lowerStops c.frontier).card + (active c.frontier).card := by
  have huv : Disjoint
      ((upperStops c.frontier).image Name.mv)
      ((lowerStops c.frontier).image Name.sv) := by
    apply Finset.disjoint_left.mpr
    intro n hnU hnL
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hnU
    obtain ⟨j, _, h⟩ := Finset.mem_image.mp hnL
    contradiction
  have huc : Disjoint
      ((upperStops c.frontier).image Name.mv)
      ((active c.frontier).image fun k => chainNode k (c.position k)) := by
    apply Finset.disjoint_left.mpr
    intro n hnU hnC
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hnU
    obtain ⟨k, _, h⟩ := Finset.mem_image.mp hnC
    unfold chainNode at h
    split_ifs at h
  have hlc : Disjoint
      ((lowerStops c.frontier).image Name.sv)
      ((active c.frontier).image fun k => chainNode k (c.position k)) := by
    apply Finset.disjoint_left.mpr
    intro n hnL hnC
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hnL
    obtain ⟨k, _, h⟩ := Finset.mem_image.mp hnC
    unfold chainNode at h
    split_ifs at h
  rw [cutOf, Finset.card_union_of_disjoint
      (Finset.disjoint_union_left.mpr ⟨huc, hlc⟩),
    Finset.card_union_of_disjoint huv,
    Finset.card_image_of_injective _ (fun _ _ h => Name.mv.inj h),
    Finset.card_image_of_injective _ (fun _ _ h => Name.sv.inj h),
    Finset.card_image_of_injective _ (chainNode_injective c.position)]

/-- A well-formed structural frontier has exactly its advertised number of
129-bit disclosure words. -/
theorem card_cutOf (c : Choice) (hw : c.frontier.WellFormed) :
    (cutOf c).card = c.frontier.words := by
  let A := splitA c.frontier.upper
  let B := splitB c.frontier.upper
  have hupper : upperFrom A B = c.frontier.upper := upperFrom_split _
  have hlower : lowerAvail A B = availableLower c.frontier.upper := lowerAvail_split _
  have hL : c.frontier.lower ⊆ lowerAvail A B := by
    rw [hlower]
    exact hw
  have hactive : (active c.frontier).card =
      3 * c.frontier.lower.card + A.card + 2 * B.card := by
    have heq := rawActive_eq_active A B c.frontier.lower hL
    rw [hupper] at heq
    rw [← heq, card_rawActive]
  have hU : c.frontier.upper.card = A.card + B.card := by
    rw [← hupper, card_upperFrom]
  have hAvail : (availableLower c.frontier.upper).card = 2 * A.card + B.card := by
    rw [← hlower, card_lowerAvail]
  have hUpperStops : (upperStops c.frontier).card = 10 - c.frontier.upper.card := by
    rw [upperStops, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin]
  have hLowerStops : (lowerStops c.frontier).card =
      (availableLower c.frontier.upper).card - c.frontier.lower.card := by
    rw [lowerStops, Finset.card_sdiff_of_subset hw]
  rw [card_cutOf_parts, hUpperStops, hLowerStops, hactive,
    hU, hAvail]
  unfold Frontier.words Frontier.expanded
  have hAc := Finset.card_le_card hL
  rw [card_lowerAvail] at hAc
  have hUle : A.card + B.card ≤ 10 := by
    rw [← hU]
    exact Finset.card_le_univ _
  rw [hU]
  omega

theorem revealBits_fins (A : Finset Name) :
    graph.revealBits (fins A) = ∑ n ∈ A, n.len := by
  unfold Graph.revealBits
  refine (Finset.sum_map A nameEmbedding graph.len).trans ?_
  exact Finset.sum_congr rfl fun n _ => by
    rw [nameEmbedding_apply, graph_len_fin]

theorem revealBits_cutOf {c : Choice} (hc : c ∈ shapes) :
    graph.revealBits (fins (cutOf c)) ≤ 42 * 129 := by
  have hv := valid_of_mem_shapes hc
  rw [revealBits_fins]
  calc
    ∑ n ∈ cutOf c, n.len = ∑ _n ∈ cutOf c, 129 :=
      Finset.sum_congr rfl fun n hn => cutOf_values c n hn
    _ = (cutOf c).card * 129 := by rw [Finset.sum_const, smul_eq_mul]
    _ = c.frontier.words * 129 := by rw [card_cutOf c hv.1]
    _ ≤ 42 * 129 := Nat.mul_le_mul_right 129 (Choice.words_le hv)

theorem disclosure_and_nonce_le {c : Choice} (hc : c ∈ shapes) :
    graph.revealBits (fins (cutOf c)) + 86 ≤ 5504 := by
  have h := revealBits_cutOf hc
  norm_num at h ⊢
  omega

/-! ## Reconstruction charges -/

/-- A concrete name is evaluated exactly when the generic reconstruction
visits it and it is not itself disclosed. -/
def Evaluated (A : Finset Name) (n : Name) : Prop :=
  graph.Visited (fins A) (nameEmbedding n) ∧ n ∉ A

theorem mem_evaluated_iff (A : Finset Name) (n : Name) :
    nameEmbedding n ∈ graph.evaluated (fins A) ↔ Evaluated A n := by
  unfold Graph.evaluated Evaluated
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_fins_embedding]

def evaluatedNames (A : Finset Name) : Finset Name :=
  Finset.univ.filter (Evaluated A)

theorem evaluated_eq_fins (A : Finset Name) :
    graph.evaluated (fins A) = fins (evaluatedNames A) := by
  ext v
  obtain ⟨n, rfl⟩ : ∃ n : Name, nameEmbedding n = v :=
    ⟨graphNameEquiv.symm v, graphNameEquiv.apply_symm_apply v⟩
  rw [mem_evaluated_iff, mem_fins_embedding]
  simp [evaluatedNames]

theorem evaluated_mh_implies_upper (c : Choice) (u : Fin 10)
    (h : Evaluated (cutOf c) (.mh u)) : u ∈ c.frontier.upper := by
  by_contra hu
  have hm : Name.mv u ∈ cutOf c := by
    rw [mv_mem_cutOf_iff]
    simp [upperStops, hu]
  exact (visited_no_above (cutOf c) h.1 (.mv u) (Above.child rfl)) hm

theorem above_mv_sh (j : Fin 18) :
    Above (.mv (upperOfLower j)) (.sh j) := by
  exact (above_mv_mc _).trans
    ((Above.child (show child (.sv j) = some (.mc (upperOfLower j)) by rfl)).trans
      (Above.child (show child (.sh j) = some (.sv j) by rfl)))

theorem evaluated_sh_implies_lower (c : Choice) (j : Fin 18)
    (h : Evaluated (cutOf c) (.sh j)) : j ∈ c.frontier.lower := by
  have hu : upperOfLower j ∈ c.frontier.upper := by
    by_contra hu
    have hm : Name.mv (upperOfLower j) ∈ cutOf c := by
      rw [mv_mem_cutOf_iff]
      simp [upperStops, hu]
    exact (visited_no_above (cutOf c) h.1 _ (above_mv_sh j)) hm
  by_contra hj
  have hs : Name.sv j ∈ cutOf c := by
    rw [sv_mem_cutOf_iff]
    simp [lowerStops, mem_availableLower, hu, hj]
  exact (visited_no_above (cutOf c) h.1 _ (Above.child rfl)) hs

theorem evaluated_ch_implies (c : Choice) (k : Fin 66) (t : Fin 18)
    (h : Evaluated (cutOf c) (.ch k t)) :
    k ∈ active c.frontier ∧ (c.position k).val ≤ t.val := by
  have hu : upperOfChain k ∈ c.frontier.upper := by
    by_contra hu
    have hm : Name.mv (upperOfChain k) ∈ cutOf c := by
      rw [mv_mem_cutOf_iff]
      simp [upperStops, hu]
    exact (visited_no_above (cutOf c) h.1 _ (above_mv_ch k t)) hm
  have hk : k ∈ active c.frontier := by
    rw [mem_active]
    refine ⟨hu, ?_⟩
    cases hl : lowerOfChain k with
    | none => trivial
    | some j =>
        by_contra hj
        have hs : Name.sv j ∈ cutOf c := by
          rw [sv_mem_cutOf_iff]
          have hua : upperOfLower j ∈ c.frontier.upper := by
            rw [← upperOfChain_eq_upperOfLower hl]
            exact hu
          simp [lowerStops, mem_availableLower, hua, hj]
        exact (visited_no_above (cutOf c) h.1 _ (above_sv_ch t hl)) hs
  refine ⟨hk, ?_⟩
  by_contra hp
  have hc : chainNode k (c.position k) ∈ cutOf c :=
    (chainNode_mem_cutOf_iff c k _).2 ⟨hk, rfl⟩
  exact (visited_no_above (cutOf c) h.1 _
    (above_chainNode_ch t (by omega))) hc

/-- The structural charge assigned to each possible evaluated node. -/
def charge (c : Choice) : Name → ℕ
  | .ch k t => if k ∈ active c.frontier ∧ (c.position k).val ≤ t.val then 1 else 0
  | .sh j => if j ∈ c.frontier.lower then 1 else 0
  | .mh u => if u ∈ c.frontier.upper then 1 else 0
  | .rh => 3
  | _ => 0

theorem evaluated_cost_le_charge (c : Choice) (n : Name) :
    (if Evaluated (cutOf c) n then n.cost else 0) ≤ charge c n := by
  cases n with
  | ch k t =>
      by_cases h : Evaluated (cutOf c) (.ch k t)
      · simp [h, charge, Name.cost, evaluated_ch_implies c k t h]
      · simp [h]
  | sh j =>
      by_cases h : Evaluated (cutOf c) (.sh j)
      · simp [h, charge, Name.cost, evaluated_sh_implies_lower c j h]
      · simp [h]
  | mh u =>
      by_cases h : Evaluated (cutOf c) (.mh u)
      · simp [h, charge, Name.cost, evaluated_mh_implies_upper c u h]
      · simp [h]
  | rh =>
      by_cases h : Evaluated (cutOf c) .rh <;> simp [h, charge, Name.cost]
  | src k | ci k t | cv k t | sc k | sv k | mc k | mv k | rc =>
      simp [charge, Name.cost]

/-! Splitting sums over `Name` by constructor. -/

abbrev NameSum :=
  Fin 66 ⊕ (Fin 66 × Fin 18) ⊕ (Fin 66 × Fin 18) ⊕
    (Fin 66 × Fin 18) ⊕ Fin 18 ⊕ Fin 18 ⊕ Fin 18 ⊕
      Fin 10 ⊕ Fin 10 ⊕ Fin 10 ⊕ Unit ⊕ Unit

def Name.toSum : Name → NameSum
  | .src k => .inl k
  | .ci k t => .inr (.inl (k, t))
  | .ch k t => .inr (.inr (.inl (k, t)))
  | .cv k t => .inr (.inr (.inr (.inl (k, t))))
  | .sc j => .inr (.inr (.inr (.inr (.inl j))))
  | .sh j => .inr (.inr (.inr (.inr (.inr (.inl j)))))
  | .sv j => .inr (.inr (.inr (.inr (.inr (.inr (.inl j))))))
  | .mc u => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl u)))))))
  | .mh u => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl u))))))))
  | .mv u => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl u)))))))))
  | .rc => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))))))
  | .rh => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (())))))))))))

def Name.ofSum : NameSum → Name
  | .inl k => .src k
  | .inr (.inl (k, t)) => .ci k t
  | .inr (.inr (.inl (k, t))) => .ch k t
  | .inr (.inr (.inr (.inl (k, t)))) => .cv k t
  | .inr (.inr (.inr (.inr (.inl j)))) => .sc j
  | .inr (.inr (.inr (.inr (.inr (.inl j))))) => .sh j
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl j)))))) => .sv j
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl u))))))) => .mc u
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl u)))))))) => .mh u
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl u))))))))) => .mv u
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ())))))))))) => .rc
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (()))))))))))) => .rh

def Name.sumEquiv : Name ≃ NameSum where
  toFun := Name.toSum
  invFun := Name.ofSum
  left_inv n := by cases n <;> rfl
  right_inv s := by
    rcases s with k | ⟨k,t⟩ | ⟨k,t⟩ | ⟨k,t⟩ | j | j | j | u | u | u | ⟨⟩ | ⟨⟩ <;> rfl

theorem sum_names {M : Type} [AddCommMonoid M] (f : Name → M) :
    ∑ n, f n =
      (∑ k, f (.src k)) + (∑ k, ∑ t, f (.ci k t)) +
      (∑ k, ∑ t, f (.ch k t)) + (∑ k, ∑ t, f (.cv k t)) +
      (∑ j, f (.sc j)) + (∑ j, f (.sh j)) + (∑ j, f (.sv j)) +
      (∑ u, f (.mc u)) + (∑ u, f (.mh u)) + (∑ u, f (.mv u)) +
      f .rc + f .rh := by
  rw [← Fintype.sum_equiv Name.sumEquiv.symm (fun s => f (Name.ofSum s)) f
    (fun _ => rfl)]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_unique,
    Name.ofSum, add_assoc]

theorem sum_fin18_ge (v : ℕ) :
    ∑ t : Fin 18, (if v ≤ t.val then 1 else 0) = 18 - v := by
  rw [Fin.sum_univ_eq_sum_range (fun t => if v ≤ t then 1 else 0) 18,
    ← Finset.card_filter]
  have h : (Finset.range 18).filter (fun t => v ≤ t) = Finset.Ico v 18 := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [h, Nat.card_Ico]

theorem sum_charge (c : Choice) : ∑ n, charge c n = c.reconstructionCost := by
  rw [sum_names]
  simp only [charge, Finset.sum_const_zero, zero_add, add_zero]
  have hchain :
      ∑ k : Fin 66, ∑ t : Fin 18,
          (if k ∈ active c.frontier ∧ (c.position k).val ≤ t.val then 1 else 0) =
        c.chainCost := by
    simp only [Choice.chainCost]
    have hinner : ∀ k : Fin 66,
        (∑ t : Fin 18,
          (if k ∈ active c.frontier ∧ (c.position k).val ≤ t.val then 1 else 0)) =
          if k ∈ active c.frontier then 18 - (c.position k).val else 0 := by
      intro k
      by_cases hk : k ∈ active c.frontier
      · simp only [hk, true_and, if_true]
        exact sum_fin18_ge _
      · simp [hk]
    simp only [hinner]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hchain]
  rw [Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_ite_mem, Finset.univ_inter]
  simp only [Finset.sum_const, smul_eq_mul]
  unfold Choice.reconstructionCost Frontier.fixedCost Frontier.expanded
  omega

theorem reconstructCost_as_sum (A : Finset Name) :
    graph.reconstructCost (fins A) =
      ∑ n : Name, if Evaluated A n then n.cost else 0 := by
  unfold Graph.reconstructCost
  rw [evaluated_eq_fins]
  refine (Finset.sum_map (evaluatedNames A) nameEmbedding
    graph.nodeCost).trans ?_
  rw [evaluatedNames, Finset.sum_filter]
  exact Finset.sum_congr rfl fun n _ => by
    rw [nameEmbedding_apply, graph_nodeCost_fin]

theorem reconstructCost_le (c : Choice) :
    graph.reconstructCost (fins (cutOf c)) ≤ c.reconstructionCost := by
  rw [reconstructCost_as_sum, ← sum_charge]
  exact Finset.sum_le_sum fun n _ => evaluated_cost_le_charge c n

theorem reconstructCost_cutOf {c : Choice} (hc : c ∈ shapes) :
    graph.reconstructCost (fins (cutOf c)) ≤ 90 := by
  exact (reconstructCost_le c).trans_eq
    (Choice.reconstructionCost_eq (valid_of_mem_shapes hc))

/- Family-level statements consumed by the eventual scheme. -/

theorem family_root_not_mem {A : Finset Name} (hA : A ∈ family) :
    graph.root ∉ fins A := by
  obtain ⟨c, _, rfl⟩ := (mem_family_iff A).1 hA
  exact root_not_mem_cutOf c

theorem family_no_hidden_source {A : Finset Name} (hA : A ∈ family) :
    ∀ v, graph.Visited (fins A) v → v ∉ fins A →
      ¬ (graph.kind v).IsSource := by
  obtain ⟨c, _, rfl⟩ := (mem_family_iff A).1 hA
  exact no_hidden_source_cutOf c

theorem family_reconstructCost {A : Finset Name} (hA : A ∈ family) :
    graph.reconstructCost (fins A) ≤ 90 := by
  obtain ⟨c, hc, rfl⟩ := (mem_family_iff A).1 hA
  exact (reconstructCost_le c).trans_eq
    (Choice.reconstructionCost_eq (valid_of_mem_supportedShapes hc))

theorem family_disclosure_and_nonce {A : Finset Name} (hA : A ∈ family) :
    graph.revealBits (fins A) + 86 ≤ 5504 := by
  obtain ⟨c, hc, rfl⟩ := (mem_family_iff A).1 hA
  have hv := valid_of_mem_supportedShapes hc
  rw [revealBits_fins]
  have hr : ∑ n ∈ cutOf c, n.len = (cutOf c).card * 129 := by
    calc
      ∑ n ∈ cutOf c, n.len = ∑ _n ∈ cutOf c, 129 :=
        Finset.sum_congr rfl fun n hn => cutOf_values c n hn
      _ = (cutOf c).card * 129 := by rw [Finset.sum_const, smul_eq_mul]
  rw [hr, card_cutOf c hv.1]
  have hw := Choice.words_le hv
  omega

#print axioms family_root_not_mem
#print axioms family_no_hidden_source
#print axioms family_reconstructCost
#print axioms family_disclosure_and_nonce

end OptimalOTS.WeightedConstruction.LongChain91
