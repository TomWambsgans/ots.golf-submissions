import Submissions.UpperCompressions.LongChain91AuthGame

/-!
# Cross-cut authentication for the cost-91 long-chain construction

Every supported disclosure cut has exact reconstruction cost 90.  Thus two
 distinct scheduled cuts of the same cost are incomparable: a value disclosed
 by the signed cut is evaluated by the forged cut.  Following the hash directly
 above that value gives either a hidden-key hit or a spurious binding.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace OptimalOTS.WeightedConstruction.LongChain91

open OptimalOTS.Dag
open Name

/-! ## Exact cost of a supported cut -/

theorem cutOf_not_mem_of_len_ne {c : Choice} {n : Name}
    (hn : n.len ≠ 129) : n ∉ cutOf c := by
  intro hmem
  exact hn (cutOf_values c n hmem)

theorem selected_eq_chainNode_of_active (c : Choice) {k : Fin 66}
    (hk : k ∈ active c.frontier) :
    selected c k = chainNode k (c.position k) := by
  have hparts := (mem_active c.frontier k).1 hk
  unfold selected
  rw [if_pos hparts.1]
  cases hl : lowerOfChain k with
  | none => simp only [hl]
  | some j =>
      have hj : j ∈ c.frontier.lower := by
        simpa only [hl] using hparts.2
      simp only [hl, if_pos hj]

theorem not_above_chainNode_ch_of_le (k : Fin 66) (p : Fin 19)
    (t : Fin 18) (hpt : p.val ≤ t.val) :
    ¬ Above (chainNode k p) (Name.ch k t) := by
  intro ha
  have hh := height_lt_of_above ha
  unfold chainNode at hh
  split_ifs at hh <;> simp only [height] at hh <;> omega

theorem not_above_chainNode_sh {k : Fin 66} {j : Fin 18}
    (hl : lowerOfChain k = some j) (p : Fin 19) :
    ¬ Above (chainNode k p) (Name.sh j) := by
  intro ha
  have hh := height_lt_of_above ha
  unfold chainNode at hh
  split_ifs at hh <;> simp [height, chainBase, hl] at hh <;> omega

theorem not_above_selected_mh_of_upper (c : Choice) {k : Fin 66}
    {u : Fin 10} (hku : upperOfChain k = u)
    (hu : u ∈ c.frontier.upper) :
    ¬ Above (selected c k) (Name.mh u) := by
  intro ha
  have hh := height_lt_of_above ha
  have huk : upperOfChain k ∈ c.frontier.upper := by
    rw [hku]
    exact hu
  unfold selected at hh
  rw [if_pos huk] at hh
  cases hl : lowerOfChain k with
  | none =>
      simp only [hl] at hh
      unfold chainNode at hh
      split_ifs at hh <;> simp [height, chainBase, hl] at hh <;> omega
  | some j =>
      simp only [hl] at hh
      by_cases hj : j ∈ c.frontier.lower
      · rw [if_pos hj] at hh
        unfold chainNode at hh
        split_ifs at hh <;> simp [height, chainBase, hl] at hh <;> omega
      · rw [if_neg hj] at hh
        simp [height] at hh

theorem evaluated_ch_of_active_le (c : Choice) (hc : c.Valid)
    (k : Fin 66) (t : Fin 18) (hk : k ∈ active c.frontier)
    (hpt : (c.position k).val ≤ t.val) :
    Evaluated (cutOf c) (Name.ch k t) := by
  apply (clearEvaluated_iff (cutOf c) (Name.ch k t)).1
  refine ⟨cutOf_not_mem_of_len_ne (by simp [Name.len]), ?_⟩
  intro m hm hmA
  have hmlen : m.len = 129 := cutOf_values c m hmA
  have hmb : Branch k m :=
    branch_above (show Branch k (Name.ch k t) by rfl) hm
  have hmp : OnPath k m := (onPath_iff_branch_of_len hmlen).2 hmb
  have hmeq : m = selected c k :=
    eq_selected_of_mem_onPath c hc.1 hmA hmp
  rw [hmeq, selected_eq_chainNode_of_active c hk] at hm
  exact not_above_chainNode_ch_of_le k (c.position k) t hpt hm

theorem evaluated_sh_of_lower (c : Choice) (hc : c.Valid)
    (j : Fin 18) (hj : j ∈ c.frontier.lower) :
    Evaluated (cutOf c) (Name.sh j) := by
  let k : Fin 66 := Name.lowerChain j 0
  have hl : lowerOfChain k = some j := by
    have hjlt := j.isLt
    dsimp [k, Name.lowerChain]
    simp [lowerOfChain] <;> omega
  have hu : upperOfChain k ∈ c.frontier.upper := by
    rw [upperOfChain_eq_upperOfLower hl]
    exact (mem_availableLower c.frontier.upper j).1 (hc.1 hj)
  have hk : k ∈ active c.frontier := by
    rw [mem_active]
    exact ⟨hu, by simp [hl, hj]⟩
  have hsel := selected_eq_chainNode_of_active c hk
  apply (clearEvaluated_iff (cutOf c) (Name.sh j)).1
  refine ⟨cutOf_not_mem_of_len_ne (by simp [Name.len]), ?_⟩
  intro m hm hmA
  have hmlen : m.len = 129 := cutOf_values c m hmA
  have hmb : Branch k m :=
    branch_above (show Branch k (Name.sh j) by simpa [Branch] using hl) hm
  have hmp : OnPath k m := (onPath_iff_branch_of_len hmlen).2 hmb
  have hmeq : m = selected c k :=
    eq_selected_of_mem_onPath c hc.1 hmA hmp
  rw [hmeq, hsel] at hm
  exact not_above_chainNode_sh hl (c.position k) hm

theorem evaluated_mh_of_upper (c : Choice) (hc : c.Valid)
    (u : Fin 10) (hu : u ∈ c.frontier.upper) :
    Evaluated (cutOf c) (Name.mh u) := by
  obtain ⟨k, hku⟩ := upperOfChain_surjective u
  apply (clearEvaluated_iff (cutOf c) (Name.mh u)).1
  refine ⟨cutOf_not_mem_of_len_ne (by simp [Name.len]), ?_⟩
  intro m hm hmA
  have hmlen : m.len = 129 := cutOf_values c m hmA
  have hmb : Branch k m :=
    branch_above (show Branch k (Name.mh u) by simpa [Branch] using hku) hm
  have hmp : OnPath k m := (onPath_iff_branch_of_len hmlen).2 hmb
  have hmeq : m = selected c k :=
    eq_selected_of_mem_onPath c hc.1 hmA hmp
  rw [hmeq] at hm
  exact not_above_selected_mh_of_upper c hku hu hm

theorem evaluated_rh_cutOf (c : Choice) :
    Evaluated (cutOf c) Name.rh := by
  apply (clearEvaluated_iff (cutOf c) Name.rh).1
  refine ⟨cutOf_not_mem_of_len_ne (by simp [Name.len]), ?_⟩
  intro m hm
  exact absurd hm (not_above_rh m)

theorem evaluated_cost_eq_charge (c : Choice) (hc : c.Valid) (n : Name) :
    (if Evaluated (cutOf c) n then n.cost else 0) = charge c n := by
  cases n with
  | ch k t =>
      have hi : Evaluated (cutOf c) (Name.ch k t) ↔
          k ∈ active c.frontier ∧ (c.position k).val ≤ t.val :=
        ⟨evaluated_ch_implies c k t,
          fun h => evaluated_ch_of_active_le c hc k t h.1 h.2⟩
      simp only [charge, Name.cost, hi]
  | sh j =>
      have hi : Evaluated (cutOf c) (Name.sh j) ↔
          j ∈ c.frontier.lower :=
        ⟨evaluated_sh_implies_lower c j,
          evaluated_sh_of_lower c hc j⟩
      simp only [charge, Name.cost, hi]
  | mh u =>
      have hi : Evaluated (cutOf c) (Name.mh u) ↔
          u ∈ c.frontier.upper :=
        ⟨evaluated_mh_implies_upper c u,
          evaluated_mh_of_upper c hc u⟩
      simp only [charge, Name.cost, hi]
  | rh => simp [charge, Name.cost, evaluated_rh_cutOf c]
  | src k | ci k t | cv k t | sc k | sv k | mc k | mv k | rc =>
      simp [charge, Name.cost]

theorem reconstructCost_cutOf_eq (c : Choice) (hc : c.Valid) :
    graph.reconstructCost (fins (cutOf c)) = c.reconstructionCost := by
  rw [reconstructCost_as_sum, ← sum_charge]
  exact Finset.sum_congr rfl fun n _ => evaluated_cost_eq_charge c hc n

theorem family_reconstructCost_eq {A : Finset Name} (hA : A ∈ family) :
    graph.reconstructCost (fins A) = 90 := by
  obtain ⟨c, hc, rfl⟩ := (mem_family_iff A).1 hA
  exact (reconstructCost_cutOf_eq c (valid_of_mem_supportedShapes hc)).trans
    (Choice.reconstructionCost_eq (valid_of_mem_supportedShapes hc))

theorem evaluatedNames_cost_eq_reconstructCost (A : Finset Name) :
    (∑ n ∈ evaluatedNames A, n.cost) = graph.reconstructCost (fins A) := by
  rw [reconstructCost_as_sum, evaluatedNames, Finset.sum_filter]

theorem family_evaluatedNames_cost_eq {A : Finset Name} (hA : A ∈ family) :
    (∑ n ∈ evaluatedNames A, n.cost) = 90 :=
  (evaluatedNames_cost_eq_reconstructCost A).trans (family_reconstructCost_eq hA)

/-! ## Equal-cost cut incomparability -/

theorem cut_covers_source {A : Finset Name} (hA : IsCut A) (k : Fin 66) :
    Name.src k ∈ A ∨ ∃ m ∈ A, Above m (Name.src k) := by
  obtain ⟨n, hnA, hnp⟩ := hA.exists_on_path k
  rcases onPath_eq_source_or_above hnp with rfl | hn
  · exact Or.inl hnA
  · exact Or.inr ⟨n, hnA, hn⟩

theorem hashOf_isSome_iff (a : Name) :
    (hashOf a).isSome ↔ a.len = 129 ∧ ∀ k, a ≠ Name.src k := by
  cases a <;> simp [hashOf, Name.len]

theorem len_of_hashOf {a h : Name} (hh : hashOf a = some h) :
    h.len = 256 := by
  cases a <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;>
    subst h <;> rfl

theorem one_le_cost_of_hashOf {a h : Name} (hh : hashOf a = some h) :
    1 ≤ h.cost := by
  cases a <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;>
    subst h <;> simp [Name.cost]

theorem cost_of_hashOf {a h : Name} (hh : hashOf a = some h) :
    a.cost = 0 := by
  cases a <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;>
    subst h <;> rfl

theorem ne_rh_of_hashOf {a h : Name} (hh : hashOf a = some h) :
    h ≠ Name.rh := by
  cases a <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;>
    subst h <;> intro he <;> contradiction

theorem hashParent_of_hashOf {a h : Name} (hh : hashOf a = some h) :
    ∃ p, hashParent h = some p := by
  cases a <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;>
    subst h <;> simp [hashParent]

theorem val_of_hashOf (xi : Rec) {a h : Name} (hh : hashOf a = some h) :
    lowWord (val xi a) = lowWord (xi.2 h.fin) := by
  cases a <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;> subst h
  · rw [val_cv]
    exact lowWord_lowWord _
  · rw [val_sv]
    exact lowWord_lowWord _
  · rw [val_mv]
    exact lowWord_lowWord _

theorem yv_of_hashOf {A : Finset Name} {d : Cache}
    {given y : graph.Assignment}
    (hy : graph.ReconEqs d (fins A) given y) {a h : Name}
    (hh : hashOf a = some h) (he : Evaluated A a) :
    lowWord (yv y a) = lowWord (yv y h) := by
  cases a <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;> subst h
  · rw [yv_cv hy he]
    exact lowWord_lowWord _
  · rw [yv_sv hy he]
    exact lowWord_lowWord _
  · rw [yv_mv hy he]
    exact lowWord_lowWord _

attribute [local irreducible] evaluatedNames

theorem exists_mem_evaluated_of_ne {A A' : Finset Name}
    (hA : IsCut A) (hA' : IsCut A')
    (hcost : (∑ n ∈ evaluatedNames A, n.cost) =
      ∑ n ∈ evaluatedNames A', n.cost)
    (hne : A ≠ A') : ∃ v ∈ A, Evaluated A' v := by
  by_contra hcon
  push Not at hcon
  have key : ∀ v ∈ A, v ∈ A' ∨ ∃ m ∈ A', Above m v := by
    intro v hv
    by_contra h
    push Not at h
    apply hcon v hv
    apply (clearEvaluated_iff A' v).1
    exact ⟨h.1, fun m hm hmA' => h.2 m hmA' hm⟩
  have hsub : evaluatedNames A' ⊆ evaluatedNames A := by
    intro n hn
    simp only [evaluatedNames, Finset.mem_filter, Finset.mem_univ,
      true_and] at hn ⊢
    have hnC := (clearEvaluated_iff A' n).2 hn
    apply (clearEvaluated_iff A n).1
    refine ⟨fun hnA => ?_, fun m hm hmA => ?_⟩
    · rcases key n hnA with h | ⟨m, hmA', hm⟩
      · exact hnC.1 h
      · exact hnC.2 m hm hmA'
    · rcases key m hmA with h | ⟨m', hm'A', hm'⟩
      · exact hnC.2 m hm h
      · exact hnC.2 m' (hm'.trans hm) hm'A'
  have hex : ∃ a ∈ A', Evaluated A a := by
    by_cases hAA' : A ⊆ A'
    · have hx : ∃ v' ∈ A', v' ∉ A := by
        by_contra h
        push Not at h
        exact hne (Finset.Subset.antisymm hAA' h)
      obtain ⟨v', hv'A', hv'A⟩ := hx
      refine ⟨v', hv'A', (clearEvaluated_iff A v').1 ⟨hv'A, ?_⟩⟩
      intro m hm hmA
      exact (cut_mem_clearAbove hA' hv'A' m hm) (hAA' hmA)
    · rw [Finset.not_subset] at hAA'
      obtain ⟨v, hvA, hvA'⟩ := hAA'
      rcases key v hvA with h | ⟨a', ha'A', ha'⟩
      · exact absurd h hvA'
      · refine ⟨a', ha'A', (clearEvaluated_iff A a').1 ⟨?_, ?_⟩⟩
        · exact cut_mem_clearAbove hA hvA a' ha'
        · intro m hm hmA
          exact (cut_mem_clearAbove hA hvA m (hm.trans ha')) hmA
  obtain ⟨a, haA', haE⟩ := hex
  have haC := (clearEvaluated_iff A a).2 haE
  have hns : ∀ k, a ≠ Name.src k := by
    intro k hk
    subst a
    rcases cut_covers_source hA k with h | ⟨m, hmA, hm⟩
    · exact haC.1 h
    · exact haC.2 m hm hmA
  have hsome : (hashOf a).isSome :=
    (hashOf_isSome_iff a).2 ⟨hA'.values a haA', hns⟩
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
  have hchild : child p = some a := child_hashOf hp
  have hpA : p ∉ A := fun h => by
    have hv := hA.values p h
    rw [len_of_hashOf hp] at hv
    omega
  have hpE : Evaluated A p := by
    apply (clearEvaluated_iff A p).1
    refine ⟨hpA, fun m hm => ?_⟩
    rw [above_of_child hchild] at hm
    rcases hm with rfl | hm
    · exact haC.1
    · exact haC.2 m hm
  have hpE' : ¬ Evaluated A' p := by
    intro he
    have heC := (clearEvaluated_iff A' p).2 he
    exact heC.2 a (Above.child hchild) haA'
  have hpcost : 1 ≤ p.cost := one_le_cost_of_hashOf hp
  have hpmem : p ∈ evaluatedNames A := by
    simp [evaluatedNames, hpE]
  have hpnmem : p ∉ evaluatedNames A' := by
    simp [evaluatedNames, hpE']
  have hsub' : evaluatedNames A' ⊆ (evaluatedNames A).erase p :=
    Finset.subset_erase.mpr ⟨hsub, hpnmem⟩
  have h1 := Finset.sum_le_sum_of_subset
    (f := fun n : Name => n.cost) hsub'
  have h2 := Finset.sum_erase_add (evaluatedNames A)
    (fun n : Name => n.cost) hpmem
  omega

/-! ## The cross-cut event -/

theorem events_ne {A A' : Finset Name} (hA : IsCut A) (hA' : IsCut A')
    (hcost : (∑ n ∈ evaluatedNames A, n.cost) =
      ∑ n ∈ evaluatedNames A', n.cost)
    (hne : A ≠ A') {xi : Rec} {d : Cache}
    {given y : graph.Assignment}
    (hy : graph.ReconEqs d (fins A') given y)
    (hacc : lowPk (yv y Name.rh) = pkOf xi) :
    Spr d xi ∨ Cache.Hits d (fHid (some A) xi) := by
  obtain ⟨v, hvA, hvE⟩ :=
    exists_mem_evaluated_of_ne hA hA' hcost hne
  have hvC := (clearEvaluated_iff A' v).2 hvE
  have hlen : v.len = 129 := hA.values v hvA
  have hns : ∀ k, v ≠ Name.src k := by
    intro k hk
    subst v
    rcases cut_covers_source hA' k with h | ⟨m, hmA', hm⟩
    · exact hvC.1 h
    · exact hvC.2 m hm hmA'
  obtain ⟨h, hh⟩ := Option.isSome_iff_exists.mp
    ((hashOf_isSome_iff v).2 ⟨hlen, hns⟩)
  have hch : child h = some v := child_hashOf hh
  have hhA' : h ∉ A' := fun hm => by
    have hv := hA'.values h hm
    rw [len_of_hashOf hh] at hv
    omega
  have hhE : Evaluated A' h := by
    apply (clearEvaluated_iff A' h).1
    refine ⟨hhA', fun m hm => ?_⟩
    rw [above_of_child hch] at hm
    rcases hm with rfl | hm
    · exact hvC.1
    · exact hvC.2 m hm
  obtain ⟨p, hhp⟩ := hashParent_of_hashOf hh
  have hpA' : p ∉ A' := fun hm => by
    have hv := hA'.values p hm
    rcases len_hashParent_cases hhp with hl | hl | hl <;> omega
  have hpE : Evaluated A' p :=
    evaluated_of_child_res (child_hashParent hhp) hpA' hhE
  by_cases hvne : yv y v = val xi v
  · obtain ⟨w, hd, hw⟩ := yv_hash hy hhp hhE
    have htr : lowWord w = lowWord (xi.2 h.fin) := by
      rw [hw, ← yv_of_hashOf hy hh hvE, hvne, val_of_hashOf xi hh]
    by_cases hpne : yv y p = val xi p
    · right
      refine ⟨⟨p.len, yv y p⟩, ?_, by rw [hd]; rfl⟩
      rw [fHid_isSome_some_iff]
      refine ⟨h, p, hhp, ?_, by rw [hpne]; rfl⟩
      intro he
      exact (visited_no_above A he.1 v (Above.child hch)) hvA
    · left
      refine ⟨h, p, hhp, yv y p, hpne, tagNat_yv hy hhp hpE,
        w, hd, ?_⟩
      unfold bindingValue
      rw [show bindingWidth h = 129 from if_neg (ne_rh_of_hashOf hh)]
      exact htr
  · left
    exact up hy hacc hvC (cost_of_hashOf hh) hvne

theorem crossCutAuthentication : CrossCutAuthentication := by
  intro xi signedClass i d given y hic hy hacc
  have hA := isCut_of_mem_family (setsName_mem signedClass)
  have hA' := isCut_of_mem_family (setsName_mem i)
  have hcost : (∑ n ∈ evaluatedNames (setsName signedClass), n.cost) =
      ∑ n ∈ evaluatedNames (setsName i), n.cost := by
    rw [family_evaluatedNames_cost_eq (setsName_mem signedClass),
      family_evaluatedNames_cost_eq (setsName_mem i)]
  apply events_ne hA hA' hcost
    (fun he => hic (setsName_injective he.symm)) hy hacc

theorem accepted_class_cases_actual
    (xi : Rec) (signedClass : Fin M) (m : Message)
    (sigma : WeightedScheme.Signature) (c d : Cache)
    (h : (true, d) ∈ support (run (scheme.verify (pkOf xi) m sigma) c)) :
    ∃ answer, d (encQuery (m, sigma.1)) = some answer ∧
      ∃ i : Fin M, LongChain91Schedule.decode answer = some i ∧
        ((i = signedClass ∧
            sigma.2 = graph.encode (fins (setsName signedClass))
              (graph.evalRec xi)) ∨
          Spr d xi ∨
          Cache.Hits d (fHid (some (setsName signedClass)) xi)) :=
  accepted_class_cases crossCutAuthentication xi signedClass m sigma c d h

theorem accepted_strong_event_actual
    (xi : Rec) (signedClass : Fin M) (signedInput : EncInput)
    (m : Message) (sigma : WeightedScheme.Signature) (c d : Cache)
    (h : (true, d) ∈ support (run (scheme.verify (pkOf xi) m sigma) c))
    (hne : (m, sigma) ≠ (signedInput.1,
      (signedInput.2,
        graph.encode (fins (setsName signedClass)) (graph.evalRec xi)))) :
    Spr d xi ∨ Cache.Hits d (fHid (some (setsName signedClass)) xi) ∨
      AlternateClass d signedInput signedClass :=
  accepted_strong_event crossCutAuthentication xi signedClass signedInput
    m sigma c d h hne

#print axioms reconstructCost_cutOf_eq
#print axioms family_reconstructCost_eq
#print axioms exists_mem_evaluated_of_ne
#print axioms crossCutAuthentication
#print axioms accepted_strong_event_actual

end OptimalOTS.WeightedConstruction.LongChain91
