import Submissions.UpperCompressions.LongChain91Geometry
import Submissions.UpperCompressions.ProofBundle03

/-!
# Concrete DAG for the cost-90 long-chain construction

This module turns the finite names from `LongChain91Geometry` into the actual
`Dag.Graph` consumed by the generic weighted scheme.  The graph has 66
length-18 chains, 18 lower ternary hashes, 10 upper ternary hashes, and a
ten-word root hash.
-/

open OracleSpec OracleComp ENNReal
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace OptimalOTS.WeightedConstruction.LongChain91

open OptimalOTS.Dag

abbrev N : ℕ := nodeCount

namespace Name

/-- Inverse of the compact topological numbering. -/
def ofFin (v : Fin N) : Name :=
  if h₀ : v.val < 66 then .src ⟨v.val, h₀⟩
  else if h₁ : v.val < 3630 then
    let m := v.val - 66
    let t : Fin 18 := ⟨m / 198, by omega⟩
    let r := m % 198
    if h₂ : r < 66 then .ci ⟨r, h₂⟩ t
    else if h₃ : r < 132 then .ch ⟨r - 66, by omega⟩ t
    else .cv ⟨r - 132, by omega⟩ t
  else if h₄ : v.val < 3648 then .sc ⟨v.val - 3630, by omega⟩
  else if h₅ : v.val < 3666 then .sh ⟨v.val - 3648, by omega⟩
  else if h₆ : v.val < 3684 then .sv ⟨v.val - 3666, by omega⟩
  else if h₇ : v.val < 3694 then .mc ⟨v.val - 3684, by omega⟩
  else if h₈ : v.val < 3704 then .mh ⟨v.val - 3694, by omega⟩
  else if h₉ : v.val < 3714 then .mv ⟨v.val - 3704, by omega⟩
  else if h₁₀ : v.val < 3715 then .rc
  else .rh

theorem fin_ofFin_aux (v : Fin N) : (ofFin v).fin = v := by
  have hv : v.val < 3716 := v.isLt
  rw [Fin.ext_iff]
  simp only [ofFin]
  split_ifs <;> simp only [fin, idx] <;> omega

@[simp] theorem ofFin_fin (n : Name) : ofFin n.fin = n :=
  idx_injective (congrArg Fin.val (fin_ofFin_aux n.fin))

@[simp] theorem fin_ofFin (v : Fin N) : (ofFin v).fin = v := fin_ofFin_aux v

def nameEquiv : Name ≃ Fin N where
  toFun := fin
  invFun := ofFin
  left_inv := ofFin_fin
  right_inv := fin_ofFin

/-- The three terminal chain values entering lower node `j`. -/
def lowerChain (j : Fin 18) (a : Fin 3) : Fin 66 := ⟨3 * j.val + a.val, by omega⟩

/-- The three 129-bit values entering upper node `u`. -/
def midChild (u : Fin 10) (a : Fin 3) : Name :=
  if hu : u.val < 8 then
    if ha₀ : a.val = 0 then .sv ⟨2 * u.val, by omega⟩
    else if ha₁ : a.val = 1 then .sv ⟨2 * u.val + 1, by omega⟩
    else .cv ⟨54 + u.val, by omega⟩ 17
  else
    if ha₀ : a.val = 0 then .sv ⟨u.val + 8, by omega⟩
    else .cv ⟨62 + 2 * (u.val - 8) + (a.val - 1), by omega⟩ 17

@[simp] theorem child_prev (k : Fin 66) (t : Fin 18) :
    child (prev k t) = some (.ci k t) := by
  revert k t
  decide +kernel

@[simp] theorem child_lowerChain (j : Fin 18) (a : Fin 3) :
    child (.cv (lowerChain j a) 17) = some (.sc j) := by
  revert j a
  decide +kernel

@[simp] theorem child_midChild (u : Fin 10) (a : Fin 3) :
    child (midChild u a) = some (.mc u) := by
  revert u a
  decide +kernel

/-- The nodes read by a graph node.  The two heterogeneous ternary layers use
the finite inverse image of `child`; all uniform edges are explicit. -/
def parents : Name → Finset Name
  | .src _ => ∅
  | .ci k t => {prev k t}
  | .ch k t => {.ci k t}
  | .cv k t => {.ch k t}
  | .sc j => Finset.univ.filter fun m => child m = some (.sc j)
  | .sh j => {.sc j}
  | .sv j => {.sh j}
  | .mc u => Finset.univ.filter fun m => child m = some (.mc u)
  | .mh u => {.mc u}
  | .mv u => {.mh u}
  | .rc => Finset.univ.image Name.mv
  | .rh => {.rc}

theorem child_of_mem_parents {m n : Name} (h : m ∈ parents n) : child m = some n := by
  cases n with
  | src k => simp [parents] at h
  | ci k t =>
      rw [parents, Finset.mem_singleton] at h
      subst m
      exact child_prev k t
  | ch k t =>
      rw [parents, Finset.mem_singleton] at h
      subst m
      rfl
  | cv k t =>
      rw [parents, Finset.mem_singleton] at h
      subst m
      rfl
  | sc j => exact (Finset.mem_filter.mp h).2
  | sh j =>
      rw [parents, Finset.mem_singleton] at h
      subst m
      rfl
  | sv j =>
      rw [parents, Finset.mem_singleton] at h
      subst m
      rfl
  | mc u => exact (Finset.mem_filter.mp h).2
  | mh u =>
      rw [parents, Finset.mem_singleton] at h
      subst m
      rfl
  | mv u =>
      rw [parents, Finset.mem_singleton] at h
      subst m
      rfl
  | rc =>
      rw [parents, Finset.mem_image] at h
      obtain ⟨u, _, rfl⟩ := h
      rfl
  | rh =>
      rw [parents, Finset.mem_singleton] at h
      subst m
      rfl

@[simp] theorem mem_parents_iff (m n : Name) : m ∈ parents n ↔ child m = some n := by
  constructor
  · exact child_of_mem_parents
  · intro h
    cases m with
    | src k =>
        simp only [child, Option.some.injEq] at h
        subst n
        simp [parents, prev]
    | ci k t =>
        simp only [child, Option.some.injEq] at h
        subst n
        simp [parents]
    | ch k t =>
        simp only [child, Option.some.injEq] at h
        subst n
        simp [parents]
    | cv k t =>
        by_cases ht : t.val = 17
        · rw [child, dif_pos ht] at h
          cases hl : lowerOfChain k with
          | none =>
              rw [hl] at h
              simp only [Option.some.injEq] at h
              subst n
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_univ _, by simp [child, ht, hl]⟩
          | some j =>
              rw [hl] at h
              simp only [Option.some.injEq] at h
              subst n
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_univ _, by simp [child, ht, hl]⟩
        · rw [child, dif_neg ht] at h
          simp only [Option.some.injEq] at h
          subst n
          rw [parents, Finset.mem_singleton]
          unfold prev
          have hpos : ¬ ((⟨t.val + 1, by omega⟩ : Fin 18).val = 0) := by simp
          rw [dif_neg hpos]
          congr 1
    | sc j =>
        simp only [child, Option.some.injEq] at h
        subst n
        simp [parents]
    | sh j =>
        simp only [child, Option.some.injEq] at h
        subst n
        simp [parents]
    | sv j =>
        simp only [child, Option.some.injEq] at h
        subst n
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    | mc u =>
        simp only [child, Option.some.injEq] at h
        subst n
        simp [parents]
    | mh u =>
        simp only [child, Option.some.injEq] at h
        subst n
        simp [parents]
    | mv u =>
        simp only [child, Option.some.injEq] at h
        subst n
        exact Finset.mem_image_of_mem Name.mv (Finset.mem_univ u)
    | rc =>
        simp only [child, Option.some.injEq] at h
        subst n
        simp [parents]
    | rh => simp only [child, reduceCtorEq] at h

/-- Parent indices used by `NodeKind`.  Uniform edges are kept definitionally
small; only the two heterogeneous ternary layers reuse the name-level inverse
image. -/
def parentFins : Name → Finset (Fin N)
  | Name.src _ => ∅
  | Name.ci k t => {(prev k t).fin}
  | Name.ch k t => {(Name.ci k t).fin}
  | Name.cv k t => {(Name.ch k t).fin}
  | Name.sc j => (parents (Name.sc j)).map nameEquiv.toEmbedding
  | Name.sh j => {(Name.sc j).fin}
  | Name.sv j => {(Name.sh j).fin}
  | Name.mc u => (parents (Name.mc u)).map nameEquiv.toEmbedding
  | Name.mh u => {(Name.mc u).fin}
  | Name.mv u => {(Name.mh u).fin}
  | Name.rc => (parents Name.rc).map nameEquiv.toEmbedding
  | Name.rh => {(Name.rc).fin}

theorem parentFins_eq_map_parents (n : Name) :
    parentFins n = (parents n).map nameEquiv.toEmbedding := by
  cases n <;> simp [parentFins, parents, nameEquiv]

theorem fin_lt_fin_of_mem_parents {m n : Name} (h : m ∈ parents n) : m.fin < n.fin := by
  exact idx_lt_of_child (child_of_mem_parents h)

@[simp] theorem midChild_len (u : Fin 10) (a : Fin 3) : (midChild u a).len = 129 := by
  unfold midChild
  split_ifs <;> rfl

end Name

open Name

/-! ## Tweaks and deterministic inputs -/

def tw (h : Name) : BitVec 16 := BitVec.ofNat 16 h.idx

theorem tw_toNat (h : Name) : (tw h).toNat = h.idx := by
  have hi := h.idx_lt
  unfold nodeCount at hi
  rw [tw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  omega

theorem tw_injective : Function.Injective tw := by
  intro h h' e
  apply Name.idx_injective
  rw [← tw_toNat h, ← tw_toNat h', e]

def lenF (v : Fin N) : ℕ := (Name.ofFin v).len

@[simp] theorem lenF_fin (n : Name) : lenF n.fin = n.len := by simp [lenF]

def cat3 (a b c : BitVec 129) : BitVec 387 := (a ++ b ++ c).cast (by norm_num)

def cat10 (a : Fin 10 → BitVec 129) : BitVec 1290 :=
  (a 0 ++ a 1 ++ a 2 ++ a 3 ++ a 4 ++ a 5 ++ a 6 ++ a 7 ++ a 8 ++ a 9).cast
    (by norm_num)

def lowWord {w : ℕ} (x : BitVec w) : BitVec 129 := x.setWidth 129
def lowPk {w : ℕ} (x : BitVec w) : BitVec 128 := x.setWidth 128

abbrev Asg := (v : Fin N) → BitVec (lenF v)

def detVal (n : Name) (x : Asg) : BitVec n.len :=
  match n with
  | Name.ci k t => tw (Name.ch k t) ++ lowWord (x (prev k t).fin)
  | Name.cv k t => lowWord (x (Name.ch k t).fin)
  | Name.sc j => tw (Name.sh j) ++ cat3
      (lowWord (x (Name.cv (Name.lowerChain j 0) 17).fin))
      (lowWord (x (Name.cv (Name.lowerChain j 1) 17).fin))
      (lowWord (x (Name.cv (Name.lowerChain j 2) 17).fin))
  | Name.sv j => lowWord (x (Name.sh j).fin)
  | Name.mc u => tw (Name.mh u) ++ cat3
      (lowWord (x (midChild u 0).fin))
      (lowWord (x (midChild u 1).fin))
      (lowWord (x (midChild u 2).fin))
  | Name.mv u => lowWord (x (Name.mh u).fin)
  | Name.rc => tw Name.rh ++ cat10 fun u => lowWord (x (Name.mv u).fin)
  | _ => 0

theorem eq_fin_of_ofFin_eq {v : Fin N} {n : Name} (h : Name.ofFin v = n) : v = n.fin := by
  rw [← h, Name.fin_ofFin]

theorem hash_parent_lt {v : Fin N} {n m : Name} (h : Name.ofFin v = n)
    (hm : m ∈ parents n) : m.fin < v := by
  rw [eq_fin_of_ofFin_eq h]
  exact Name.fin_lt_fin_of_mem_parents hm

theorem det_parents_lt {v : Fin N} {n : Name} (h : Name.ofFin v = n) :
    ∀ w ∈ Name.parentFins n, w < v := by
  rw [Name.parentFins_eq_map_parents]
  intro w hw
  rw [Finset.mem_map] at hw
  obtain ⟨m, hm, rfl⟩ := hw
  exact hash_parent_lt h hm

theorem detVal_local (n : Name) (x y : Asg)
    (hxy : ∀ w ∈ Name.parentFins n, x w = y w) :
    detVal n x = detVal n y := by
  cases n with
  | ci k t =>
      show tw (Name.ch k t) ++ lowWord (x (prev k t).fin) =
        tw (Name.ch k t) ++ lowWord (y (prev k t).fin)
      have hp : (prev k t).fin ∈ Name.parentFins (Name.ci k t) :=
        by simpa [Name.parentFins] using Finset.mem_singleton_self (prev k t).fin
      rw [hxy _ hp]
  | cv k t =>
      show lowWord (x (Name.ch k t).fin) = lowWord (y (Name.ch k t).fin)
      have hp : (Name.ch k t).fin ∈ Name.parentFins (Name.cv k t) :=
        by simpa [Name.parentFins] using Finset.mem_singleton_self (Name.ch k t).fin
      rw [hxy _ hp]
  | sc j =>
      show tw (Name.sh j) ++ cat3
          (lowWord (x (Name.cv (Name.lowerChain j 0) 17).fin))
          (lowWord (x (Name.cv (Name.lowerChain j 1) 17).fin))
          (lowWord (x (Name.cv (Name.lowerChain j 2) 17).fin)) =
        tw (Name.sh j) ++ cat3
          (lowWord (y (Name.cv (Name.lowerChain j 0) 17).fin))
          (lowWord (y (Name.cv (Name.lowerChain j 1) 17).fin))
          (lowWord (y (Name.cv (Name.lowerChain j 2) 17).fin))
      have hp (a : Fin 3) : (Name.cv (Name.lowerChain j a) 17).fin ∈
          Name.parentFins (Name.sc j) :=
        Finset.mem_map_of_mem _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Name.child_lowerChain j a⟩)
      rw [hxy _ (hp 0), hxy _ (hp 1), hxy _ (hp 2)]
  | sv j =>
      show lowWord (x (Name.sh j).fin) = lowWord (y (Name.sh j).fin)
      have hp : (Name.sh j).fin ∈ Name.parentFins (Name.sv j) :=
        by simpa [Name.parentFins] using Finset.mem_singleton_self (Name.sh j).fin
      rw [hxy _ hp]
  | mc u =>
      show tw (Name.mh u) ++ cat3
          (lowWord (x (midChild u 0).fin))
          (lowWord (x (midChild u 1).fin))
          (lowWord (x (midChild u 2).fin)) =
        tw (Name.mh u) ++ cat3
          (lowWord (y (midChild u 0).fin))
          (lowWord (y (midChild u 1).fin))
          (lowWord (y (midChild u 2).fin))
      have hp (a : Fin 3) : (midChild u a).fin ∈
          Name.parentFins (Name.mc u) :=
        Finset.mem_map_of_mem _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Name.child_midChild u a⟩)
      rw [hxy _ (hp 0), hxy _ (hp 1), hxy _ (hp 2)]
  | mv u =>
      show lowWord (x (Name.mh u).fin) = lowWord (y (Name.mh u).fin)
      have hp : (Name.mh u).fin ∈ Name.parentFins (Name.mv u) :=
        by simpa [Name.parentFins] using Finset.mem_singleton_self (Name.mh u).fin
      rw [hxy _ hp]
  | rc =>
      show tw Name.rh ++ cat10 (fun u => lowWord (x (Name.mv u).fin)) =
        tw Name.rh ++ cat10 (fun u => lowWord (y (Name.mv u).fin))
      have he : (fun u => lowWord (x (Name.mv u).fin)) =
          fun u => lowWord (y (Name.mv u).fin) := by
        funext u
        have hp : (Name.mv u).fin ∈ Name.parentFins Name.rc :=
          Finset.mem_map_of_mem _
            (Finset.mem_image_of_mem _ (Finset.mem_univ u))
        rw [hxy _ hp]
      rw [he]
  | src _ | ch _ _ | sh _ | mh _ | rh => rfl

/-! ## `Dag.Graph` instance -/

def kindOf (v : Fin N) : (n : Name) → Name.ofFin v = n → NodeKind N lenF v
  | Name.src _, _ => .source
  | Name.ci k t, h => .det (Name.parentFins (Name.ci k t))
      (det_parents_lt h)
      (fun x => (detVal (Name.ci k t) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | Name.ch k t, h => .hash (Name.ci k t).fin (hash_parent_lt h (Finset.mem_singleton_self _)) (by rw [lenF, h]; rfl)
  | Name.cv k t, h => .det (Name.parentFins (Name.cv k t))
      (det_parents_lt h)
      (fun x => (detVal (Name.cv k t) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | Name.sc j, h => .det (Name.parentFins (Name.sc j))
      (det_parents_lt h)
      (fun x => (detVal (Name.sc j) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | Name.sh j, h => .hash (Name.sc j).fin (hash_parent_lt h (Finset.mem_singleton_self _)) (by rw [lenF, h]; rfl)
  | Name.sv j, h => .det (Name.parentFins (Name.sv j))
      (det_parents_lt h)
      (fun x => (detVal (Name.sv j) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | Name.mc u, h => .det (Name.parentFins (Name.mc u))
      (det_parents_lt h)
      (fun x => (detVal (Name.mc u) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | Name.mh u, h => .hash (Name.mc u).fin (hash_parent_lt h (Finset.mem_singleton_self _)) (by rw [lenF, h]; rfl)
  | Name.mv u, h => .det (Name.parentFins (Name.mv u))
      (det_parents_lt h)
      (fun x => (detVal (Name.mv u) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | Name.rc, h => .det (Name.parentFins Name.rc)
      (det_parents_lt h)
      (fun x => (detVal Name.rc x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | Name.rh, h => .hash Name.rc.fin (hash_parent_lt h (Finset.mem_singleton_self _)) (by rw [lenF, h]; rfl)

theorem kindOf_isHash (v : Fin N) (n : Name) (h : Name.ofFin v = n) :
    (kindOf v n h).IsHash ↔ n.cost ≠ 0 := by
  cases n <;> simp [kindOf, NodeKind.IsHash, Name.cost]

theorem kindOf_isSource (v : Fin N) (n : Name) (h : Name.ofFin v = n) :
    (kindOf v n h).IsSource ↔ ∃ k, n = .src k := by
  cases n <;> simp [kindOf, NodeKind.IsSource]

theorem kindOf_parents (v : Fin N) (n : Name) (h : Name.ofFin v = n) :
    (kindOf v n h).parents = (parents n).map Name.nameEquiv.toEmbedding := by
  rw [← Name.parentFins_eq_map_parents]
  cases n <;> rfl

def graph : Graph where
  size := N
  len := lenF
  kind v := kindOf v (Name.ofFin v) rfl
  root := Name.rh.fin
  root_isHash := (kindOf_isHash _ _ rfl).2 (by rw [Name.ofFin_fin]; decide)

def publicKey (x : graph.Assignment) : PublicKey := lowPk (x graph.root)

theorem graph_kind_eq (v : Fin N) (n : Name) (h : Name.ofFin v = n) :
    graph.kind v = kindOf v n h := by subst h; rfl

theorem graph_kind_fin (n : Name) :
    graph.kind n.fin = kindOf n.fin n (Name.ofFin_fin n) := graph_kind_eq _ _ _

@[simp] theorem graph_len_fin (n : Name) : graph.len n.fin = n.len := lenF_fin n

theorem graph_parents_fin (n : Name) :
    (graph.kind n.fin).parents = (parents n).map Name.nameEquiv.toEmbedding := by
  rw [graph_kind_fin]
  exact kindOf_parents _ _ _

theorem graph_isHash_fin (n : Name) : (graph.kind n.fin).IsHash ↔ n.cost ≠ 0 := by
  rw [graph_kind_fin]
  exact kindOf_isHash _ _ _

theorem graph_isSource_fin (n : Name) :
    (graph.kind n.fin).IsSource ↔ ∃ k, n = .src k := by
  rw [graph_kind_fin]
  exact kindOf_isSource _ _ _

theorem graph_nodeCost_fin (n : Name) : graph.nodeCost n.fin = n.cost := by
  unfold Graph.nodeCost
  rw [graph_kind_fin]
  cases n <;> simp only [kindOf, graph_len_fin] <;>
    simp [Name.cost, Name.len, blockCost, blockBits]

theorem graph_keygenCost : graph.keygenCost = 1219 := by
  show ∑ v : Fin N, graph.nodeCost v = 1219
  rw [← Fintype.sum_equiv Name.nameEquiv
    (fun n => graph.nodeCost n.fin) (fun v => graph.nodeCost v) (fun _ => rfl)]
  simp only [graph_nodeCost_fin]
  exact sum_name_cost.trans keygenCost_eq

theorem hash_output_width (n : Name) (hn : n.cost ≠ 0) : n.len = 256 := by
  cases n <;> simp [Name.cost] at hn <;> rfl

theorem graph_hash_input_length_ne_index {p h : Name}
    (hp : child p = some h) (hh : h.cost ≠ 0) : p.len ≠ 342 := by
  cases p <;> simp only [Name.len] <;> omega

theorem input_costs :
    blockCost 145 = 1 ∧ blockCost 403 = 1 ∧ blockCost 1306 = 3 := by
  norm_num [blockCost, blockBits]

#print axioms graph_keygenCost
#print axioms hash_output_width
#print axioms input_costs

end OptimalOTS.WeightedConstruction.LongChain91
