import Submissions.UpperCompressions.ProofBundle00

/-!
# Cost-90 row-4719 geometry

This module isolates the new combinatorial geometry from the probability and
game proofs.  The graph has 66 length-18 chains, eighteen lower ternary nodes,
ten upper ternary nodes, and a ten-input root.  A frontier is described by the
expanded upper and lower nodes and by one position on each active chain.

The schedule deliberately does not depend on a research-script frontier
ranking.  Once the finite cut family has the certified cardinality, its
`Finset.equivFin` supplies an arbitrary stable class numbering.
-/

open scoped BigOperators Classical

noncomputable section

namespace OptimalOTS.WeightedConstruction.LongChain91

open OptimalOTS.ShallowResearch

/-! ## Graph names and static costs -/

/-- Names for the two-level row-4719 tree. -/
inductive Name where
  | src (k : Fin 66)
  | ci (k : Fin 66) (t : Fin 18)
  | ch (k : Fin 66) (t : Fin 18)
  | cv (k : Fin 66) (t : Fin 18)
  | sc (j : Fin 18)
  | sh (j : Fin 18)
  | sv (j : Fin 18)
  | mc (j : Fin 10)
  | mh (j : Fin 10)
  | mv (j : Fin 10)
  | rc
  | rh
  deriving DecidableEq, Fintype

/-- Number of graph nodes. -/
def nodeCount : ℕ := 3716

namespace Name

/-- A compact topological numbering. -/
def idx : Name → ℕ
  | src k => k
  | ci k t => 66 + 198 * t + k
  | ch k t => 132 + 198 * t + k
  | cv k t => 198 + 198 * t + k
  | sc j => 3630 + j
  | sh j => 3648 + j
  | sv j => 3666 + j
  | mc j => 3684 + j
  | mh j => 3694 + j
  | mv j => 3704 + j
  | rc => 3714
  | rh => 3715

theorem idx_lt (n : Name) : n.idx < nodeCount := by
  cases n <;> simp only [idx, nodeCount] <;> omega

theorem idx_injective : Function.Injective idx := by
  intro m n h
  cases m <;> cases n <;> simp_all [idx, Fin.ext_iff] <;> omega

def fin (n : Name) : Fin nodeCount := ⟨n.idx, n.idx_lt⟩

theorem fin_injective : Function.Injective fin := by
  intro m n h
  apply idx_injective
  exact congrArg Fin.val h

/-- Bit length of the value stored at a node. -/
def len : Name → ℕ
  | src _ => 129
  | ci _ _ => 145
  | ch _ _ => 256
  | cv _ _ => 129
  | sc _ => 403
  | sh _ => 256
  | sv _ => 129
  | mc _ => 403
  | mh _ => 256
  | mv _ => 129
  | rc => 1306
  | rh => 256

/-- SHA-256 compression cost at each hash-output node. -/
def cost : Name → ℕ
  | ch _ _ => 1
  | sh _ => 1
  | mh _ => 1
  | rh => 3
  | _ => 0

end Name

/-- The lower ternary node containing one of the first 54 chains. -/
def lowerOfChain (k : Fin 66) : Option (Fin 18) :=
  if h : k.val < 54 then some ⟨k.val / 3, by omega⟩ else none

/-- Parent upper node of a lower ternary node. -/
def upperOfLower (j : Fin 18) : Fin 10 :=
  if h : j.val < 16 then ⟨j.val / 2, by omega⟩ else ⟨j.val - 8, by omega⟩

/-- Parent upper node of a chain.  Chains 54--61 are the direct leaf of an A
node; 62--65 are the two direct leaves of the B nodes. -/
def upperOfChain (k : Fin 66) : Fin 10 :=
  if h₀ : k.val < 54 then upperOfLower ⟨k.val / 3, by omega⟩
  else if h₁ : k.val < 62 then ⟨k.val - 54, by omega⟩
  else if h₂ : k.val < 64 then 8
  else 9

/-- Every node except the root feeds exactly one node. -/
def Name.child : Name → Option Name
  | .src k => some (.ci k 0)
  | .ci k t => some (.ch k t)
  | .ch k t => some (.cv k t)
  | .cv k t =>
      if ht : t.val = 17 then
        match lowerOfChain k with
        | some j => some (.sc j)
        | none => some (.mc (upperOfChain k))
      else some (.ci k ⟨t.val + 1, by omega⟩)
  | .sc j => some (.sh j)
  | .sh j => some (.sv j)
  | .sv j => some (.mc (upperOfLower j))
  | .mc j => some (.mh j)
  | .mh j => some (.mv j)
  | .mv _ => some .rc
  | .rc => some .rh
  | .rh => none

theorem Name.idx_lt_of_child {m n : Name} (h : m.child = some n) : m.idx < n.idx := by
  cases m <;> simp only [Name.child, Option.some.injEq, reduceCtorEq] at h <;>
    (try split_ifs at h) <;>
    (try split at h) <;>
    (try simp only [Option.some.injEq] at h) <;>
    subst h <;> simp only [Name.idx, lowerOfChain, upperOfLower, upperOfChain] <;>
    (try split_ifs) <;> omega

/-- The value node feeding chain stage `t`. -/
def prev (k : Fin 66) (t : Fin 18) : Name :=
  if h : t.val = 0 then .src k else .cv k ⟨t.val - 1, by omega⟩

/-- Position zero discloses a source; positive position `p` discloses the
output of chain hash `p-1`. -/
def chainNode (k : Fin 66) (p : Fin 19) : Name :=
  if h : p.val = 0 then .src k else .cv k ⟨p.val - 1, by omega⟩

@[simp] theorem chainNode_len (k : Fin 66) (p : Fin 19) : (chainNode k p).len = 129 := by
  unfold chainNode
  split_ifs <;> rfl

/-- All internal hash inputs are length-separated from the 342-bit
message/nonce index input. -/
theorem hash_input_length_ne_index (n : Name)
    (h : n.len = 145 ∨ n.len = 403 ∨ n.len = 1306) : n.len ≠ 342 := by
  omega

/-- Static key-generation cost.  This is the arithmetic target for the later
`Dag.Graph.keygenCost` bridge. -/
def keygenCost : ℕ := 66 * 18 + 18 + 10 + 3

theorem keygenCost_eq : keygenCost = 1219 := by norm_num [keygenCost]

theorem keygenCost_le : keygenCost ≤ 2 ^ 20 := by norm_num [keygenCost]

theorem card_name : Fintype.card Name = nodeCount := by decide +kernel

theorem sum_name_cost : (∑ n : Name, n.cost) = keygenCost := by decide +kernel

/-! ## Structural frontiers -/

/-- A structural frontier records exactly the internal nodes which are
expanded.  `lower` must be a subset of the lower children made available by
the expanded upper nodes. -/
structure Frontier where
  upper : Finset (Fin 10)
  lower : Finset (Fin 18)
  deriving DecidableEq, Fintype

@[ext] theorem Frontier.ext {f g : Frontier} (hu : f.upper = g.upper)
    (hl : f.lower = g.lower) : f = g := by
  cases f
  cases g
  simp only [Frontier.mk.injEq] at hu hl ⊢
  exact ⟨hu, hl⟩

/-- Lower nodes exposed by the chosen expanded upper nodes. -/
def availableLower (U : Finset (Fin 10)) : Finset (Fin 18) :=
  Finset.univ.filter fun j => upperOfLower j ∈ U

@[simp] theorem mem_availableLower (U : Finset (Fin 10)) (j : Fin 18) :
    j ∈ availableLower U ↔ upperOfLower j ∈ U := by
  simp [availableLower]

/-- Active chains below a structural frontier. -/
def active (f : Frontier) : Finset (Fin 66) :=
  Finset.univ.filter fun k =>
    upperOfChain k ∈ f.upper ∧
      match lowerOfChain k with
      | none => True
      | some j => j ∈ f.lower

@[simp] theorem mem_active (f : Frontier) (k : Fin 66) :
    k ∈ active f ↔ upperOfChain k ∈ f.upper ∧
      match lowerOfChain k with
      | none => True
      | some j => j ∈ f.lower := by
  simp [active]

theorem upperOfChain_eq_upperOfLower {k : Fin 66} {j : Fin 18}
    (h : lowerOfChain k = some j) : upperOfChain k = upperOfLower j := by
  unfold lowerOfChain at h
  split_ifs at h with hk
  · simp only [Option.some.injEq] at h
    subst j
    simp [upperOfChain, hk]

/-! The ten upper nodes split as eight `A` nodes, each with two lower
children and one direct chain, and two `B` nodes, each with one lower child
and two direct chains.  These explicit embeddings let us count a supported
family without enumerating all `2^28` structural frontiers. -/

def aNode (i : Fin 8) : Fin 10 := ⟨i, by omega⟩

def bNode (i : Fin 2) : Fin 10 := ⟨8 + i, by omega⟩

def upperFrom (A : Finset (Fin 8)) (B : Finset (Fin 2)) : Finset (Fin 10) :=
  A.image aNode ∪ B.image bNode

theorem aNode_injective : Function.Injective aNode := by
  intro i j h
  apply Fin.ext
  change (aNode i).val = (aNode j).val
  exact congrArg Fin.val h

theorem bNode_injective : Function.Injective bNode := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [bNode] at hv
  omega

theorem upperFrom_disjoint (A : Finset (Fin 8)) (B : Finset (Fin 2)) :
    Disjoint (A.image aNode) (B.image bNode) := by
  apply Finset.disjoint_left.mpr
  intro u huA huB
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp huA
  obtain ⟨j, hj, h⟩ := Finset.mem_image.mp huB
  have hv := congrArg Fin.val h
  simp [aNode, bNode] at hv
  omega

theorem card_upperFrom (A : Finset (Fin 8)) (B : Finset (Fin 2)) :
    (upperFrom A B).card = A.card + B.card := by
  rw [upperFrom, Finset.card_union_of_disjoint (upperFrom_disjoint A B),
    Finset.card_image_of_injective _ aNode_injective,
    Finset.card_image_of_injective _ bNode_injective]

@[simp] theorem aNode_mem_upperFrom (A : Finset (Fin 8)) (B : Finset (Fin 2))
    (i : Fin 8) : aNode i ∈ upperFrom A B ↔ i ∈ A := by
  simp only [upperFrom, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨j, hj, h⟩ | ⟨j, hj, h⟩)
    · exact aNode_injective h ▸ hj
    · have hv := congrArg Fin.val h
      simp [aNode, bNode] at hv
      omega
  · intro hi
    exact Or.inl ⟨i, hi, rfl⟩

@[simp] theorem bNode_mem_upperFrom (A : Finset (Fin 8)) (B : Finset (Fin 2))
    (i : Fin 2) : bNode i ∈ upperFrom A B ↔ i ∈ B := by
  simp only [upperFrom, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨j, hj, h⟩ | ⟨j, hj, h⟩)
    · have hv := congrArg Fin.val h
      simp [aNode, bNode] at hv
      omega
    · exact bNode_injective h ▸ hj
  · intro hi
    exact Or.inr ⟨i, hi, rfl⟩

def lowerA (x : Fin 8 × Fin 2) : Fin 18 := ⟨2 * x.1 + x.2, by omega⟩

def lowerB (i : Fin 2) : Fin 18 := ⟨16 + i, by omega⟩

def lowerAvail (A : Finset (Fin 8)) (B : Finset (Fin 2)) : Finset (Fin 18) :=
  (A ×ˢ (Finset.univ : Finset (Fin 2))).image lowerA ∪ B.image lowerB

theorem lowerA_injective : Function.Injective lowerA := by
  rintro ⟨i, r⟩ ⟨j, s⟩ h
  have hv := congrArg Fin.val h
  simp only [lowerA] at hv
  have hi : i = j := Fin.ext (by omega)
  have hr : r = s := Fin.ext (by omega)
  exact Prod.ext hi hr

theorem lowerB_injective : Function.Injective lowerB := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [lowerB] at hv
  omega

theorem lowerAvail_disjoint (A : Finset (Fin 8)) (B : Finset (Fin 2)) :
    Disjoint ((A ×ˢ (Finset.univ : Finset (Fin 2))).image lowerA)
      (B.image lowerB) := by
  apply Finset.disjoint_left.mpr
  intro j hjA hjB
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hjA
  obtain ⟨i, hi, h⟩ := Finset.mem_image.mp hjB
  have hv := congrArg Fin.val h
  simp [lowerA, lowerB] at hv
  omega

theorem card_lowerAvail (A : Finset (Fin 8)) (B : Finset (Fin 2)) :
    (lowerAvail A B).card = 2 * A.card + B.card := by
  rw [lowerAvail, Finset.card_union_of_disjoint (lowerAvail_disjoint A B),
    Finset.card_image_of_injective _ lowerA_injective,
    Finset.card_image_of_injective _ lowerB_injective,
    Finset.card_product, Finset.card_univ, Fintype.card_fin]
  omega

theorem lowerAvail_subset_availableLower (A : Finset (Fin 8))
    (B : Finset (Fin 2)) : lowerAvail A B ⊆ availableLower (upperFrom A B) := by
  intro j hj
  simp only [lowerAvail, Finset.mem_union, Finset.mem_image] at hj
  rw [mem_availableLower]
  rcases hj with ⟨x, hx, rfl⟩ | ⟨i, hi, rfl⟩
  · have hA : x.1 ∈ A := (Finset.mem_product.mp hx).1
    have hu : aNode x.1 ∈ upperFrom A B := (aNode_mem_upperFrom _ _ _).2 hA
    convert hu using 1
    apply Fin.ext
    have h16 : (lowerA x).val < 16 := by simp [lowerA]; omega
    rw [upperOfLower, dif_pos h16]
    simp [lowerA, aNode]
    omega
  · have hu : bNode i ∈ upperFrom A B := (bNode_mem_upperFrom _ _ _).2 hi
    convert hu using 1
    apply Fin.ext
    have h16 : ¬ (lowerB i).val < 16 := by simp [lowerB]
    rw [upperOfLower, dif_neg h16]
    simp [lowerB, bNode]
    omega

abbrev RawStructure :=
  (Finset (Fin 8) × Finset (Fin 2)) × Finset (Fin 18)

def abPairs (a b : ℕ) : Finset (Finset (Fin 8) × Finset (Fin 2)) :=
  Finset.powersetCard a Finset.univ ×ˢ Finset.powersetCard b Finset.univ

def rawStructures (a b g : ℕ) : Finset RawStructure :=
  ((abPairs a b).sigma fun x =>
    Finset.powersetCard g (lowerAvail x.1 x.2)).image fun x => (x.1, x.2)

theorem rawStructure_mk_injective : Function.Injective
    (fun x : (ab : Finset (Fin 8) × Finset (Fin 2)) × Finset (Fin 18) =>
      ((x.1, x.2) : RawStructure)) := by
  rintro ⟨ab, L⟩ ⟨ab', L'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem card_abPairs (a b : ℕ) :
    (abPairs a b).card = Nat.choose 8 a * Nat.choose 2 b := by
  rw [abPairs, Finset.card_product, Finset.card_powersetCard,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
    Finset.card_univ, Fintype.card_fin]

theorem card_rawStructures (a b g : ℕ) :
    (rawStructures a b g).card =
      Nat.choose 8 a * Nat.choose 2 b * Nat.choose (2 * a + b) g := by
  rw [rawStructures,
    Finset.card_image_of_injective _ rawStructure_mk_injective,
    Finset.card_sigma]
  have hinner : ∀ ab ∈ abPairs a b,
      (Finset.powersetCard g (lowerAvail ab.1 ab.2)).card =
        Nat.choose (2 * a + b) g := by
    intro ab hab
    unfold abPairs at hab
    rw [Finset.mem_product, Finset.mem_powersetCard,
      Finset.mem_powersetCard] at hab
    rw [Finset.card_powersetCard, card_lowerAvail, hab.1.2, hab.2.2]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul,
    card_abPairs]

theorem mem_rawStructures (a b g : ℕ) (r : RawStructure) :
    r ∈ rawStructures a b g ↔
      r.1.1.card = a ∧ r.1.2.card = b ∧ r.2.card = g ∧
        r.2 ⊆ lowerAvail r.1.1 r.1.2 := by
  simp only [rawStructures, Finset.mem_image, Finset.mem_sigma,
    abPairs, Finset.mem_product, Finset.mem_powersetCard]
  constructor
  · rintro ⟨x, ⟨⟨hA, hB⟩, hL⟩, rfl⟩
    exact ⟨hA.2, hB.2, hL.2, hL.1⟩
  · rintro ⟨hA, hB, hLcard, hL⟩
    exact ⟨⟨r.1, r.2⟩,
      ⟨⟨⟨Finset.subset_univ _, hA⟩, ⟨Finset.subset_univ _, hB⟩⟩,
        ⟨hL, hLcard⟩⟩, rfl⟩

def lowerChain (x : Fin 18 × Fin 3) : Fin 66 := ⟨3 * x.1 + x.2, by omega⟩

def directA (i : Fin 8) : Fin 66 := ⟨54 + i, by omega⟩

def directB (x : Fin 2 × Fin 2) : Fin 66 := ⟨62 + 2 * x.1 + x.2, by omega⟩

def rawActive (A : Finset (Fin 8)) (B : Finset (Fin 2))
    (L : Finset (Fin 18)) : Finset (Fin 66) :=
  (L ×ˢ (Finset.univ : Finset (Fin 3))).image lowerChain ∪
    A.image directA ∪
      (B ×ˢ (Finset.univ : Finset (Fin 2))).image directB

theorem lowerChain_injective : Function.Injective lowerChain := by
  rintro ⟨i, r⟩ ⟨j, s⟩ h
  have hv := congrArg Fin.val h
  simp only [lowerChain] at hv
  have hi : i = j := Fin.ext (by omega)
  have hr : r = s := Fin.ext (by omega)
  exact Prod.ext hi hr

theorem directA_injective : Function.Injective directA := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [directA] at hv
  omega

theorem directB_injective : Function.Injective directB := by
  rintro ⟨i, r⟩ ⟨j, s⟩ h
  have hv := congrArg Fin.val h
  simp only [directB] at hv
  have hi : i = j := Fin.ext (by omega)
  have hr : r = s := Fin.ext (by omega)
  exact Prod.ext hi hr

theorem rawActive_lower_directA_disjoint (A : Finset (Fin 8))
    (L : Finset (Fin 18)) :
    Disjoint ((L ×ˢ (Finset.univ : Finset (Fin 3))).image lowerChain)
      (A.image directA) := by
  apply Finset.disjoint_left.mpr
  intro k hkL hkA
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hkL
  obtain ⟨i, hi, h⟩ := Finset.mem_image.mp hkA
  have hv := congrArg Fin.val h
  simp [lowerChain, directA] at hv
  omega

theorem rawActive_lower_directB_disjoint (B : Finset (Fin 2))
    (L : Finset (Fin 18)) :
    Disjoint ((L ×ˢ (Finset.univ : Finset (Fin 3))).image lowerChain)
      ((B ×ˢ (Finset.univ : Finset (Fin 2))).image directB) := by
  apply Finset.disjoint_left.mpr
  intro k hkL hkB
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hkL
  obtain ⟨y, hy, h⟩ := Finset.mem_image.mp hkB
  have hv := congrArg Fin.val h
  simp [lowerChain, directB] at hv
  omega

theorem rawActive_direct_disjoint (A : Finset (Fin 8))
    (B : Finset (Fin 2)) :
    Disjoint (A.image directA)
      ((B ×ˢ (Finset.univ : Finset (Fin 2))).image directB) := by
  apply Finset.disjoint_left.mpr
  intro k hkA hkB
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hkA
  obtain ⟨y, hy, h⟩ := Finset.mem_image.mp hkB
  have hv := congrArg Fin.val h
  simp [directA, directB] at hv
  omega

theorem card_rawActive (A : Finset (Fin 8)) (B : Finset (Fin 2))
    (L : Finset (Fin 18)) :
    (rawActive A B L).card = 3 * L.card + A.card + 2 * B.card := by
  unfold rawActive
  have hlast : Disjoint
      ((L ×ˢ (Finset.univ : Finset (Fin 3))).image lowerChain ∪
        A.image directA)
      ((B ×ˢ (Finset.univ : Finset (Fin 2))).image directB) :=
    Finset.disjoint_union_left.mpr
      ⟨rawActive_lower_directB_disjoint B L,
        rawActive_direct_disjoint A B⟩
  rw [Finset.card_union_of_disjoint hlast,
    Finset.card_union_of_disjoint (rawActive_lower_directA_disjoint A L),
    Finset.card_image_of_injective _ lowerChain_injective,
    Finset.card_image_of_injective _ directA_injective,
    Finset.card_image_of_injective _ directB_injective,
    Finset.card_product, Finset.card_product,
    Finset.card_univ, Fintype.card_fin, Finset.card_univ, Fintype.card_fin]
  omega

theorem lowerOfChain_lowerChain (j : Fin 18) (r : Fin 3) :
    lowerOfChain (lowerChain (j, r)) = some j := by
  unfold lowerOfChain
  rw [dif_pos (by simp [lowerChain]; omega)]
  congr 2
  simp [lowerChain]
  omega

theorem upperOfChain_lowerChain (j : Fin 18) (r : Fin 3) :
    upperOfChain (lowerChain (j, r)) = upperOfLower j := by
  unfold upperOfChain
  rw [dif_pos (by simp [lowerChain]; omega)]
  congr 1
  apply Fin.ext
  simp [lowerChain]
  omega

theorem lowerOfChain_directA (i : Fin 8) :
    lowerOfChain (directA i) = none := by
  simp [lowerOfChain, directA]

theorem upperOfChain_directA (i : Fin 8) :
    upperOfChain (directA i) = aNode i := by
  unfold upperOfChain
  rw [dif_neg (by simp [directA]), dif_pos (by simp [directA]; omega)]
  apply Fin.ext
  simp [directA, aNode]

theorem lowerOfChain_directB (i : Fin 2) (r : Fin 2) :
    lowerOfChain (directB (i, r)) = none := by
  unfold lowerOfChain
  rw [dif_neg (by simp [directB]; omega)]

theorem upperOfChain_directB (i : Fin 2) (r : Fin 2) :
    upperOfChain (directB (i, r)) = bNode i := by
  unfold upperOfChain
  rw [dif_neg (by simp [directB]; omega),
    dif_neg (by simp [directB]; omega)]
  by_cases h64 : (directB (i, r)).val < 64
  · rw [dif_pos h64]
    apply Fin.ext
    simp [directB, bNode] at h64 ⊢
    omega
  · rw [dif_neg h64]
    apply Fin.ext
    simp [directB, bNode] at h64 ⊢
    omega

theorem rawActive_eq_active (A : Finset (Fin 8)) (B : Finset (Fin 2))
    (L : Finset (Fin 18)) (hL : L ⊆ lowerAvail A B) :
    rawActive A B L = active ⟨upperFrom A B, L⟩ := by
  ext k
  constructor
  · intro hk
    simp only [rawActive, Finset.mem_union] at hk
    rcases hk with (hk | hk) | hk
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hj, hr⟩ := Finset.mem_product.mp hx
      rw [mem_active, upperOfChain_lowerChain, lowerOfChain_lowerChain]
      exact ⟨(mem_availableLower _ _).1
        (lowerAvail_subset_availableLower A B (hL hj)), hj⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
      rw [mem_active, upperOfChain_directA, lowerOfChain_directA]
      exact ⟨(aNode_mem_upperFrom _ _ _).2 hi, trivial⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hi, hr⟩ := Finset.mem_product.mp hx
      rw [mem_active, upperOfChain_directB, lowerOfChain_directB]
      exact ⟨(bNode_mem_upperFrom _ _ _).2 hi, trivial⟩
  · intro hk
    obtain ⟨hu, hl⟩ := (mem_active _ _).1 hk
    by_cases h54 : k.val < 54
    · have heq : lowerOfChain k = some ⟨k.val / 3, by omega⟩ := by
        simp [lowerOfChain, h54]
      have hj : (⟨k.val / 3, by omega⟩ : Fin 18) ∈ L := by
        simpa [heq] using hl
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨(⟨k.val / 3, by omega⟩, ⟨k.val % 3, by omega⟩), ?_, ?_⟩
      · rw [Finset.mem_product]
        exact ⟨hj, Finset.mem_univ _⟩
      · apply Fin.ext
        simp [lowerChain]
        omega
    · by_cases h62 : k.val < 62
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        have hi : (⟨k.val - 54, by omega⟩ : Fin 8) ∈ A := by
          apply (aNode_mem_upperFrom _ _ _).1
          convert hu using 1
          apply Fin.ext
          simp [upperOfChain, h54, h62, aNode]
        apply Finset.mem_image.mpr
        refine ⟨⟨k.val - 54, by omega⟩, hi, ?_⟩
        apply Fin.ext
        simp [directA]
        omega
      · apply Finset.mem_union_right
        have hi : (⟨(k.val - 62) / 2, by omega⟩ : Fin 2) ∈ B := by
          apply (bNode_mem_upperFrom _ _ _).1
          convert hu using 1
          apply Fin.ext
          by_cases h64 : k.val < 64
          · simp [upperOfChain, h54, h62, h64, bNode]
            omega
          · simp [upperOfChain, h54, h62, h64, bNode]
            omega
        apply Finset.mem_image.mpr
        refine ⟨(⟨(k.val - 62) / 2, by omega⟩,
          ⟨(k.val - 62) % 2, by omega⟩), ?_, ?_⟩
        · rw [Finset.mem_product]
          exact ⟨hi, Finset.mem_univ _⟩
        · apply Fin.ext
          simp [directB]
          omega

def Frontier.WellFormed (f : Frontier) : Prop :=
  f.lower ⊆ availableLower f.upper

/-- Number of expanded nonroot internal nodes. -/
def Frontier.expanded (f : Frontier) : ℕ := f.upper.card + f.lower.card

/-- Every ternary expansion replaces one disclosed word by three. -/
def Frontier.words (f : Frontier) : ℕ := 10 + 2 * f.expanded

/-- Root cost plus one compression for each expanded ternary node. -/
def Frontier.fixedCost (f : Frontier) : ℕ := 3 + f.expanded

/-- A full cut choice adds one bounded chain position per chain.  Inactive
positions are fixed to 18 to make the encoding injective. -/
structure Choice where
  frontier : Frontier
  position : Fin 66 → Fin 19
  deriving DecidableEq

@[ext] theorem Choice.ext {c d : Choice} (hf : c.frontier = d.frontier)
    (hp : c.position = d.position) : c = d := by
  cases c
  cases d
  simp only [Choice.mk.injEq] at hf hp ⊢
  exact ⟨hf, hp⟩

def Choice.Canonical (c : Choice) : Prop :=
  ∀ k ∉ active c.frontier, c.position k = 18

def Choice.chainCost (c : Choice) : ℕ :=
  Finset.sum (active c.frontier) fun k => 18 - (c.position k).val

/-- Exactly the cost-90, at-most-42-word layer. -/
def Choice.Valid (c : Choice) : Prop :=
  c.frontier.WellFormed ∧ c.Canonical ∧ c.frontier.expanded ≤ 16 ∧
    c.chainCost = 90 - c.frontier.fixedCost

def Choice.reconstructionCost (c : Choice) : ℕ :=
  c.frontier.fixedCost + c.chainCost

theorem Choice.words_le {c : Choice} (h : c.Valid) : c.frontier.words ≤ 42 := by
  have he : c.frontier.upper.card + c.frontier.lower.card ≤ 16 := by
    simpa [Frontier.expanded] using h.2.2.1
  unfold Frontier.words Frontier.expanded
  omega

theorem Choice.fixedCost_le {c : Choice} (h : c.Valid) : c.frontier.fixedCost ≤ 19 := by
  have he : c.frontier.upper.card + c.frontier.lower.card ≤ 16 := by
    simpa [Frontier.expanded] using h.2.2.1
  unfold Frontier.fixedCost Frontier.expanded
  omega

theorem Choice.reconstructionCost_eq {c : Choice} (h : c.Valid) :
    c.reconstructionCost = 90 := by
  unfold Choice.reconstructionCost
  rw [h.2.2.2]
  have := Choice.fixedCost_le h
  omega

/-! The position codec below is the accepted `WideCuts.positions` argument
with only `Fin 54` changed to `Fin 66`.  The chain length and position type are
unchanged, so `ShallowResearch.card_comp` applies verbatim. -/

irreducible_def positions (S : Finset (Fin 66)) (s : ℕ) : Finset (Fin 66 → Fin 19) :=
  Finset.univ.filter fun t =>
    (∀ k ∉ S, t k = 18) ∧ Finset.sum S (fun k => 18 - (t k).val) = s

theorem mem_positions (S : Finset (Fin 66)) (s : ℕ) (t : Fin 66 → Fin 19) :
    t ∈ positions S s ↔
      (∀ k ∉ S, t k = 18) ∧ Finset.sum S (fun k => 18 - (t k).val) = s := by
  rw [positions_def, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

theorem card_positions (S : Finset (Fin 66)) (s : ℕ) :
    (positions S s).card = comp S.card s := by
  rw [← card_comp]
  refine Finset.card_nbij' (fun t i => Fin.rev (t (S.equivFin.symm i)))
    (fun c k => if h : k ∈ S then Fin.rev (c (S.equivFin ⟨k, h⟩)) else 18) ?_ ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_coe, mem_positions] at ht
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← ht.2, ← Finset.sum_coe_sort S, ← Equiv.sum_comp S.equivFin.symm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.val_rev]
    omega
  · intro c hc
    rw [Finset.mem_coe, Finset.mem_filter] at hc
    rw [Finset.mem_coe, mem_positions]
    refine ⟨fun k hk => dif_neg hk, ?_⟩
    rw [← hc.2, ← Finset.sum_coe_sort S, ← Equiv.sum_comp S.equivFin
      (fun i => (c i).val)]
    refine Finset.sum_congr rfl fun x _ => ?_
    dsimp only
    rw [dif_pos x.2]
    simp only [Fin.val_rev, Subtype.coe_eta]
    omega
  · intro t ht
    rw [Finset.mem_coe, mem_positions] at ht
    funext k
    dsimp only
    by_cases hk : k ∈ S
    · simp only [dif_pos hk, Equiv.symm_apply_apply, Fin.rev_rev]
    · rw [dif_neg hk, ht.1 k hk]
  · intro c _
    funext i
    dsimp only
    have h := (S.equivFin.symm i).2
    simp only [dif_pos h, Subtype.coe_eta, Equiv.apply_symm_apply, Fin.rev_rev]

/-- All structurally valid frontiers under the 42-word cap. -/
irreducible_def structuralFrontiers : Finset Frontier :=
  Finset.univ.filter fun f => f.WellFormed ∧ f.expanded ≤ 16

theorem mem_structuralFrontiers (f : Frontier) :
    f ∈ structuralFrontiers ↔ f.WellFormed ∧ f.expanded ≤ 16 := by
  rw [structuralFrontiers_def, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- Canonical supported choices before mapping them to graph cuts. -/
irreducible_def shapes : Finset Choice :=
  (structuralFrontiers.sigma fun f =>
    positions (active f) (90 - f.fixedCost)).image fun x =>
      { frontier := x.1, position := x.2 }

theorem choice_mk_injective : Function.Injective
    (fun x : (f : Frontier) × (Fin 66 → Fin 19) =>
      ({ frontier := x.1, position := x.2 } : Choice)) := by
  rintro ⟨f, p⟩ ⟨f', p'⟩ h
  cases h
  rfl

theorem mem_shapes_iff (c : Choice) : c ∈ shapes ↔
    c.frontier ∈ structuralFrontiers ∧
      c.position ∈ positions (active c.frontier) (90 - c.frontier.fixedCost) := by
  rw [shapes, Finset.mem_image]
  constructor
  · rintro ⟨⟨f, p⟩, hp, h⟩
    rw [Finset.mem_sigma] at hp
    cases h
    exact hp
  · intro h
    exact ⟨⟨c.frontier, c.position⟩, (Finset.mem_sigma.mpr h), rfl⟩

theorem valid_of_mem_shapes {c : Choice} (hc : c ∈ shapes) : c.Valid := by
  obtain ⟨hf, hp⟩ := (mem_shapes_iff c).1 hc
  obtain ⟨hw, he⟩ := (mem_structuralFrontiers c.frontier).1 hf
  obtain ⟨hcanon, hcost⟩ := (mem_positions _ _ _).1 hp
  exact ⟨hw, hcanon, he, hcost⟩

theorem card_shapes : shapes.card =
    ∑ f ∈ structuralFrontiers, comp (active f).card (90 - f.fixedCost) := by
  rw [shapes, Finset.card_image_of_injective _ choice_mk_injective, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro f hf
  exact card_positions _ _

/-! ## Explicit mode-indexed supported family

The broad `shapes` set is useful for the cut codec, but the construction only
needs a large finite subfamily.  We enumerate that subfamily directly by the
three mode counts `(a,b,g)`, then by the chosen upper/lower nodes and chain
positions.  This avoids any appeal to a frontier ranking or to brute-force
enumeration of all structural frontiers. -/

theorem upperFrom_injective : Function.Injective
    (fun x : Finset (Fin 8) × Finset (Fin 2) => upperFrom x.1 x.2) := by
  rintro ⟨A, B⟩ ⟨A', B'⟩ h
  change upperFrom A B = upperFrom A' B' at h
  apply Prod.ext
  · ext i
    rw [← aNode_mem_upperFrom A B i,
      ← aNode_mem_upperFrom A' B' i, h]
  · ext i
    rw [← bNode_mem_upperFrom A B i,
      ← bNode_mem_upperFrom A' B' i, h]

def frontierOf (r : RawStructure) : Frontier :=
  ⟨upperFrom r.1.1 r.1.2, r.2⟩

theorem frontierOf_injective : Function.Injective frontierOf := by
  rintro ⟨⟨A, B⟩, L⟩ ⟨⟨A', B'⟩, L'⟩ h
  have hu : upperFrom A B = upperFrom A' B' :=
    congrArg Frontier.upper h
  have hl : L = L' := congrArg Frontier.lower h
  have hab : (A, B) = (A', B') := upperFrom_injective hu
  cases hab
  cases hl
  rfl

abbrev ModeDatum := (a : ℕ) × (b : ℕ) × (g : ℕ) × RawStructure

def modeStructures : Finset ModeDatum :=
  (Finset.range 9).sigma fun a =>
    (Finset.range 3).sigma fun b =>
      (Finset.range (2 * a + b + 1)).sigma fun g =>
        if a + b + g ≤ 16 then rawStructures a b g else ∅

theorem mem_modeStructures (x : ModeDatum) :
    x ∈ modeStructures ↔
      x.1 < 9 ∧ x.2.1 < 3 ∧ x.2.2.1 < 2 * x.1 + x.2.1 + 1 ∧
        x.1 + x.2.1 + x.2.2.1 ≤ 16 ∧
          x.2.2.2 ∈ rawStructures x.1 x.2.1 x.2.2.1 := by
  simp only [modeStructures, Finset.mem_sigma, Finset.mem_range]
  by_cases he : x.1 + x.2.1 + x.2.2.1 ≤ 16
  · simp [he]
  · simp [he]

def modeFrontier (x : ModeDatum) : Frontier := frontierOf x.2.2.2

set_option maxRecDepth 10000 in
theorem modeFrontier_injOn : Set.InjOn modeFrontier modeStructures := by
  rintro ⟨a, ⟨b, ⟨g, r⟩⟩⟩ hx
    ⟨a', ⟨b', ⟨g', r'⟩⟩⟩ hy hfrontier
  have hr : r = r' := frontierOf_injective hfrontier
  have hxr := (mem_rawStructures a b g r).1
    ((mem_modeStructures ⟨a, ⟨b, ⟨g, r⟩⟩⟩).1 hx).2.2.2.2
  have hyr := (mem_rawStructures a' b' g' r').1
    ((mem_modeStructures ⟨a', ⟨b', ⟨g', r'⟩⟩⟩).1 hy).2.2.2.2
  have ha : a = a' := by rw [← hxr.1, hr, hyr.1]
  have hb : b = b' := by rw [← hxr.2.1, hr, hyr.2.1]
  have hg : g = g' := by rw [← hxr.2.2.1, hr, hyr.2.2.1]
  subst a'
  subst b'
  subst g'
  subst r'
  rfl

set_option maxRecDepth 10000 in
theorem mode_active_card {x : ModeDatum} (hx : x ∈ modeStructures) :
    (active (modeFrontier x)).card = x.1 + 2 * x.2.1 + 3 * x.2.2.1 := by
  have hr := (mem_rawStructures x.1 x.2.1 x.2.2.1 x.2.2.2).1
    ((mem_modeStructures x).1 hx).2.2.2.2
  rw [modeFrontier, frontierOf]
  rw [← rawActive_eq_active x.2.2.2.1.1 x.2.2.2.1.2
    x.2.2.2.2 hr.2.2.2]
  rw [card_rawActive, hr.1, hr.2.1, hr.2.2.1]
  omega

set_option maxRecDepth 10000 in
theorem modeFrontier_wellFormed {x : ModeDatum} (hx : x ∈ modeStructures) :
    (modeFrontier x).WellFormed := by
  have hr := (mem_rawStructures x.1 x.2.1 x.2.2.1 x.2.2.2).1
    ((mem_modeStructures x).1 hx).2.2.2.2
  intro j hj
  exact lowerAvail_subset_availableLower _ _ (hr.2.2.2 hj)

set_option maxRecDepth 10000 in
theorem modeFrontier_expanded {x : ModeDatum} (hx : x ∈ modeStructures) :
    (modeFrontier x).expanded = x.1 + x.2.1 + x.2.2.1 := by
  have hr := (mem_rawStructures x.1 x.2.1 x.2.2.1 x.2.2.2).1
    ((mem_modeStructures x).1 hx).2.2.2.2
  rw [Frontier.expanded, modeFrontier, frontierOf, card_upperFrom,
    hr.1, hr.2.1, hr.2.2.1]

abbrev ModeChoiceDatum :=
  (x : ModeDatum) × (Fin 66 → Fin 19)

def modeChoiceData : Finset ModeChoiceDatum :=
  modeStructures.sigma fun x =>
    positions (active (modeFrontier x))
      (87 - (x.1 + x.2.1 + x.2.2.1))

def choiceOfMode (x : ModeChoiceDatum) : Choice :=
  ⟨modeFrontier x.1, x.2⟩

set_option maxRecDepth 10000 in
theorem choiceOfMode_injOn : Set.InjOn choiceOfMode modeChoiceData := by
  rintro ⟨x, p⟩ hx ⟨y, q⟩ hy h
  have hxmode : x ∈ modeStructures := (Finset.mem_sigma.mp hx).1
  have hymode : y ∈ modeStructures := (Finset.mem_sigma.mp hy).1
  have hfront : modeFrontier x = modeFrontier y :=
    congrArg Choice.frontier h
  have hxy : x = y := modeFrontier_injOn hxmode hymode hfront
  subst y
  have hp : p = q := congrArg Choice.position h
  subst q
  rfl

set_option maxRecDepth 10000 in
theorem choiceOfMode_valid {x : ModeChoiceDatum} (hx : x ∈ modeChoiceData) :
    (choiceOfMode x).Valid := by
  obtain ⟨hxmode, hposition⟩ := Finset.mem_sigma.mp hx
  have hm := (mem_modeStructures x.1).1 hxmode
  have he : x.1.1 + x.1.2.1 + x.1.2.2.1 ≤ 16 := hm.2.2.2.1
  have hexp := modeFrontier_expanded hxmode
  obtain ⟨hcanon, hcost⟩ := (mem_positions _ _ _).1 hposition
  refine ⟨modeFrontier_wellFormed hxmode, ?_, ?_, ?_⟩
  · intro k hk
    exact hcanon k hk
  · simpa [choiceOfMode, hexp] using he
  · rw [choiceOfMode, Choice.chainCost, hcost, Frontier.fixedCost, hexp]
    omega

/-- The supported family used by the scheme.  It is an explicitly counted
subfamily of the broad valid layer `shapes`. -/
irreducible_def supportedShapes : Finset Choice :=
  modeChoiceData.image choiceOfMode

theorem mem_supportedShapes_iff (c : Choice) : c ∈ supportedShapes ↔
    ∃ x ∈ modeChoiceData, choiceOfMode x = c := by
  rw [supportedShapes, Finset.mem_image]

set_option maxRecDepth 10000 in
theorem valid_of_mem_supportedShapes {c : Choice}
    (hc : c ∈ supportedShapes) : c.Valid := by
  obtain ⟨x, hx, rfl⟩ := (mem_supportedShapes_iff c).1 hc
  exact choiceOfMode_valid hx

set_option maxRecDepth 10000 in
theorem supportedShapes_subset_shapes : supportedShapes ⊆ shapes := by
  intro c hc
  have hv := valid_of_mem_supportedShapes hc
  apply (mem_shapes_iff c).2
  exact ⟨(mem_structuralFrontiers c.frontier).2 ⟨hv.1, hv.2.2.1⟩,
    (mem_positions _ _ _).2 ⟨hv.2.1, hv.2.2.2⟩⟩

theorem card_supportedShapes_eq_modeChoiceData :
    supportedShapes.card = modeChoiceData.card := by
  rw [supportedShapes]
  exact Finset.card_image_of_injOn choiceOfMode_injOn

set_option maxRecDepth 10000 in
theorem card_modeChoiceData : modeChoiceData.card =
    ∑ a ∈ Finset.range 9, ∑ b ∈ Finset.range 3,
      ∑ g ∈ Finset.range (2 * a + b + 1),
        if a + b + g ≤ 16 then
          (Nat.choose 8 a * Nat.choose 2 b * Nat.choose (2 * a + b) g) *
            comp (a + 2 * b + 3 * g) (87 - (a + b + g))
        else 0 := by
  rw [modeChoiceData, Finset.card_sigma, modeStructures, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro g hg
  by_cases he : a + b + g ≤ 16
  · simp only [he, if_pos]
    have hterm : ∀ r ∈ rawStructures a b g,
        (positions (active (modeFrontier ⟨a, ⟨b, ⟨g, r⟩⟩⟩))
          (87 - (a + b + g))).card =
            comp (a + 2 * b + 3 * g) (87 - (a + b + g)) := by
      intro r hr
      rw [card_positions]
      congr 1
      apply mode_active_card
      simp [modeStructures, ha, hb, hg, he, hr]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul,
      card_rawStructures]
  · simp [he]

theorem card_supportedShapes_formula : supportedShapes.card =
    ∑ a ∈ Finset.range 9, ∑ b ∈ Finset.range 3,
      ∑ g ∈ Finset.range (2 * a + b + 1),
        if a + b + g ≤ 16 then
          (Nat.choose 8 a * Nat.choose 2 b * Nat.choose (2 * a + b) g) *
            comp (a + 2 * b + 3 * g) (87 - (a + b + g))
        else 0 := by
  rw [card_supportedShapes_eq_modeChoiceData, card_modeChoiceData]

/-! ## Cut codec -/

def upperStops (f : Frontier) : Finset (Fin 10) := Finset.univ \ f.upper

def lowerStops (f : Frontier) : Finset (Fin 18) := availableLower f.upper \ f.lower

/-- The disclosure cut encoded by a frontier and its active chain positions. -/
def cutOf (c : Choice) : Finset Name :=
  (upperStops c.frontier).image Name.mv ∪
    (lowerStops c.frontier).image Name.sv ∪
    (active c.frontier).image fun k => chainNode k (c.position k)

theorem chainNode_pair_injective {k k' : Fin 66} {p p' : Fin 19}
    (h : chainNode k p = chainNode k' p') : k = k' ∧ p = p' := by
  unfold chainNode at h
  split_ifs at h with hp hp'
  · have hk : k = k' := Name.src.inj h
    have hpp : p = p' := Fin.ext (by omega)
    exact ⟨hk, hpp⟩
  · have hv := Name.cv.inj h
    have hk : k = k' := hv.1
    have hpp : p = p' := Fin.ext (by
      have ht := congrArg Fin.val hv.2
      simp only at ht
      omega)
    exact ⟨hk, hpp⟩

theorem chainNode_injective (p : Fin 66 → Fin 19) :
    Function.Injective fun k => chainNode k (p k) := by
  intro k k' h
  exact (chainNode_pair_injective h).1

@[simp] theorem mv_mem_cutOf_iff (c : Choice) (u : Fin 10) :
    Name.mv u ∈ cutOf c ↔ u ∈ upperStops c.frontier := by
  constructor
  · intro h
    simp only [cutOf, Finset.mem_union, Finset.mem_image] at h
    rcases h with (⟨u', hu', heq⟩ | ⟨j, _, heq⟩) | ⟨k, _, heq⟩
    · exact (Name.mv.inj heq) ▸ hu'
    · contradiction
    · unfold chainNode at heq
      split_ifs at heq <;> contradiction
  · intro h
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_image_of_mem _ h

@[simp] theorem sv_mem_cutOf_iff (c : Choice) (j : Fin 18) :
    Name.sv j ∈ cutOf c ↔ j ∈ lowerStops c.frontier := by
  constructor
  · intro h
    simp only [cutOf, Finset.mem_union, Finset.mem_image] at h
    rcases h with (⟨u, _, heq⟩ | ⟨j', hj', heq⟩) | ⟨k, _, heq⟩
    · contradiction
    · exact (Name.sv.inj heq) ▸ hj'
    · unfold chainNode at heq
      split_ifs at heq <;> contradiction
  · intro h
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image_of_mem _ h

theorem chainNode_mem_cutOf_iff (c : Choice) (k : Fin 66) (p : Fin 19) :
    chainNode k p ∈ cutOf c ↔
      k ∈ active c.frontier ∧ c.position k = p := by
  constructor
  · intro h
    simp only [cutOf, Finset.mem_union, Finset.mem_image] at h
    rcases h with (⟨u, _, hu⟩ | ⟨j, _, hj⟩) | ⟨k', hk', heq⟩
    · unfold chainNode at hu
      split_ifs at hu <;> contradiction
    · unfold chainNode at hj
      split_ifs at hj <;> contradiction
    · obtain ⟨hkk, hpp⟩ := chainNode_pair_injective heq
      subst k'
      exact ⟨hk', hpp⟩
  · rintro ⟨hk, hp⟩
    subst p
    apply Finset.mem_union_right
    exact Finset.mem_image_of_mem _ hk

/-- The source-to-root value path used by the cut proof. -/
def OnPath (k : Fin 66) (n : Name) : Prop :=
  n = .src k ∨ (∃ t, n = .cv k t) ∨
    (∃ j, lowerOfChain k = some j ∧ n = .sv j) ∨ n = .mv (upperOfChain k)

@[simp] theorem onPath_mv_iff (k : Fin 66) (u : Fin 10) :
    OnPath k (.mv u) ↔ u = upperOfChain k := by
  simp [OnPath]

@[simp] theorem onPath_sv_iff (k : Fin 66) (j : Fin 18) :
    OnPath k (.sv j) ↔ lowerOfChain k = some j := by
  simp [OnPath]

@[simp] theorem onPath_chainNode_iff (k k' : Fin 66) (p : Fin 19) :
    OnPath k (chainNode k' p) ↔ k' = k := by
  unfold chainNode OnPath
  split_ifs <;> simp

/-- The unique value selected on source path `k`. -/
def selected (c : Choice) (k : Fin 66) : Name :=
  if upperOfChain k ∈ c.frontier.upper then
    match lowerOfChain k with
    | none => chainNode k (c.position k)
    | some j => if j ∈ c.frontier.lower then chainNode k (c.position k) else .sv j
  else .mv (upperOfChain k)

theorem selected_mem_cutOf (c : Choice) (k : Fin 66) :
    selected c k ∈ cutOf c := by
  unfold selected
  split_ifs with hu
  · split <;> rename_i hl
    · apply Finset.mem_union_right
      exact Finset.mem_image_of_mem _ ((mem_active _ _).2 ⟨hu, by simp [hl]⟩)
    · split_ifs with hj
      · apply Finset.mem_union_right
        exact Finset.mem_image_of_mem _ ((mem_active _ _).2 ⟨hu, by simp [hl, hj]⟩)
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        apply Finset.mem_image_of_mem
        simp only [lowerStops, Finset.mem_sdiff, mem_availableLower]
        exact ⟨by rwa [← upperOfChain_eq_upperOfLower hl], hj⟩
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_image_of_mem
    simp [upperStops, hu]

theorem selected_onPath (c : Choice) (k : Fin 66) : OnPath k (selected c k) := by
  unfold selected
  by_cases hu : upperOfChain k ∈ c.frontier.upper
  · rw [if_pos hu]
    cases hl : lowerOfChain k with
    | none =>
        simp only [hl]
        exact (onPath_chainNode_iff _ _ _).2 rfl
    | some j =>
        simp only [hl]
        by_cases hj : j ∈ c.frontier.lower
        · rw [if_pos hj]
          exact (onPath_chainNode_iff _ _ _).2 rfl
        · rw [if_neg hj]
          exact (onPath_sv_iff _ _).2 hl
  · rw [if_neg hu]
    exact (onPath_mv_iff _ _).2 rfl

theorem eq_selected_of_mem_onPath (c : Choice) (hw : c.frontier.WellFormed)
    {k : Fin 66} {n : Name} (hn : n ∈ cutOf c) (hp : OnPath k n) :
    n = selected c k := by
  simp only [cutOf, Finset.mem_union, Finset.mem_image] at hn
  rcases hn with (⟨u, hu, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨k', hk', rfl⟩
  · have heq : u = upperOfChain k := (onPath_mv_iff _ _).1 hp
    subst u
    have hnot : upperOfChain k ∉ c.frontier.upper := by
      simpa [upperStops] using hu
    simp [selected, hnot]
  · have hl : lowerOfChain k = some j := (onPath_sv_iff _ _).1 hp
    have hparts : j ∈ availableLower c.frontier.upper ∧ j ∉ c.frontier.lower := by
      simpa [lowerStops] using hj
    have hu : upperOfChain k ∈ c.frontier.upper := by
      rw [upperOfChain_eq_upperOfLower hl]
      exact (mem_availableLower _ _).1 hparts.1
    unfold selected
    rw [if_pos hu]
    simp only [hl]
    rw [if_neg hparts.2]
  · have heq : k' = k := (onPath_chainNode_iff _ _ _).1 hp
    subst k'
    have ha := (mem_active _ _).1 hk'
    unfold selected
    rw [if_pos ha.1]
    cases hl : lowerOfChain k with
    | none => simp only [hl]
    | some j =>
        have hj : j ∈ c.frontier.lower := by simpa [hl] using ha.2
        simp only [hl]
        rw [if_pos hj]

/-- Semantic cut interface.  The uniqueness field is the tree-antichain fact
specialized to source paths; the later graph bridge turns it into the generic
`WideForest.IsCut.antichain` statement. -/
structure IsCut (A : Finset Name) : Prop where
  values : ∀ n ∈ A, n.len = 129
  exists_on_path : ∀ k, ∃ n ∈ A, OnPath k n
  unique_on_path : ∀ k n, n ∈ A → OnPath k n →
    ∀ m, m ∈ A → OnPath k m → m = n

theorem cutOf_values (c : Choice) : ∀ n ∈ cutOf c, n.len = 129 := by
  intro n hn
  simp only [cutOf, Finset.mem_union, Finset.mem_image] at hn
  rcases hn with (⟨j, _, rfl⟩ | ⟨j, _, rfl⟩) | ⟨k, _, rfl⟩
  · rfl
  · rfl
  · exact chainNode_len _ _

/-- The remaining graph-independent cut obligation.  It is intentionally a
named seam: its proof is a finite case split on whether the upper node and,
when present, the lower node on a chain path were expanded. -/
theorem cutCodecCorrect (c : Choice) (hw : c.frontier.WellFormed) : IsCut (cutOf c) where
  values := cutOf_values c
  exists_on_path k := ⟨selected c k, selected_mem_cutOf c k, selected_onPath c k⟩
  unique_on_path k n hn hnp m hm hmp := by
    rw [eq_selected_of_mem_onPath c hw hn hnp, eq_selected_of_mem_onPath c hw hm hmp]

/-- Canonical choices are recovered from their cuts. -/
theorem cutOf_injective : Set.InjOn cutOf shapes := by
  intro c hc d hd hcut
  have hupperStops : upperStops c.frontier = upperStops d.frontier := by
    ext u
    rw [← mv_mem_cutOf_iff c u, ← mv_mem_cutOf_iff d u, hcut]
  have hupper : c.frontier.upper = d.frontier.upper := by
    ext u
    have hn : u ∉ c.frontier.upper ↔ u ∉ d.frontier.upper := by
      have hm := Finset.ext_iff.mp hupperStops u
      simpa [upperStops] using hm
    tauto
  have hcvalid := valid_of_mem_shapes hc
  have hdvalid := valid_of_mem_shapes hd
  have hlowerStops : lowerStops c.frontier = lowerStops d.frontier := by
    ext j
    rw [← sv_mem_cutOf_iff c j, ← sv_mem_cutOf_iff d j, hcut]
  have hlower : c.frontier.lower = d.frontier.lower := by
    ext j
    by_cases hj : j ∈ availableLower c.frontier.upper
    · have hn : j ∉ c.frontier.lower ↔ j ∉ d.frontier.lower := by
        have hm := Finset.ext_iff.mp hlowerStops j
        have hjd : j ∈ availableLower d.frontier.upper := by rwa [← hupper]
        simpa [lowerStops, hj, hjd] using hm
      tauto
    · have hcj : j ∉ c.frontier.lower := fun h => hj (hcvalid.1 h)
      have hdj : j ∉ d.frontier.lower := fun h =>
        hj (by rw [hupper]; exact hdvalid.1 h)
      simp [hcj, hdj]
  have hfrontier : c.frontier = d.frontier := by
    apply Frontier.ext
    · exact hupper
    · exact hlower
  have hposition : c.position = d.position := by
    funext k
    by_cases hk : k ∈ active c.frontier
    · have hm : chainNode k (c.position k) ∈ cutOf d := by
        rw [← hcut]
        exact (chainNode_mem_cutOf_iff c k _).2 ⟨hk, rfl⟩
      have hp := (chainNode_mem_cutOf_iff d k _).1 hm
      exact hp.2.symm
    · have hkd : k ∉ active d.frontier := by rwa [← hfrontier]
      rw [hcvalid.2.1 k hk, hdvalid.2.1 k hkd]
  apply Choice.ext
  · exact hfrontier
  · exact hposition

/-- The actual supported cut family. -/
irreducible_def family : Finset (Finset Name) := supportedShapes.image cutOf

theorem mem_family_iff (A : Finset Name) :
    A ∈ family ↔ ∃ c ∈ supportedShapes, cutOf c = A := by
  rw [family, Finset.mem_image]

theorem isCut_of_mem_family {A : Finset Name} (hA : A ∈ family) : IsCut A := by
  obtain ⟨c, hc, rfl⟩ := (mem_family_iff A).1 hA
  exact cutCodecCorrect c (valid_of_mem_supportedShapes hc).1

theorem cost90_of_mem_family {A : Finset Name} (hA : A ∈ family) :
    ∃ c ∈ supportedShapes, cutOf c = A ∧ c.reconstructionCost = 90 := by
  obtain ⟨c, hc, hcut⟩ := (mem_family_iff A).1 hA
  exact ⟨c, hc, hcut,
    Choice.reconstructionCost_eq (valid_of_mem_supportedShapes hc)⟩

theorem words42_of_mem_family {A : Finset Name} (hA : A ∈ family) :
    ∃ c ∈ supportedShapes, cutOf c = A ∧ c.frontier.words ≤ 42 := by
  obtain ⟨c, hc, hcut⟩ := (mem_family_iff A).1 hA
  exact ⟨c, hc, hcut, Choice.words_le (valid_of_mem_supportedShapes hc)⟩

theorem cutOf_injective_supported :
    Set.InjOn cutOf supportedShapes :=
  cutOf_injective.mono supportedShapes_subset_shapes

theorem card_family_eq_supportedShapes :
    family.card = supportedShapes.card := by
  rw [family]
  exact Finset.card_image_of_injOn cutOf_injective_supported

/-! ## Exact cardinality certificate -/

/-- Range-19 coefficient, evaluated through the already proved polynomial
dynamic-programming table rather than exponential unfolding of `comp`. -/
def boundedComp (n s : ℕ) : ℕ := (compTable 87 n).getD s 0

theorem boundedComp_eq (n s : ℕ) (hs : s ≤ 87) : boundedComp n s = comp n s :=
  compTable_getD 87 n s hs

/-- Contribution of mode `(a,b,g)`: `a` expanded A nodes, `b` expanded B
nodes, and `g` expanded lower S nodes. -/
def modeCount (a b g : ℕ) : ℕ :=
  if a ≤ 8 ∧ b ≤ 2 ∧ g ≤ 2 * a + b ∧ a + b + g ≤ 16 then
    Nat.choose 8 a * Nat.choose 2 b * Nat.choose (2 * a + b) g *
      boundedComp (a + 2 * b + 3 * g) (87 - (a + b + g))
  else 0

/-- Exact number of supported cost-90 cuts. -/
def classCount : ℕ :=
  ∑ a ∈ Finset.range 9, ∑ b ∈ Finset.range 3,
    ∑ g ∈ Finset.range (2 * a + b + 1), modeCount a b g

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem classCount_exact :
    classCount = 676013856769711926075368867014708 := by
  decide +kernel

theorem card_supportedShapes_eq_classCount :
    supportedShapes.card = classCount := by
  rw [card_supportedShapes_formula, classCount]
  apply Finset.sum_congr rfl
  intro a ha
  have ha' := Finset.mem_range.mp ha
  apply Finset.sum_congr rfl
  intro b hb
  have hb' := Finset.mem_range.mp hb
  apply Finset.sum_congr rfl
  intro g hg
  have hg' := Finset.mem_range.mp hg
  by_cases he : a + b + g ≤ 16
  · rw [if_pos he, modeCount, if_pos]
    · rw [boundedComp_eq]
      omega
    · exact ⟨by omega, by omega, by omega, he⟩
  · rw [if_neg he, modeCount, if_neg]
    intro h
    exact he h.2.2.2

theorem card_family_eq_classCount : family.card = classCount := by
  rw [card_family_eq_supportedShapes, card_supportedShapes_eq_classCount]

theorem classCount_le_family : classCount ≤ family.card := by
  rw [card_family_eq_classCount]

theorem card_family_exact :
    family.card = 676013856769711926075368867014708 := by
  rw [card_family_eq_classCount, classCount_exact]

theorem classCapacity_le_family :
    676013856769711926075368867014708 ≤ family.card := by
  rw [card_family_exact]

/-! ## Arbitrary class numbering -/

/-- Select the first `M` members of a finite family using only its canonical
finite equivalence.  No frontier rank or schedule allocation is involved. -/
def selectCut {family : Finset (Finset Name)} {M : ℕ} (hM : M ≤ family.card) :
    Fin M → Finset Name := fun i => family.equivFin.symm (Fin.castLE hM i)

theorem selectCut_mem {family : Finset (Finset Name)} {M : ℕ}
    (hM : M ≤ family.card) (i : Fin M) : selectCut hM i ∈ family :=
  (family.equivFin.symm (Fin.castLE hM i)).property

theorem selectCut_injective {family : Finset (Finset Name)} {M : ℕ}
    (hM : M ≤ family.card) : Function.Injective (selectCut hM) := by
  intro i j hij
  have hs : family.equivFin.symm (Fin.castLE hM i) =
      family.equivFin.symm (Fin.castLE hM j) := Subtype.ext hij
  have hf : Fin.castLE hM i = Fin.castLE hM j := family.equivFin.symm.injective hs
  have hv : i.val = j.val := by
    change (Fin.castLE hM i).val = (Fin.castLE hM j).val
    exact congrArg Fin.val hf
  exact Fin.ext hv

end OptimalOTS.WeightedConstruction.LongChain91
