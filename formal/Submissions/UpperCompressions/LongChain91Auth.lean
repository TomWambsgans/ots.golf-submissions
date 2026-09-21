import Submissions.UpperCompressions.LongChain91Scheme
import Submissions.UpperCompressions.ProofBundle05

/-!
# Authentication bridge for the cost-91 long-chain construction

This module identifies the concrete key-generation oracle points of the
long-chain graph, splits them into exposed and hidden points after signing,
and defines the spurious-output authentication event used by the accepted
weighted-game proof.  The final section proves the fresh-query charge for
that event, including the 128-bit public root.
-/

open OracleSpec OracleComp ENNReal
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace OptimalOTS.WeightedConstruction.LongChain91

open OptimalOTS.Dag
open Name

/-! ## Index queries -/

abbrev EncInput := Message × BitVec 86

def encQuery (u : EncInput) : Query := ⟨msgBits + 86, u.1 ++ u.2⟩

theorem encQuery_length (u : EncInput) : (encQuery u).1 = 342 := rfl

theorem ne_encQuery_of_length_ne {q : Query} (hq : q.1 ≠ msgBits + 86)
    (u : EncInput) : q ≠ encQuery u := by
  intro h
  exact hq (congrArg Sigma.fst h)

/-! ## Concrete record values -/

abbrev Rec := graph.Rec

def val (ξ : Rec) (n : Name) : BitVec n.len :=
  (graph.evalRec ξ n.fin).cast (graph_len_fin n)

theorem lowWord_cast {n m : ℕ} (h : n = m) (x : BitVec n) :
    lowWord (x.cast h) = lowWord x := by
  subst h
  rfl

theorem lowWord_lowWord {n : ℕ} (x : BitVec n) :
    lowWord (lowWord x) = lowWord x := BitVec.setWidth_eq _

theorem cast_cast_eq {n m : ℕ} (h₁ : n = m) (h₂ : m = n) (x : BitVec n) :
    (x.cast h₁).cast h₂ = x := by
  subst h₁
  rfl

theorem evalRec_apply_fin (ξ : Rec) (n : Name) :
    graph.evalRec ξ n.fin =
      (kindOf n.fin n (Name.ofFin_fin n)).value
        (graph.evalRec ξ) (ξ.1 n.fin) (ξ.2 n.fin) := by
  have h := Graph.evalRec_apply graph ξ n.fin
  rwa [graph_kind_fin] at h

theorem lowWord_evalRec (ξ : Rec) (n : Name) :
    lowWord (graph.evalRec ξ n.fin) = lowWord (val ξ n) := by
  unfold val
  exact (lowWord_cast _ _).symm

theorem val_src (ξ : Rec) (k : Fin 66) :
    val ξ (Name.src k) = (ξ.1 (Name.src k).fin).cast (graph_len_fin _) := by
  unfold val
  rw [evalRec_apply_fin]
  rfl

theorem lowWord_eq_self (x : BitVec 129) : lowWord x = x := BitVec.setWidth_eq _

theorem val_ci (ξ : Rec) (k : Fin 66) (t : Fin 18) :
    val ξ (Name.ci k t) = tw (Name.ch k t) ++ lowWord (val ξ (prev k t)) := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  refine (cast_cast_eq _ _ _).trans ?_
  show tw (Name.ch k t) ++ lowWord (graph.evalRec ξ (prev k t).fin) = _
  rw [lowWord_evalRec]
  rfl

theorem val_ch (ξ : Rec) (k : Fin 66) (t : Fin 18) :
    val ξ (Name.ch k t) = ξ.2 (Name.ch k t).fin := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  exact cast_cast_eq _ _ _

theorem lowWord_val_ch (ξ : Rec) (k : Fin 66) (t : Fin 18) :
    lowWord (graph.evalRec ξ (Name.ch k t).fin) = lowWord (ξ.2 (Name.ch k t).fin) := by
  rw [lowWord_evalRec, val_ch]
  rfl

theorem val_cv (ξ : Rec) (k : Fin 66) (t : Fin 18) :
    val ξ (Name.cv k t) = lowWord (ξ.2 (Name.ch k t).fin) := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  refine (cast_cast_eq _ _ _).trans ?_
  exact lowWord_val_ch ξ k t

theorem lowWord_val_cv (ξ : Rec) (k : Fin 66) (t : Fin 18) :
    lowWord (graph.evalRec ξ (Name.cv k t).fin) = lowWord (ξ.2 (Name.ch k t).fin) := by
  rw [lowWord_evalRec, val_cv]
  exact lowWord_lowWord _

theorem val_sc (ξ : Rec) (j : Fin 18) :
    val ξ (Name.sc j) = tw (Name.sh j) ++ cat3
      (lowWord (ξ.2 (Name.ch (Name.lowerChain j 0) 17).fin))
      (lowWord (ξ.2 (Name.ch (Name.lowerChain j 1) 17).fin))
      (lowWord (ξ.2 (Name.ch (Name.lowerChain j 2) 17).fin)) := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  refine (cast_cast_eq _ _ _).trans ?_
  show tw (Name.sh j) ++ cat3
      (lowWord (graph.evalRec ξ (Name.cv (Name.lowerChain j 0) 17).fin))
      (lowWord (graph.evalRec ξ (Name.cv (Name.lowerChain j 1) 17).fin))
      (lowWord (graph.evalRec ξ (Name.cv (Name.lowerChain j 2) 17).fin)) = _
  rw [lowWord_val_cv, lowWord_val_cv, lowWord_val_cv]

theorem val_sh (ξ : Rec) (j : Fin 18) : val ξ (Name.sh j) = ξ.2 (Name.sh j).fin := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  exact cast_cast_eq _ _ _

theorem lowWord_val_sh (ξ : Rec) (j : Fin 18) :
    lowWord (graph.evalRec ξ (Name.sh j).fin) = lowWord (ξ.2 (Name.sh j).fin) := by
  rw [lowWord_evalRec, val_sh]
  rfl

theorem val_sv (ξ : Rec) (j : Fin 18) :
    val ξ (Name.sv j) = lowWord (ξ.2 (Name.sh j).fin) := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  refine (cast_cast_eq _ _ _).trans ?_
  exact lowWord_val_sh ξ j

theorem lowWord_val_sv (ξ : Rec) (j : Fin 18) :
    lowWord (graph.evalRec ξ (Name.sv j).fin) = lowWord (ξ.2 (Name.sh j).fin) := by
  rw [lowWord_evalRec, val_sv]
  exact lowWord_lowWord _

theorem val_mc (ξ : Rec) (u : Fin 10) :
    val ξ (Name.mc u) = tw (Name.mh u) ++ cat3
      (lowWord (val ξ (midChild u 0)))
      (lowWord (val ξ (midChild u 1)))
      (lowWord (val ξ (midChild u 2))) := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  refine (cast_cast_eq _ _ _).trans ?_
  show tw (Name.mh u) ++ cat3
      (lowWord (graph.evalRec ξ (midChild u 0).fin))
      (lowWord (graph.evalRec ξ (midChild u 1).fin))
      (lowWord (graph.evalRec ξ (midChild u 2).fin)) = _
  rw [lowWord_evalRec, lowWord_evalRec, lowWord_evalRec]
  rfl

theorem val_mh (ξ : Rec) (u : Fin 10) : val ξ (Name.mh u) = ξ.2 (Name.mh u).fin := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  exact cast_cast_eq _ _ _

theorem lowWord_val_mh (ξ : Rec) (u : Fin 10) :
    lowWord (graph.evalRec ξ (Name.mh u).fin) = lowWord (ξ.2 (Name.mh u).fin) := by
  rw [lowWord_evalRec, val_mh]
  rfl

theorem val_mv (ξ : Rec) (u : Fin 10) :
    val ξ (Name.mv u) = lowWord (ξ.2 (Name.mh u).fin) := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  refine (cast_cast_eq _ _ _).trans ?_
  exact lowWord_val_mh ξ u

theorem lowWord_val_mv (ξ : Rec) (u : Fin 10) :
    lowWord (graph.evalRec ξ (Name.mv u).fin) = lowWord (ξ.2 (Name.mh u).fin) := by
  rw [lowWord_evalRec, val_mv]
  exact lowWord_lowWord _

theorem val_rc (ξ : Rec) :
    val ξ Name.rc = tw Name.rh ++ cat10 (fun u => lowWord (ξ.2 (Name.mh u).fin)) := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  refine (cast_cast_eq _ _ _).trans ?_
  show tw Name.rh ++ cat10 (fun u => lowWord (graph.evalRec ξ (Name.mv u).fin)) = _
  exact congrArg (fun a => tw Name.rh ++ cat10 a) (funext fun u => lowWord_val_mv ξ u)

theorem val_rh (ξ : Rec) : val ξ Name.rh = ξ.2 Name.rh.fin := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  exact cast_cast_eq _ _ _

def pkOf (ξ : Rec) : BitVec 128 := lowPk (ξ.2 Name.rh.fin)

/-! ## Hash inputs and graph tagging -/

def hashParent : Name → Option Name
  | Name.ch k t => some (Name.ci k t)
  | Name.sh j => some (Name.sc j)
  | Name.mh u => some (Name.mc u)
  | Name.rh => some Name.rc
  | _ => none

theorem hashParent_isSome_iff (h : Name) :
    (hashParent h).isSome ↔ h.cost ≠ 0 := by
  cases h <;> simp [hashParent, Name.cost]

theorem cost_ne_zero_of_hashParent {h p : Name} (hp : hashParent h = some p) :
    h.cost ≠ 0 :=
  (hashParent_isSome_iff h).1 (by rw [hp]; rfl)

theorem child_hashParent {h p : Name} (hp : hashParent h = some p) :
    child p = some h := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    subst hp <;> rfl

theorem len_hashParent_cases {h p : Name} (hp : hashParent h = some p) :
    p.len = 145 ∨ p.len = 403 ∨ p.len = 1306 := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    subst hp <;> simp [Name.len]

theorem len_hashParent_ne_enc {h p : Name} (hp : hashParent h = some p) :
    p.len ≠ msgBits + 86 := by
  have he : msgBits + 86 = 342 := rfl
  rw [he]
  rcases len_hashParent_cases hp with h | h | h <;> omega

def pointOf (ξ : Rec) (_h p : Name) : Query := ⟨p.len, val ξ p⟩

def tagNat (q : Query) : ℕ := WideForest.tagNat q

theorem tagNat_append {n : ℕ} (a : BitVec 16) (u : BitVec n) :
    tagNat ⟨16 + n, a ++ u⟩ = a.toNat :=
  WideForest.tagNat_append a u

theorem tagNat_tw_append {n : ℕ} (h : Name) (u : BitVec n) :
    tagNat ⟨16 + n, tw h ++ u⟩ = h.idx := by
  rw [tagNat_append, tw_toNat]

theorem tagNat_cast {n m : ℕ} (e : n = m) (u : BitVec n) :
    tagNat ⟨m, u.cast e⟩ = tagNat ⟨n, u⟩ :=
  WideForest.tagNat_cast e u

theorem tagNat_val {h p : Name} (hp : hashParent h = some p) (ξ : Rec) :
    tagNat ⟨p.len, val ξ p⟩ = h.idx := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp
  · rw [val_ci]; exact tagNat_tw_append _ _
  · rw [val_sc]; exact tagNat_tw_append _ _
  · rw [val_mc]; exact tagNat_tw_append _ _
  · rw [val_rc]; exact tagNat_tw_append _ _

theorem tagNat_pointOf {h p : Name} (hp : hashParent h = some p) (ξ : Rec) :
    tagNat (pointOf ξ h p) = h.idx := tagNat_val hp ξ

theorem pointOf_inj_left {ξ ξ' : Rec} {h h' p p' : Name}
    (hp : hashParent h = some p) (hp' : hashParent h' = some p')
    (e : pointOf ξ h p = pointOf ξ' h' p') : h = h' := by
  apply Name.idx_injective
  rw [← tagNat_pointOf hp ξ, ← tagNat_pointOf hp' ξ', e]

theorem pointOf_inj_input {ξ ξ' : Rec} {h p : Name}
    (e : pointOf ξ h p = pointOf ξ' h p) : val ξ p = val ξ' p := by
  simp only [pointOf, Sigma.mk.inj_iff, heq_eq_eq, true_and] at e
  exact e

theorem pointOf_ne_encQuery {h p : Name} (hp : hashParent h = some p)
    (ξ : Rec) (u : EncInput) : pointOf ξ h p ≠ encQuery u :=
  ne_encQuery_of_length_ne (len_hashParent_ne_enc hp) u

theorem mk_ne_encQuery {h p : Name} (hp : hashParent h = some p)
    (u' : BitVec p.len) (u : EncInput) :
    (⟨p.len, u'⟩ : Query) ≠ encQuery u :=
  ne_encQuery_of_length_ne (len_hashParent_ne_enc hp) u

theorem sigma_mk_cast_eq {n m : ℕ} (h : n = m) (x : BitVec n) :
    (⟨n, x⟩ : Σ k, BitVec k) = ⟨m, x.cast h⟩ := by
  subst h
  rfl

theorem sigma_val (ξ : Rec) (p : Name) :
    (⟨lenF p.fin, graph.evalRec ξ p.fin⟩ : Σ k, BitVec k) =
      ⟨p.len, val ξ p⟩ := by
  unfold val
  generalize graph.evalRec ξ p.fin = x
  exact sigma_mk_cast_eq (graph_len_fin p) x

theorem graph_point_fin (ξ : Rec) (h : Name) :
    graph.point (graph.evalRec ξ) h.fin =
      (hashParent h).map fun p => pointOf ξ h p := by
  unfold Graph.point
  rw [graph_kind_fin]
  cases h <;> simp only [kindOf, hashParent, Option.map_some, Option.map_none, pointOf]
  case ch k t => exact congrArg some (sigma_val ξ (Name.ci k t))
  case sh j => exact congrArg some (sigma_val ξ (Name.sc j))
  case mh u => exact congrArg some (sigma_val ξ (Name.mc u))
  case rh => exact congrArg some (sigma_val ξ Name.rc)

def tagOf (q : Query) : Option (Fin N) :=
  if h : tagNat q < N then some ⟨tagNat q, h⟩ else none

theorem tagOf_eq_some_of_tagNat {q : Query} {h : Name}
    (e : tagNat q = h.idx) : tagOf q = some h.fin := by
  unfold tagOf
  rw [dif_pos (by rw [e]; exact h.idx_lt)]
  exact congrArg some (Fin.ext e)

theorem graph_kind_hashParent {h p : Name} (hp : hashParent h = some p) :
    ∃ ps hps hf, graph.kind p.fin =
      .det ps hps (fun x => (detVal p x).cast (graph_len_fin p).symm) hf := by
  rw [graph_kind_fin]
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;>
    subst hp <;> exact ⟨_, _, _, rfl⟩

theorem graph_kind_eq_hash {h : Name} {q : Fin N} {hq : q < h.fin}
    {hl : lenF h.fin = 256} (hk : graph.kind h.fin = .hash q hq hl) :
    ∃ p, hashParent h = some p ∧ q = p.fin := by
  rw [graph_kind_fin] at hk
  cases h <;> simp only [kindOf, reduceCtorEq] at hk
  case ch k t => exact ⟨Name.ci k t, rfl, (NodeKind.hash.inj hk).symm⟩
  case sh j => exact ⟨Name.sc j, rfl, (NodeKind.hash.inj hk).symm⟩
  case mh u => exact ⟨Name.mc u, rfl, (NodeKind.hash.inj hk).symm⟩
  case rh => exact ⟨Name.rc, rfl, (NodeKind.hash.inj hk).symm⟩

theorem tagNat_detVal_of_hashParent {h p : Name}
    (hp : hashParent h = some p) (x : Asg) :
    tagNat ⟨p.len, detVal p x⟩ = h.idx := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp
  · exact tagNat_tw_append _ _
  · exact tagNat_tw_append _ _
  · exact tagNat_tw_append _ _
  · exact tagNat_tw_append _ _

theorem tagNat_cast_detVal_of_hashParent {h p : Name}
    (hp : hashParent h = some p) (x : Asg) {m : ℕ} (e : p.len = m) :
    tagNat ⟨m, (detVal p x).cast e⟩ = h.idx := by
  rw [tagNat_cast, tagNat_detVal_of_hashParent hp]

def tagging : graph.Tagging where
  tag q := if h : tagNat q < N then some ⟨tagNat q, h⟩ else none
  tag_parent := by
    intro v q hq hl hk
    obtain ⟨h, rfl⟩ : ∃ h : Name, h.fin = v := ⟨Name.ofFin v, Name.fin_ofFin v⟩
    obtain ⟨p, hp, rfl⟩ := graph_kind_eq_hash hk
    obtain ⟨ps, hps, hf, hkp⟩ := graph_kind_hashParent hp
    refine ⟨ps, hps, _, hf, hkp, fun x => ?_⟩
    exact tagOf_eq_some_of_tagNat
      (tagNat_cast_detVal_of_hashParent hp x (graph_len_fin p).symm)

/-! ## Key-generation cache split -/

def kc (ξ : Rec) : Cache := graph.keygenCache ξ

theorem kc_apply_iff (ξ : Rec) (q : Query) (w : BitVec 256) :
    kc ξ q = some w ↔
      ∃ h p, hashParent h = some p ∧ q = pointOf ξ h p ∧ w = ξ.2 h.fin := by
  refine (Graph.keygenCache_apply_iff graph tagging ξ q w).trans ?_
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨h, rfl⟩ : ∃ h : Name, h.fin = v := ⟨Name.ofFin v, Name.fin_ofFin v⟩
    rw [graph_point_fin, Option.map_eq_some_iff] at hv
    obtain ⟨p, hp, rfl⟩ := hv
    exact ⟨h, p, hp, rfl, rfl⟩
  · rintro ⟨h, p, hp, rfl, rfl⟩
    exact ⟨h.fin, by rw [graph_point_fin, hp]; rfl, rfl⟩

theorem kc_isSome_iff (ξ : Rec) (q : Query) :
    (kc ξ q).isSome ↔ ∃ h p, hashParent h = some p ∧ q = pointOf ξ h p := by
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨h, p, hp, hq, -⟩ := (kc_apply_iff ξ q w).1 hw
    exact ⟨h, p, hp, hq⟩
  · rintro ⟨h, p, hp, hq⟩
    exact ⟨_, (kc_apply_iff ξ q _).2 ⟨h, p, hp, hq, rfl⟩⟩

theorem kc_enc (ξ : Rec) (u : EncInput) : kc ξ (encQuery u) = none := by
  rcases hk : kc ξ (encQuery u) with _ | w
  · rfl
  · obtain ⟨h, p, hp, hq, -⟩ := (kc_apply_iff ξ _ w).1 hk
    exact absurd hq.symm (pointOf_ne_encQuery hp ξ u)

def Exposed (A? : Option (Finset Name)) (h : Name) : Prop :=
  ∃ A, A? = some A ∧ Evaluated A h

theorem exposed_some_iff_evaluated (A : Finset Name) (h : Name) :
    Exposed (some A) h ↔ Evaluated A h := by simp [Exposed]

theorem not_exposed_none (h : Name) : ¬ Exposed none h := by
  rintro ⟨A, hA, -⟩
  cases hA

def fExp (A? : Option (Finset Name)) (ξ : Rec) : Cache := fun q =>
  if ∃ h p, hashParent h = some p ∧ Exposed A? h ∧ q = pointOf ξ h p
  then kc ξ q else none

def fHid (A? : Option (Finset Name)) (ξ : Rec) : Cache := fun q =>
  if ∃ h p, hashParent h = some p ∧ ¬ Exposed A? h ∧ q = pointOf ξ h p
  then kc ξ q else none

theorem extend_fExp_fHid (A? : Option (Finset Name)) (ξ : Rec) :
    Cache.extend (fExp A? ξ) (fHid A? ξ) = kc ξ := by
  funext q
  simp only [Cache.extend_apply, fExp, fHid]
  by_cases h1 : ∃ h p, hashParent h = some p ∧ Exposed A? h ∧ q = pointOf ξ h p
  · rw [if_pos h1]
    obtain ⟨h, p, hp, -, hq⟩ := h1
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1
      ((kc_isSome_iff ξ q).2 ⟨h, p, hp, hq⟩)
    rw [hw]
    rfl
  · rw [if_neg h1, Option.none_or]
    by_cases h2 : ∃ h p, hashParent h = some p ∧ ¬ Exposed A? h ∧ q = pointOf ξ h p
    · rw [if_pos h2]
    · rw [if_neg h2]
      rcases hk : kc ξ q with _ | w
      · rfl
      · exfalso
        obtain ⟨h, p, hp, hq, -⟩ := (kc_apply_iff ξ q w).1 hk
        by_cases he : Exposed A? h
        · exact h1 ⟨h, p, hp, he, hq⟩
        · exact h2 ⟨h, p, hp, he, hq⟩

theorem disjoint_fExp_fHid (A? : Option (Finset Name)) (ξ : Rec) :
    Cache.Disjoint (fExp A? ξ) (fHid A? ξ) := by
  intro q hq
  simp only [fHid] at hq
  split_ifs at hq with h2
  · obtain ⟨h, p, hp, he, hq⟩ := h2
    simp only [fExp]
    rw [if_neg]
    rintro ⟨h', p', hp', he', hq'⟩
    rw [hq] at hq'
    obtain rfl := pointOf_inj_left hp hp' hq'
    exact he he'
  · simp at hq

theorem fHid_isSome_iff (A? : Option (Finset Name)) (ξ : Rec) (q : Query) :
    (fHid A? ξ q).isSome ↔
      ∃ h p, hashParent h = some p ∧ ¬ Exposed A? h ∧ q = pointOf ξ h p := by
  simp only [fHid]
  split_ifs with hc
  · obtain ⟨h, p, hp, -, hq⟩ := id hc
    exact iff_of_true ((kc_isSome_iff ξ q).2 ⟨h, p, hp, hq⟩) hc
  · exact iff_of_false (by simp) hc

theorem fHid_none (ξ : Rec) : fHid none ξ = kc ξ := by
  funext q
  simp only [fHid]
  split_ifs with hc
  · rfl
  · rcases hk : kc ξ q with _ | w
    · rfl
    · exfalso
      obtain ⟨h, p, hp, hq, -⟩ := (kc_apply_iff ξ q w).1 hk
      exact hc ⟨h, p, hp, not_exposed_none h, hq⟩

theorem fExp_none (ξ : Rec) : fExp none ξ = ∅ := by
  funext q
  simp only [fExp]
  rw [if_neg]
  · rfl
  · rintro ⟨h, -, -, he, -⟩
    exact not_exposed_none h he

theorem fExp_enc (A? : Option (Finset Name)) (ξ : Rec) (u : EncInput) :
    fExp A? ξ (encQuery u) = none := by
  simp only [fExp]
  rw [if_neg]
  rintro ⟨h, p, hp, -, hq⟩
  exact pointOf_ne_encQuery hp ξ u hq.symm

theorem fHid_enc (A? : Option (Finset Name)) (ξ : Rec) (u : EncInput) :
    fHid A? ξ (encQuery u) = none := by
  simp only [fHid]
  rw [if_neg]
  rintro ⟨h, p, hp, -, hq⟩
  exact pointOf_ne_encQuery hp ξ u hq.symm

theorem fHid_isSome_some_iff (A : Finset Name) (ξ : Rec) (q : Query) :
    (fHid (some A) ξ q).isSome ↔
      ∃ h p, hashParent h = some p ∧ ¬ Evaluated A h ∧ q = pointOf ξ h p := by
  simp only [fHid_isSome_iff, exposed_some_iff_evaluated]

/-! ## Spurious authentication and its exact fresh-query charge -/

def bindingWidth (h : Name) : ℕ := if h = Name.rh then 128 else 129

def bindingValue (h : Name) (w : BitVec 256) : BitVec (bindingWidth h) :=
  w.setWidth (bindingWidth h)

def Spr (c : Cache) (ξ : Rec) : Prop :=
  ∃ h p, hashParent h = some p ∧
    ∃ u : BitVec p.len, u ≠ val ξ p ∧ tagNat ⟨p.len, u⟩ = h.idx ∧
      ∃ w, c ⟨p.len, u⟩ = some w ∧
        bindingValue h w = bindingValue h (ξ.2 h.fin)

theorem Spr.mono {c c' : Cache} (h : Cache.Sub c c') {ξ : Rec}
    (hs : Spr c ξ) : Spr c' ξ := by
  obtain ⟨hn, p, hp, u, hu, htag, w, hw, ht⟩ := hs
  exact ⟨hn, p, hp, u, hu, htag, w, h _ _ hw, ht⟩

theorem spr_cacheQuery_enc (c : Cache) (ξ : Rec) (u : EncInput)
    (w : BitVec 256) : Spr (c.cacheQuery (encQuery u) w) ξ ↔ Spr c ξ := by
  have key : ∀ (h p : Name), hashParent h = some p → ∀ u' : BitVec p.len,
      c.cacheQuery (encQuery u) w ⟨p.len, u'⟩ = c ⟨p.len, u'⟩ :=
    fun h p hp u' => QueryCache.cacheQuery_of_ne _ _ (mk_ne_encQuery hp u' u)
  constructor
  · rintro ⟨h, p, hp, u', hu, htag, w', hw, ht⟩
    rw [key h p hp] at hw
    exact ⟨h, p, hp, u', hu, htag, w', hw, ht⟩
  · rintro ⟨h, p, hp, u', hu, htag, w', hw, ht⟩
    refine ⟨h, p, hp, u', hu, htag, w', ?_, ht⟩
    rw [key h p hp]
    exact hw

theorem spr_of_extend {c f : Cache} {ξ : Rec}
    (hs : Spr (Cache.extend c f) ξ) : Spr c ξ ∨ Spr f ξ := by
  obtain ⟨h, p, hp, u, hu, htag, w, hw, ht⟩ := hs
  rw [Cache.extend_apply, Option.or_eq_some_iff] at hw
  rcases hw with hw | ⟨-, hw⟩
  · exact Or.inl ⟨h, p, hp, u, hu, htag, w, hw, ht⟩
  · exact Or.inr ⟨h, p, hp, u, hu, htag, w, hw, ht⟩

theorem not_spr_kc (ξ : Rec) : ¬ Spr (kc ξ) ξ := by
  rintro ⟨h, p, hp, u, hu, htag, w, hw, -⟩
  obtain ⟨h', p', hp', hq, -⟩ := (kc_apply_iff ξ _ w).1 hw
  have hh : h = h' := by
    apply Name.idx_injective
    rw [← htag, hq, tagNat_pointOf hp' ξ]
  subst hh
  rw [hp] at hp'
  obtain rfl := Option.some.inj hp'
  exact hu (eq_of_heq (Sigma.mk.inj_iff.1 hq).2)

theorem sub_fExp_kc (A? : Option (Finset Name)) (ξ : Rec) :
    Cache.Sub (fExp A? ξ) (kc ξ) := by
  intro q w hw
  simp only [fExp] at hw
  by_cases hc : ∃ h p, hashParent h = some p ∧ Exposed A? h ∧ q = pointOf ξ h p
  · rwa [if_pos hc] at hw
  · rw [if_neg hc] at hw
    cases hw

theorem not_spr_fExp (A? : Option (Finset Name)) (ξ : Rec) :
    ¬ Spr (fExp A? ξ) ξ :=
  fun hs => not_spr_kc ξ (hs.mono (sub_fExp_kc A? ξ))

theorem not_spr_empty (ξ : Rec) : ¬ Spr ∅ ξ := by
  rintro ⟨h, p, hp, u, hu, -, w, hw, -⟩
  simp at hw

def ε : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ 129)⁻¹

theorem inv_card_bitVec_mul_two_pow :
    (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
      ((2 ^ 127 : ℕ) : ℝ≥0∞) = ε := by
  have h0 : (2 : ℝ≥0∞) ^ 127 ≠ 0 := pow_ne_zero _ two_ne_zero
  have ht : (2 : ℝ≥0∞) ^ 127 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have e : (2 : ℝ≥0∞) ^ 129 * 2 ^ 127 = 2 ^ 256 := by rw [← pow_add]
  rw [Fintype.card_bitVec, ε]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [← e, ENNReal.mul_inv (Or.inr ht) (Or.inr h0), mul_assoc,
    ENNReal.inv_mul_cancel h0 ht, mul_one]

def sprRate (h : Name) : ℝ≥0∞ := if h = Name.rh then ε + ε else ε

theorem bindingWidth_le (h : Name) : bindingWidth h ≤ 256 := by
  simp only [bindingWidth]
  split_ifs <;> omega

theorem binding_fiber (h : Name) (a : BitVec (bindingWidth h)) :
    (Finset.univ.filter fun b : BitVec 256 => bindingValue h b = a).card =
      2 ^ (256 - bindingWidth h) :=
  TruncFiber.card_filter_setWidth (bindingWidth_le h) a

theorem inv_card_binding (h : Name) :
    (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
      ((2 ^ (256 - bindingWidth h) : ℕ) : ℝ≥0∞) = sprRate h := by
  by_cases hh : h = Name.rh
  · simp only [bindingWidth, sprRate, if_pos hh]
    change (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
      ((2 ^ 128 : ℕ) : ℝ≥0∞) = ε + ε
    have he : (2 : ℕ)^128 = 2^127 + 2^127 := by
      rw [show (128 : ℕ) = 127 + 1 from rfl, pow_succ, mul_two]
    rw [he, Nat.cast_add, mul_add, inv_card_bitVec_mul_two_pow]
  · simp only [bindingWidth, sprRate, if_neg hh]
    exact inv_card_bitVec_mul_two_pow

theorem epsilon_le_query_cost (q : Query) :
    ε ≤ ε * (blockCost q.1 : ℝ≥0∞) := by
  have hc : (1 : ℝ≥0∞) ≤ (blockCost q.1 : ℝ≥0∞) := by
    exact_mod_cast Nat.le_max_left 1 ((q.1 + blockBits - 1) / blockBits)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hc
    (show (0 : ℝ≥0∞) ≤ ε from zero_le)

theorem sprRate_le_query_cost {h p : Name} (hp : hashParent h = some p)
    (q : Query) (hlen : q.1 = p.len) :
    sprRate h ≤ ε * (blockCost q.1 : ℝ≥0∞) := by
  by_cases hh : h = Name.rh
  · subst h
    simp only [hashParent, Option.some.injEq] at hp
    subst p
    rw [sprRate, if_pos rfl, hlen]
    change ε + ε ≤ ε * (blockCost 1306 : ℝ≥0∞)
    have hc : blockCost 1306 = 3 := by norm_num [blockCost, blockBits]
    rw [hc, ← mul_two]
    exact mul_le_mul_of_nonneg_left (by norm_num : (2 : ℝ≥0∞) ≤ 3) zero_le
  · rw [sprRate, if_neg hh]
    exact epsilon_le_query_cost q

theorem spr_charge (c : Cache) (ξ : Rec) (q : Query) (_hq : c q = none) :
    ∑ b : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
      (if Spr (c.cacheQuery q b) ξ then 1 else 0) ≤
        (if Spr c ξ then 1 else 0) + ε * (blockCost q.1 : ℝ≥0∞) := by
  by_cases hs : Spr c ξ
  · rw [if_pos hs]
    calc
      ∑ b : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
          (if Spr (c.cacheQuery q b) ξ then 1 else 0)
          ≤ ∑ _b : BitVec 256,
              (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ * 1 := by
            refine Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left ?_ zero_le
            split_ifs <;> simp
      _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
          ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero)
            (ENNReal.natCast_ne_top _)]
      _ ≤ _ := le_self_add
  · rw [if_neg hs, zero_add]
    have key : ∀ b, Spr (c.cacheQuery q b) ξ →
        ∃ h p, hashParent h = some p ∧ q.1 = p.len ∧ tagNat q = h.idx ∧
          bindingValue h b = bindingValue h (ξ.2 h.fin) := by
      rintro b ⟨h, p, hp, u, hu, htag, b', hb', ht⟩
      by_cases hqq : (⟨p.len, u⟩ : Query) = q
      · subst hqq
        rw [QueryCache.cacheQuery_self] at hb'
        obtain rfl := Option.some.inj hb'
        exact ⟨h, p, hp, rfl, htag, ht⟩
      · rw [QueryCache.cacheQuery_of_ne _ _ hqq] at hb'
        exact (hs ⟨h, p, hp, u, hu, htag, b', hb', ht⟩).elim
    by_cases hex : ∃ h₀ p₀, hashParent h₀ = some p₀ ∧
        q.1 = p₀.len ∧ tagNat q = h₀.idx
    · obtain ⟨h₀, p₀, hp₀, hlen₀, hq₀⟩ := hex
      have key' : ∀ b, Spr (c.cacheQuery q b) ξ →
          bindingValue h₀ b = bindingValue h₀ (ξ.2 h₀.fin) := by
        intro b hb
        obtain ⟨h, p, hp, hlen, hq', ht⟩ := key b hb
        have he : h₀ = h := Name.idx_injective (hq₀.symm.trans hq')
        subst he
        exact ht
      calc
        ∑ b : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
            (if Spr (c.cacheQuery q b) ξ then 1 else 0)
            ≤ ∑ b : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
              (if bindingValue h₀ b = bindingValue h₀ (ξ.2 h₀.fin) then 1 else 0) := by
              refine Finset.sum_le_sum fun b _ =>
                mul_le_mul_of_nonneg_left ?_ zero_le
              split_ifs with h1 h2
              · exact le_rfl
              · exact absurd (key' b h1) h2
              · exact zero_le_one
              · exact le_rfl
        _ = (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
            ((Finset.univ.filter fun b : BitVec 256 =>
              bindingValue h₀ b = bindingValue h₀ (ξ.2 h₀.fin)).card : ℝ≥0∞) := by
              rw [← Finset.mul_sum, Finset.sum_boole]
        _ = sprRate h₀ := by rw [binding_fiber, inv_card_binding]
        _ ≤ _ := sprRate_le_query_cost hp₀ q hlen₀
    · have hno : ∀ b, ¬ Spr (c.cacheQuery q b) ξ := fun b hb => by
        obtain ⟨h, p, hp, hlen, htag, _⟩ := key b hb
        exact hex ⟨h, p, hp, hlen, htag⟩
      rw [Finset.sum_eq_zero fun b _ => by rw [if_neg (hno b), mul_zero]]
      exact zero_le

theorem two_epsilon_eq_half_kappa :
    ε + ε = (((2 : ℝ≥0∞)^127)⁻¹) / 2 := by
  have hstep (n : ℕ) :
      ((2 : ℝ≥0∞)^(n+1))⁻¹ = ((2 : ℝ≥0∞)^n)⁻¹ / 2 := by
    rw [pow_succ, ENNReal.mul_inv
      (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
      (Or.inr two_ne_zero), div_eq_mul_inv]
  calc
    ε + ε = ((2 : ℝ≥0∞)^128)⁻¹ / 2 +
        ((2 : ℝ≥0∞)^128)⁻¹ / 2 := by
      rw [ε, show (129 : ℕ) = 128 + 1 from rfl, hstep]
    _ = ((2 : ℝ≥0∞)^128)⁻¹ := ENNReal.add_halves _
    _ = _ := hstep 127

def authRate : ℝ≥0∞ := (((2 : ℝ≥0∞)^127)⁻¹) / 2

theorem authentication_charge_budget (q : Query) :
    ε + ε * (blockCost q.1 : ℝ≥0∞) ≤
      authRate * (blockCost q.1 : ℝ≥0∞) := by
  calc
    ε + ε * (blockCost q.1 : ℝ≥0∞)
        ≤ ε * (blockCost q.1 : ℝ≥0∞) +
          ε * (blockCost q.1 : ℝ≥0∞) :=
      add_le_add (epsilon_le_query_cost q) le_rfl
    _ = (ε + ε) * (blockCost q.1 : ℝ≥0∞) := (add_mul ..).symm
    _ = _ := by rw [two_epsilon_eq_half_kappa]; rfl

/-! ## Authentication potential and free index queries -/

/-- Uniform mass of one complete key-generation record. -/
def w : ℝ≥0∞ := (Fintype.card Rec : ℝ≥0∞)⁻¹

theorem sum_w : ∑ _ξ : Rec, w = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, w]
  exact ENNReal.mul_inv_cancel
    (by exact_mod_cast Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _)

def sumW (T : Finset Rec) : ℝ≥0∞ := ∑ ξ ∈ T, w

def ind (p : Prop) : ℝ≥0∞ := if p then 1 else 0

def authPotential (T : Finset Rec) (A? : Option (Finset Name))
    (c : Cache) : ℝ≥0∞ :=
  ∑ ξ ∈ T, w *
    (ind (Cache.Hits c (fHid A? ξ)) + ind (Spr c ξ))

theorem avg_sum_comm (T : Finset Rec)
    (f : Rec → BitVec hashBits → ℝ≥0∞) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ ξ ∈ T, w * f ξ u =
      ∑ ξ ∈ T, w *
        ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * f ξ u := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ξ _ =>
    Finset.sum_congr rfl fun u _ => ?_
  ring

theorem avg_const (X : ℝ≥0∞) :
    ∑ _u : BitVec hashBits,
      (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * X = X :=
  WideForest.avg_const X

theorem ind_congr {p r : Prop} (h : p ↔ r) : ind p = ind r := by
  unfold ind
  simp only [h]

theorem hits_avg_eq (T : Finset Rec) (f : Rec → Cache)
    (c : Cache) (q : Query) (hf : ∀ ξ, f ξ q = none) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ ξ ∈ T, w * ind (Cache.Hits (c.cacheQuery q u) (f ξ)) =
      ∑ ξ ∈ T, w * ind (Cache.Hits c (f ξ)) := by
  rw [← avg_const (∑ ξ ∈ T, w * ind (Cache.Hits c (f ξ)))]
  refine Finset.sum_congr rfl fun u _ =>
    congrArg ((Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * ·)
      (Finset.sum_congr rfl fun ξ _ => congrArg (w * ·) (ind_congr ?_))
  simp only [Cache.hits_cacheQuery, hf, Option.isSome_none,
    Bool.false_eq_true, or_false]

theorem spr_avg_eq (T : Finset Rec) (c : Cache) (u₀ : EncInput) :
    ∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
        ∑ ξ ∈ T, w * ind (Spr (c.cacheQuery (encQuery u₀) u) ξ) =
      ∑ ξ ∈ T, w * ind (Spr c ξ) := by
  rw [← avg_const (∑ ξ ∈ T, w * ind (Spr c ξ))]
  refine Finset.sum_congr rfl fun u _ =>
    congrArg ((Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ * ·)
      (Finset.sum_congr rfl fun ξ _ => congrArg (w * ·) (ind_congr ?_))
  exact spr_cacheQuery_enc c ξ u₀ u

theorem authPotential_eq (T : Finset Rec) (A? : Option (Finset Name))
    (c : Cache) :
    authPotential T A? c =
      (∑ ξ ∈ T, w * ind (Cache.Hits c (fHid A? ξ))) +
        ∑ ξ ∈ T, w * ind (Spr c ξ) := by
  simp only [authPotential, mul_add, Finset.sum_add_distrib]

/-- Index queries cannot affect graph authentication: their length differs
from every graph hash input, and hidden keygen caches are empty there. -/
theorem authPotential_index (T : Finset Rec)
    (A? : Option (Finset Name)) (c : Cache) (u₀ : EncInput) :
    (∑ u, (Fintype.card (BitVec hashBits) : ℝ≥0∞)⁻¹ *
      authPotential T A? (c.cacheQuery (encQuery u₀) u)) =
        authPotential T A? c := by
  simp only [authPotential_eq, mul_add, Finset.sum_add_distrib]
  rw [hits_avg_eq _ _ _ _ (fun ξ => fHid_enc A? ξ u₀), spr_avg_eq]

/-! The two record partitions used by the actual security game.  Their
resampling closure and hidden-input charge are the next graph-specific layer. -/

def fiberA (pk : BitVec 128) : Finset Rec :=
  Finset.univ.filter fun ξ => pkOf ξ = pk

abbrev Data := BitVec 128 × List Bool × Cache

def revealed (A : Finset Name) (ξ : Rec) : List Bool :=
  graph.encode (fins A) (graph.evalRec ξ)

def dataOf (A : Finset Name) (ξ : Rec) : Data :=
  (pkOf ξ, revealed A ξ, fExp (some A) ξ)

def fiberB (A : Finset Name) (d : Data) : Finset Rec :=
  Finset.univ.filter fun ξ => dataOf A ξ = d

/-! ## Signing locality

The generic replacement signer only inserts message/nonce index queries.  The
following interface records exactly that fact and shows that such an extension
neither hits a hidden graph point nor changes `Spr`.
-/

def IndexExtension (d d' : Cache) : Prop := Cache.Sub d d' ∧
  ∀ q v, d q = none → d' q = some v → ∃ u : EncInput, q = encQuery u

theorem sub_extend_left (c f : Cache) : Cache.Sub c (Cache.extend c f) :=
  fun _ _ h => Cache.extend_apply_of_some h

theorem indexExtension_kc_none {d d' : Cache} (hd' : IndexExtension d d')
    {ξ : Rec} (hξ : ¬ Cache.Hits d (kc ξ)) {q : Query}
    (hq : (kc ξ q).isSome) : d' q = none := by
  rcases hq' : d' q with _ | v
  · rfl
  · exfalso
    rcases hdq : d q with _ | u
    · obtain ⟨u₀, hqe⟩ := hd'.2 q v hdq hq'
      rw [hqe, kc_enc] at hq
      simp at hq
    · exact hξ ⟨q, hq, by rw [hdq]; rfl⟩

theorem not_hits_fHid_of_indexExtension {d d' : Cache}
    (hd' : IndexExtension d d') {ξ : Rec}
    (hξ : ¬ Cache.Hits d (kc ξ)) (A? : Option (Finset Name)) :
    ¬ Cache.Hits d' (fHid A? ξ) := by
  rintro ⟨q, hq, hq'⟩
  have hkq : (kc ξ q).isSome := by
    obtain ⟨h, p, hp, -, hqp⟩ := (fHid_isSome_iff A? ξ q).1 hq
    exact (kc_isSome_iff ξ q).2 ⟨h, p, hp, hqp⟩
  rw [indexExtension_kc_none hd' hξ hkq] at hq'
  simp at hq'

theorem not_hits_extend_fExp_fHid {d d' : Cache}
    (hd' : IndexExtension d d') {ξ : Rec}
    (hξ : ¬ Cache.Hits d (kc ξ)) (A? : Option (Finset Name)) :
    ¬ Cache.Hits (Cache.extend d' (fExp A? ξ)) (fHid A? ξ) := by
  rw [Cache.hits_extend]
  rintro (h | h)
  · exact not_hits_fHid_of_indexExtension hd' hξ A? h
  · exact (disjoint_fExp_fHid A? ξ).not_hits h

theorem spr_indexExtension_iff {d d' : Cache}
    (hd' : IndexExtension d d') (ξ : Rec) : Spr d' ξ ↔ Spr d ξ := by
  constructor
  · rintro ⟨h, p, hp, u, hu, htag, w', hw, htr⟩
    refine ⟨h, p, hp, u, hu, htag, w', ?_, htr⟩
    rcases hdq : d ⟨p.len, u⟩ with _ | v
    · exfalso
      obtain ⟨u₀, hqe⟩ := hd'.2 _ w' hdq hw
      exact mk_ne_encQuery hp u _ hqe
    · rw [hd'.1 _ _ hdq] at hw
      exact hw
  · exact Spr.mono hd'.1

theorem spr_extend_fExp_iff {d d' : Cache}
    (hd' : IndexExtension d d') (ξ : Rec)
    (A? : Option (Finset Name)) :
    Spr (Cache.extend d' (fExp A? ξ)) ξ ↔ Spr d ξ := by
  constructor
  · intro hs
    rcases spr_of_extend hs with hs | hs
    · exact (spr_indexExtension_iff hd' ξ).1 hs
    · exact absurd hs (not_spr_fExp A? ξ)
  · intro hs
    exact Spr.mono (sub_extend_left d' _)
      ((spr_indexExtension_iff hd' ξ).2 hs)

theorem authPotential_after_sign {d d' : Cache}
    (hd' : IndexExtension d d') (T : Finset Rec)
    (A? : Option (Finset Name))
    (hT : ∀ ξ ∈ T, ¬ Cache.Hits d (kc ξ))
    (fe : Cache) (he : ∀ ξ ∈ T, fExp A? ξ = fe) :
    authPotential T A? (Cache.extend d' fe) =
      ∑ ξ ∈ T, w * ind (Spr d ξ) := by
  unfold authPotential
  apply Finset.sum_congr rfl
  intro ξ hξ
  rw [← he ξ hξ]
  have hh := not_hits_extend_fExp_fHid hd' (hT ξ hξ) A?
  have hs := spr_extend_fExp_iff hd' ξ A?
  simp only [ind, if_neg hh, hs, zero_add]

theorem sign_indexExtension {M' : ℕ} (S : WeightedScheme.Scheme M')
    (x : S.graph.Assignment) (m : Message) (c : Cache)
    (p : Option WeightedScheme.Signature × Cache)
    (hp : p ∈ support (run (S.sign x m) c)) : IndexExtension c p.2 := by
  refine ⟨sub_of_mem_support_run _ c p hp, ?_⟩
  intro q v hc he
  obtain ⟨η, hη⟩ :=
    ReplacementLocality.sign_new_cache_row S x m c p hp q v hc he
  exact ⟨(m, η), hη⟩

theorem authPotential_after_actual_sign {M' : ℕ}
    (S : WeightedScheme.Scheme M') (x : S.graph.Assignment)
    (m : Message) (c : Cache)
    (p : Option WeightedScheme.Signature × Cache)
    (hp : p ∈ support (run (S.sign x m) c))
    (T : Finset Rec) (A? : Option (Finset Name))
    (hT : ∀ ξ ∈ T, ¬ Cache.Hits c (kc ξ))
    (fe : Cache) (he : ∀ ξ ∈ T, fExp A? ξ = fe) :
    authPotential T A? (Cache.extend p.2 fe) =
      ∑ ξ ∈ T, w * ind (Spr c ξ) :=
  authPotential_after_sign (sign_indexExtension S x m c p hp)
    T A? hT fe he

#print axioms spr_charge
#print axioms authentication_charge_budget
#print axioms not_spr_kc
#print axioms authPotential_index
#print axioms authPotential_after_actual_sign

end OptimalOTS.WeightedConstruction.LongChain91
