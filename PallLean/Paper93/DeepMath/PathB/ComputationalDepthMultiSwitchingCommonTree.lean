import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseAdapter

/-!
# Common decision-tree carrier for multi-switching

The ordinary simultaneous switching API stores one independent canonical tree per gate and unions
their bad events.  A reusable multi-switching lemma instead needs one common query tree whose leaves
carry the residual state of every gate.  This file introduces that missing representation without
assuming a counting theorem.

`CommonTree n α` is a decision tree with an arbitrary leaf payload.  Its monadic `bind` operation
refines every leaf by another query tree.  `commonRefine` uses this operation to combine a list of
Boolean decision trees into one tree whose reached leaf is exactly the list of all their outputs.
-/

namespace PallLean.Paper93.DeepMath.PathB.MultiSwitching

open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting

/-- A query tree with data of type `α` at each leaf. -/
inductive CommonTree (n : ℕ) (α : Type) where
  | leaf : α → CommonTree n α
  | query : Fin n → CommonTree n α → CommonTree n α → CommonTree n α

namespace CommonTree

/-- The payload reached by a complete assignment. -/
def run {n : ℕ} {α : Type} : CommonTree n α → (Fin n → Bool) → α
  | .leaf a, _ => a
  | .query i lo hi, x => if x i then run hi x else run lo x

/-- Maximum number of queries on a root-to-leaf path. -/
def depth {n : ℕ} {α : Type} : CommonTree n α → ℕ
  | .leaf _ => 0
  | .query _ lo hi => max (depth lo) (depth hi) + 1

/-- The single shared branch transcript followed by an assignment. -/
def trace {n : ℕ} {α : Type} : CommonTree n α → (Fin n → Bool) → List Bool
  | .leaf _, _ => []
  | .query i lo hi, x =>
      if x i then true :: trace hi x else false :: trace lo x

/-- Queried coordinates on the branch followed by an assignment. -/
def queryVars {n : ℕ} {α : Type} : CommonTree n α → (Fin n → Bool) → List (Fin n)
  | .leaf _, _ => []
  | .query i lo hi, x =>
      i :: if x i then queryVars hi x else queryVars lo x

/-- Pathwise read-once normalization.  A repeated query already fixed by the current branch is
resolved immediately; a fresh query is retained and recorded in both recursive branch states. -/
def readOnce {n : ℕ} {α : Type} :
    Restriction n → CommonTree n α → CommonTree n α
  | _, .leaf a => .leaf a
  | σ, .query i lo hi =>
      match σ i with
      | some true => readOnce σ hi
      | some false => readOnce σ lo
      | none => .query i (readOnce (fixVar σ i false) lo)
          (readOnce (fixVar σ i true) hi)

/-- Read-once normalization preserves execution on every assignment extending the accumulated
branch restriction. -/
theorem run_readOnce {n : ℕ} {α : Type} (σ : Restriction n) (t : CommonTree n α)
    (x : Fin n → Bool) (hext : Rung4Restriction.Extends σ x) :
    run (readOnce σ t) x = run t x := by
  induction t generalizing σ with
  | leaf a => rfl
  | query i lo hi ihlo ihhi =>
      cases hσ : σ i with
      | none =>
          by_cases hx : x i
          · simp only [readOnce, hσ, run, hx, if_true]
            exact ihhi _ (extends_fixVar hext hx)
          · simp only [readOnce, hσ, run, hx]
            exact ihlo _ (extends_fixVar hext (Bool.eq_false_of_not_eq_true hx))
      | some b =>
          have hxb : x i = b := hext i b hσ
          cases b <;> simp [readOnce, hσ, run, hxb, ihlo, ihhi, hext]

/-- A coordinate already fixed in the accumulated branch state never appears later on the
normalized execution path. -/
theorem not_mem_queryVars_readOnce_of_fixed {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) {j : Fin n} (hj : σ j ≠ none) :
    j ∉ queryVars (readOnce σ t) x := by
  induction t generalizing σ with
  | leaf a => simp [readOnce, queryVars]
  | query i lo hi ihlo ihhi =>
      cases hσ : σ i with
      | some b =>
          cases b <;> simp only [readOnce, hσ]
          · exact ihlo σ hext hj
          · exact ihhi σ hext hj
      | none =>
          have hji : j ≠ i := by
            intro h; subst h; exact hj hσ
          by_cases hx : x i
          · simp only [readOnce, hσ, queryVars, hx, if_true, List.mem_cons]
            refine fun h => h.elim hji ?_
            have hjfix : fixVar σ i true j ≠ none := by
              rw [fixVar, Function.update_of_ne hji]
              exact hj
            exact ihhi (fixVar σ i true) (extends_fixVar hext hx) hjfix
          · simp only [readOnce, hσ, queryVars, hx, Bool.false_eq_true,
              List.mem_cons]
            refine fun h => h.elim hji ?_
            have hjfix : fixVar σ i false j ≠ none := by
              rw [fixVar, Function.update_of_ne hji]
              exact hj
            exact ihlo (fixVar σ i false)
              (extends_fixVar hext (Bool.eq_false_of_not_eq_true hx)) hjfix

/-- Every normalized execution path queries each coordinate at most once. -/
theorem queryVars_readOnce_nodup {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) :
    (queryVars (readOnce σ t) x).Nodup := by
  induction t generalizing σ with
  | leaf a => simp [readOnce, queryVars]
  | query i lo hi ihlo ihhi =>
      cases hσ : σ i with
      | some b =>
          cases b <;> simp only [readOnce, hσ]
          · exact ihlo σ hext
          · exact ihhi σ hext
      | none =>
          by_cases hx : x i
          · simp only [readOnce, hσ, queryVars, hx, if_true, List.nodup_cons]
            exact ⟨not_mem_queryVars_readOnce_of_fixed (fixVar σ i true) hi x
              (extends_fixVar hext hx) (by simp [fixVar]),
              ihhi _ (extends_fixVar hext hx)⟩
          · simp only [readOnce, hσ, queryVars, hx, List.nodup_cons]
            have hext' := extends_fixVar hext (Bool.eq_false_of_not_eq_true hx)
            exact ⟨not_mem_queryVars_readOnce_of_fixed (fixVar σ i false) lo x hext'
              (by simp [fixVar]), ihlo _ hext'⟩

/-- Bit transcripts and queried-coordinate transcripts have identical lengths. -/
theorem trace_length_eq_queryVars_length {n : ℕ} {α : Type}
    (t : CommonTree n α) (x : Fin n → Bool) :
    (trace t x).length = (queryVars t x).length := by
  induction t with
  | leaf a => rfl
  | query i lo hi ihlo ihhi =>
      by_cases hx : x i <;> simp [trace, queryVars, hx, ihlo, ihhi]

/-- A normalized common path has at most one query per ambient coordinate. -/
theorem trace_readOnce_length_le_ambient {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) :
    (trace (readOnce σ t) x).length ≤ n := by
  rw [trace_length_eq_queryVars_length]
  simpa using (queryVars_readOnce_nodup σ t x hext).length_le_card

/-- Every coordinate retained on a normalized path was free in the starting restriction. -/
theorem mem_queryVars_readOnce_freeVars {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) {j : Fin n}
    (hj : j ∈ queryVars (readOnce σ t) x) : j ∈ freeVars σ := by
  rw [mem_freeVars]
  by_contra hnone
  exact not_mem_queryVars_readOnce_of_fixed σ t x hext hnone hj

/-- The normalized shared transcript is bounded by the current live dimension, not the ambient
dimension and not the sum of the independent gate depths. -/
theorem trace_readOnce_length_le_stars {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) :
    (trace (readOnce σ t) x).length ≤ stars σ := by
  rw [trace_length_eq_queryVars_length]
  have hnd := queryVars_readOnce_nodup σ t x hext
  rw [← List.toFinset_card_of_nodup hnd]
  apply Finset.card_le_card
  intro j hj
  exact mem_queryVars_readOnce_freeVars σ t x hext (List.mem_toFinset.mp hj)

/-- Replay a complete branch transcript, rejecting truncated or overlong transcripts. -/
def replay {n : ℕ} {α : Type} : CommonTree n α → List Bool → Option α
  | .leaf a, [] => some a
  | .leaf _, _ :: _ => none
  | .query _ _ _, [] => none
  | .query _ lo hi, b :: bs => if b then replay hi bs else replay lo bs

/-- Every actual transcript fits within the common tree's maximum depth. -/
theorem trace_length_le_depth {n : ℕ} {α : Type} (t : CommonTree n α)
    (x : Fin n → Bool) : (trace t x).length ≤ depth t := by
  induction t with
  | leaf a => simp [trace, depth]
  | query i lo hi ihlo ihhi =>
      by_cases h : x i
      · simp only [trace, h, if_true, List.length_cons, depth]
        exact Nat.succ_le_succ (ihhi.trans (Nat.le_max_right _ _))
      · simp only [trace, h, depth]
        exact Nat.succ_le_succ (ihlo.trans (Nat.le_max_left _ _))

/-- Replaying the transcript generated by an assignment reaches its exact payload. -/
theorem replay_trace {n : ℕ} {α : Type} (t : CommonTree n α)
    (x : Fin n → Bool) : replay t (trace t x) = some (run t x) := by
  induction t with
  | leaf a => rfl
  | query i lo hi ihlo ihhi =>
      by_cases h : x i <;> simp [trace, replay, run, h, ihlo, ihhi]

/-- One shared transcript determines the entire structured leaf payload. -/
theorem run_eq_of_trace_eq {n : ℕ} {α : Type} (t : CommonTree n α)
    {x y : Fin n → Bool} (h : trace t x = trace t y) : run t x = run t y := by
  have hs : some (run t x) = some (run t y) := by
    rw [← replay_trace t x, ← replay_trace t y, h]
  exact Option.some.inj hs

/-- A depth-bounded common-path label.  It contains one shared bit string, not one string per gate. -/
def PathLabel (d : ℕ) := {bs : List Bool // bs.length ≤ d}

/-- A finite representation of a path of length at most `d`: its actual length and a `d`-bit
buffer.  Bits beyond the recorded length are ignored. -/
abbrev FinitePathLabel (d : ℕ) := Fin (d + 1) × (Fin d → Bool)

/-- The exact size of the finite common-path label space. -/
theorem card_finitePathLabel (d : ℕ) :
    Fintype.card (FinitePathLabel d) = (d + 1) * 2 ^ d := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]

/-- Store a bounded variable-length transcript in the finite label space. -/
def PathLabel.toFinite {d : ℕ} (p : PathLabel d) : FinitePathLabel d :=
  (⟨p.1.length, Nat.lt_succ_of_le p.2⟩, fun i => p.1.getD i.1 false)

/-- Length plus the padded bit buffer loses no bounded transcript information. -/
theorem PathLabel.toFinite_injective {d : ℕ} :
    Function.Injective (@PathLabel.toFinite d) := by
  intro p q h
  apply Subtype.ext
  apply List.ext_getElem (congrArg (fun z => z.1.1) h)
  intro i hip hiq
  have hfun : (fun j : Fin d => p.1.getD j.1 false) =
      (fun j : Fin d => q.1.getD j.1 false) := congrArg Prod.snd h
  have hi : i < d := hip.trans_le p.2
  have hbit := congrFun hfun ⟨i, hi⟩
  rw [List.getD_eq_getElem p.1 false hip, List.getD_eq_getElem q.1 false hiq] at hbit
  exact hbit

/-- A finite shared transcript label parameterized by the actual live dimension. -/
def liveFinitePathLabel {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) (x : Fin n → Bool)
    (hext : Rung4Restriction.Extends σ x) : FinitePathLabel (stars σ) :=
  PathLabel.toFinite ⟨trace (readOnce σ t) x,
    trace_readOnce_length_le_stars σ t x hext⟩

/-- Exact size of the live-dimension shared transcript space. -/
theorem card_liveFinitePathLabel {n : ℕ} (σ : Restriction n) :
    Fintype.card (FinitePathLabel (stars σ)) =
      (stars σ + 1) * 2 ^ stars σ :=
  card_finitePathLabel _

/-- Equal live-dimension labels recover the complete normalized leaf payload. -/
theorem run_readOnce_eq_of_liveFinitePathLabel_eq {n : ℕ} {α : Type}
    (σ : Restriction n) (t : CommonTree n α) {x y : Fin n → Bool}
    (hx : Rung4Restriction.Extends σ x) (hy : Rung4Restriction.Extends σ y)
    (hlabel : liveFinitePathLabel σ t x hx = liveFinitePathLabel σ t y hy) :
    run (readOnce σ t) x = run (readOnce σ t) y := by
  apply run_eq_of_trace_eq
  exact congrArg Subtype.val (PathLabel.toFinite_injective hlabel)

/-- Package an assignment's actual branch transcript as a bounded common-path label. -/
def pathLabel {n : ℕ} {α : Type} (t : CommonTree n α) (x : Fin n → Bool) :
    PathLabel (depth t) :=
  ⟨trace t x, trace_length_le_depth t x⟩

/-- The finite common-path label generated by an assignment. -/
def finitePathLabel {n : ℕ} {α : Type} (t : CommonTree n α) (x : Fin n → Bool) :
    FinitePathLabel (depth t) :=
  (pathLabel t x).toFinite

/-- Equality of common-path labels recovers the complete reached payload. -/
theorem run_eq_of_pathLabel_eq {n : ℕ} {α : Type} (t : CommonTree n α)
    {x y : Fin n → Bool} (h : pathLabel t x = pathLabel t y) : run t x = run t y := by
  apply run_eq_of_trace_eq t
  exact congrArg Subtype.val h

/-- The explicitly finite label still determines the complete reached payload. -/
theorem run_eq_of_finitePathLabel_eq {n : ℕ} {α : Type} (t : CommonTree n α)
    {x y : Fin n → Bool} (h : finitePathLabel t x = finitePathLabel t y) :
    run t x = run t y := by
  apply run_eq_of_pathLabel_eq t
  exact PathLabel.toFinite_injective h

/-- Replace every leaf by a further common query tree. -/
def bind {n : ℕ} {α β : Type} : CommonTree n α → (α → CommonTree n β) → CommonTree n β
  | .leaf a, f => f a
  | .query i lo hi, f => .query i (bind lo f) (bind hi f)

@[simp] theorem run_leaf {n : ℕ} {α : Type} (a : α) (x : Fin n → Bool) :
    run (.leaf a : CommonTree n α) x = a := rfl

@[simp] theorem run_query {n : ℕ} {α : Type} (i : Fin n)
    (lo hi : CommonTree n α) (x : Fin n → Bool) :
    run (.query i lo hi) x = if x i then run hi x else run lo x := rfl

/-- Executing a refined tree first reaches an old leaf and then executes its replacement. -/
theorem run_bind {n : ℕ} {α β : Type} (t : CommonTree n α)
    (f : α → CommonTree n β) (x : Fin n → Bool) :
    run (bind t f) x = run (f (run t x)) x := by
  induction t with
  | leaf a => rfl
  | query i lo hi ihlo ihhi =>
      simp only [bind, run]
      by_cases h : x i <;> simp [h, ihlo, ihhi]

/-- Refinement concatenates the transcript of the outer tree with that of the reached
replacement tree.  This is the canonical source of common-family segment boundaries. -/
theorem trace_bind {n : ℕ} {α β : Type} (t : CommonTree n α)
    (f : α → CommonTree n β) (x : Fin n → Bool) :
    trace (bind t f) x = trace t x ++ trace (f (run t x)) x := by
  induction t with
  | leaf a => rfl
  | query i lo hi ihlo ihhi =>
      by_cases h : x i <;> simp [bind, trace, run, h, ihlo, ihhi]

/-- Regard an ordinary Boolean decision tree as a common tree with Boolean leaves. -/
def ofBool {n : ℕ} : BoolDecisionTree n → CommonTree n Bool
  | .leaf b => .leaf b
  | .query i lo hi => .query i (ofBool lo) (ofBool hi)

theorem run_ofBool {n : ℕ} (t : BoolDecisionTree n) (x : Fin n → Bool) :
    run (ofBool t) x = t.eval x := by
  induction t with
  | leaf b => rfl
  | query i lo hi ihlo ihhi =>
      simp only [ofBool, run, BoolDecisionTree.eval]
      by_cases h : x i <;> simp [h, ihlo, ihhi]

/-- Sequential common refinement of a finite family.  The payload order matches the input list. -/
def commonRefine {n : ℕ} : List (BoolDecisionTree n) → CommonTree n (List Bool)
  | [] => .leaf []
  | t :: ts => bind (ofBool t) fun b =>
      bind (commonRefine ts) fun bs => .leaf (b :: bs)

/-- The common tree records every member tree's value at the same assignment. -/
theorem run_commonRefine {n : ℕ} (ts : List (BoolDecisionTree n)) (x : Fin n → Bool) :
    run (commonRefine ts) x = ts.map (fun t => t.eval x) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [commonRefine, run_bind, run_ofBool, run_leaf, List.map_cons]
      rw [ih]

/-- The common refinement transcript is canonically partitioned into the ordered transcript
segments of its member trees. -/
theorem trace_commonRefine {n : ℕ} (ts : List (BoolDecisionTree n))
    (x : Fin n → Bool) :
    trace (commonRefine ts) x =
      (ts.map fun t => trace (ofBool t) x).flatten := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [commonRefine, trace_bind, run_ofBool,
        List.map_cons, List.flatten_cons, trace]
      rw [ih]
      simp

/-- Consequently, common-path length is the sum of its real per-tree segment lengths. -/
theorem trace_commonRefine_length {n : ℕ} (ts : List (BoolDecisionTree n))
    (x : Fin n → Bool) :
    (trace (commonRefine ts) x).length =
      (ts.map fun t => (trace (ofBool t) x).length).sum := by
  rw [trace_commonRefine, List.length_flatten]
  rw [List.map_map]
  simp only [Function.comp_def]

/-- Indexed-family form used by padded bottom-gate enumerations. -/
def commonRefineFin {n G : ℕ} (trees : Fin G → BoolDecisionTree n) :
    CommonTree n (Fin G → Bool) :=
  bind (commonRefine (List.ofFn trees)) fun values =>
    .leaf fun g => values.getD g.1 false

theorem run_commonRefineFin {n G : ℕ} (trees : Fin G → BoolDecisionTree n)
    (x : Fin n → Bool) (g : Fin G) :
    run (commonRefineFin trees) x g = (trees g).eval x := by
  simp only [commonRefineFin, run_bind, run_leaf, run_commonRefine]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

/-- The indexed common refinement has the same path as its underlying ordered list refinement;
the final payload-conversion leaf introduces no queries. -/
theorem trace_commonRefineFin {n G : ℕ} (trees : Fin G → BoolDecisionTree n)
    (x : Fin n → Bool) :
    trace (commonRefineFin trees) x = trace (commonRefine (List.ofFn trees)) x := by
  rw [commonRefineFin, trace_bind]
  simp only [trace, List.append_nil]

/-- Exact indexed-family segment-length formula. -/
theorem trace_commonRefineFin_length {n G : ℕ} (trees : Fin G → BoolDecisionTree n)
    (x : Fin n → Bool) :
    (trace (commonRefineFin trees) x).length =
      ((List.ofFn trees).map fun t => (trace (ofBool t) x).length).sum := by
  rw [trace_commonRefineFin, trace_commonRefine_length]

end CommonTree

open PallLean.Paper93.DeepMath.PathB.Depth3
open PallLean.Paper93.DeepMath.PathB.SwitchingCounting

/-- The exact common refinement of every canonical bottom-gate tree. -/
def canonicalFamilyTree {n G : ℕ} (gates : Fin G → List (Clause n))
    (fuel : ℕ) (σ : Restriction n) : CommonTree n (Fin G → Bool) :=
  CommonTree.commonRefineFin fun g => canonicalDT (gates g) fuel σ

/-- Read-once normalization of the genuine canonical family tree, initialized with its base
restriction. -/
def readOnceCanonicalFamilyTree {n G : ℕ} (gates : Fin G → List (Clause n))
    (fuel : ℕ) (σ : Restriction n) : CommonTree n (Fin G → Bool) :=
  CommonTree.readOnce σ (canonicalFamilyTree gates fuel σ)

/-- One common-tree execution simultaneously returns every canonical gate value. -/
theorem run_canonicalFamilyTree {n G : ℕ} (gates : Fin G → List (Clause n))
    (fuel : ℕ) (σ : Restriction n) (x : Fin n → Bool) (g : Fin G) :
    CommonTree.run (canonicalFamilyTree gates fuel σ) x g =
      (canonicalDT (gates g) fuel σ).eval x :=
  CommonTree.run_commonRefineFin _ x g

/-- With sufficient fuel, the common leaf payload is the vector of genuine DNF values on every
assignment extending the base restriction. -/
theorem run_canonicalFamilyTree_eq_dnf {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ) (σ : Restriction n)
    (x : Fin n → Bool) (hstars : stars σ ≤ fuel) (hext : Rung4Restriction.Extends σ x)
    (g : Fin G) :
    CommonTree.run (canonicalFamilyTree gates fuel σ) x g = dnfEval (gates g) x := by
  rw [run_canonicalFamilyTree]
  exact canonicalDT_eval fuel σ x hstars hext

/-- The normalized family tree still returns every genuine DNF value. -/
theorem run_readOnceCanonicalFamilyTree_eq_dnf {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ) (σ : Restriction n)
    (x : Fin n → Bool) (hstars : stars σ ≤ fuel) (hext : Rung4Restriction.Extends σ x)
    (g : Fin G) :
    CommonTree.run (readOnceCanonicalFamilyTree gates fuel σ) x g =
      dnfEval (gates g) x := by
  rw [readOnceCanonicalFamilyTree, CommonTree.run_readOnce σ _ x hext]
  exact run_canonicalFamilyTree_eq_dnf gates fuel σ x hstars hext g

/-- Every genuine normalized family path is read-once. -/
theorem queryVars_readOnceCanonicalFamilyTree_nodup {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ) (σ : Restriction n)
    (x : Fin n → Bool) (hext : Rung4Restriction.Extends σ x) :
    (CommonTree.queryVars (readOnceCanonicalFamilyTree gates fuel σ) x).Nodup := by
  exact CommonTree.queryVars_readOnce_nodup σ _ x hext

/-- One live-dimension finite label determines all genuine gate values simultaneously. -/
theorem canonicalFamily_values_eq_of_liveFinitePathLabel_eq {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ) (σ : Restriction n)
    {x y : Fin n → Bool} (hx : Rung4Restriction.Extends σ x)
    (hy : Rung4Restriction.Extends σ y)
    (hlabel : CommonTree.liveFinitePathLabel σ (canonicalFamilyTree gates fuel σ) x hx =
      CommonTree.liveFinitePathLabel σ (canonicalFamilyTree gates fuel σ) y hy) :
    ∀ g, CommonTree.run (readOnceCanonicalFamilyTree gates fuel σ) x g =
      CommonTree.run (readOnceCanonicalFamilyTree gates fuel σ) y g := by
  intro g
  exact congrFun (CommonTree.run_readOnce_eq_of_liveFinitePathLabel_eq
    σ (canonicalFamilyTree gates fuel σ) hx hy hlabel) g

/-- A single common-path label determines all canonical outputs in the family simultaneously. -/
theorem canonicalFamily_values_eq_of_pathLabel_eq {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ) (σ : Restriction n)
    {x y : Fin n → Bool}
    (h : CommonTree.pathLabel (canonicalFamilyTree gates fuel σ) x =
      CommonTree.pathLabel (canonicalFamilyTree gates fuel σ) y) :
    ∀ g, (canonicalDT (gates g) fuel σ).eval x =
      (canonicalDT (gates g) fuel σ).eval y := by
  intro g
  rw [← run_canonicalFamilyTree gates fuel σ x g,
    ← run_canonicalFamilyTree gates fuel σ y g]
  exact congrFun (CommonTree.run_eq_of_pathLabel_eq _ h) g

/-- The finite shared label, of cardinality `(d+1)·2^d`, determines the whole canonical family. -/
theorem canonicalFamily_values_eq_of_finitePathLabel_eq {n G : ℕ}
    (gates : Fin G → List (Clause n)) (fuel : ℕ) (σ : Restriction n)
    {x y : Fin n → Bool}
    (h : CommonTree.finitePathLabel (canonicalFamilyTree gates fuel σ) x =
      CommonTree.finitePathLabel (canonicalFamilyTree gates fuel σ) y) :
    ∀ g, (canonicalDT (gates g) fuel σ).eval x =
      (canonicalDT (gates g) fuel σ).eval y := by
  intro g
  rw [← run_canonicalFamilyTree gates fuel σ x g,
    ← run_canonicalFamilyTree gates fuel σ y g]
  exact congrFun (CommonTree.run_eq_of_finitePathLabel_eq _ h) g

end PallLean.Paper93.DeepMath.PathB.MultiSwitching

#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.run_bind
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.run_readOnce
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.queryVars_readOnce_nodup
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.trace_readOnce_length_le_ambient
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.trace_readOnce_length_le_stars
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.run_readOnce_eq_of_liveFinitePathLabel_eq
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.card_liveFinitePathLabel
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.trace_bind
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.run_commonRefine
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.trace_commonRefine
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.run_commonRefineFin
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.trace_commonRefineFin_length
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.replay_trace
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.card_finitePathLabel
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.PathLabel.toFinite_injective
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.run_eq_of_pathLabel_eq
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.CommonTree.run_eq_of_finitePathLabel_eq
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.run_canonicalFamilyTree_eq_dnf
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.run_readOnceCanonicalFamilyTree_eq_dnf
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.queryVars_readOnceCanonicalFamilyTree_nodup
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalFamily_values_eq_of_liveFinitePathLabel_eq
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalFamily_values_eq_of_pathLabel_eq
#print axioms PallLean.Paper93.DeepMath.PathB.MultiSwitching.canonicalFamily_values_eq_of_finitePathLabel_eq
