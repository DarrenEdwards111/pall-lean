import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic
import PallLean.SPDPDefs
/-!
# Tseitin Encoding — Definitions (Pall §8)

Pure data structures and polynomial definitions for Tseitin encoding.
Split from Tseitin.lean to break circular imports with TagMonomial.lean.

Structures: RegularGraph, HighGirthFamily, Clause3, TseitinFormula,
  DisjointPacking
Definitions: tseitinNumVars, literalPoly, clauseGadget, selectorIdx,
  coupledVerifier
-/

namespace Tseitin

open MvPolynomial SPDP

/-! ## Graph Structure -/

structure RegularGraph where
  numVertices : ℕ
  degree : ℕ
  numEdges : ℕ
  vertices_pos : numVertices ≥ 1
  degree_lower : degree ≥ 2
  edges_bound : numEdges ≤ numVertices * degree
  edges_lower : numEdges ≥ numVertices
  degree_bound : degree ≤ 10
  edgeSrc : Fin numEdges → Fin numVertices
  edgeTgt : Fin numEdges → Fin numVertices
  regular : ∀ v : Fin numVertices,
    (Finset.univ.filter (fun e => edgeSrc e = v ∨ edgeTgt e = v)).card = degree

structure HighGirthFamily where
  graph : ℕ → RegularGraph
  degree_const : ∃ d, ∀ n, (graph n).degree = d
  vertices_eq : ∀ n, n ≥ 3 → (graph n).numVertices = n
  girth_log : ∃ C, ∀ n, n ≥ 2 → C * Nat.log 2 n ≤ (graph n).numVertices

/-! ## Tseitin Encoding (§8.2) -/

inductive TseitinVar
  | edge (e : ℕ)
  | auxGadget (c j : ℕ)
  | selector (c : ℕ)
  deriving DecidableEq

structure Clause3 where
  var1 : ℕ
  var2 : ℕ
  var3 : ℕ
  sign1 : Bool
  sign2 : Bool
  sign3 : Bool
  distinct12 : var1 ≠ var2
  distinct13 : var1 ≠ var3
  distinct23 : var2 ≠ var3

structure TseitinFormula where
  graph : RegularGraph
  parityBit : Fin graph.numVertices → Bool
  parity_odd : (Finset.univ.filter (fun v => parityBit v = true)).card % 2 = 1
  clauses : List Clause3
  num_clauses_upper : clauses.length ≤ 10 * graph.numVertices
  num_clauses_lower : clauses.length ≥ graph.numVertices
  clause_vars_bound : ∀ c ∈ clauses,
    c.var1 < graph.numEdges + 3 * clauses.length ∧
    c.var2 < graph.numEdges + 3 * clauses.length ∧
    c.var3 < graph.numEdges + 3 * clauses.length
  bounded_occurrence : ∀ (v : ℕ),
    (clauses.filter (fun c => c.var1 = v ∨ c.var2 = v ∨ c.var3 = v)).length ≤ 10

/-! ## Disjoint Clause Packing (Lemma 8.3) -/

/-- The set of variable indices used by a clause (its 3 body variables) -/
def clauseVarSet (Φ : TseitinFormula) (c : Fin Φ.clauses.length) : Finset ℕ :=
  let cl := Φ.clauses.get c
  {cl.var1, cl.var2, cl.var3}

theorem mem_clauseVarSet (Φ : TseitinFormula) (c : Fin Φ.clauses.length) (v : ℕ) :
    v ∈ clauseVarSet Φ c ↔
    v = (Φ.clauses.get c).var1 ∨ v = (Φ.clauses.get c).var2 ∨ v = (Φ.clauses.get c).var3 := by
  simp [clauseVarSet, Finset.mem_insert, Finset.mem_singleton, or_assoc]

structure DisjointPacking (Φ : TseitinFormula) where
  selected : List (Fin Φ.clauses.length)
  selected_nodup : selected.Nodup
  /-- Body variables of packed clauses are pairwise disjoint.
      This is the key combinatorial property from the greedy packing on
      a bounded-degree, high-girth graph (Lemma 8.3). -/
  vars_disjoint : ∀ (i j : Fin selected.length), i ≠ j →
    Disjoint (clauseVarSet Φ (selected.get i)) (clauseVarSet Φ (selected.get j))
  size_bound : selected.length ≥ Φ.graph.numVertices / 30

/-! ### Greedy Set Packing -/

/-- The set of clauses that conflict with clause c (share a variable) -/
def conflicting (Φ : TseitinFormula) (c : Fin Φ.clauses.length) :
    Finset (Fin Φ.clauses.length) :=
  Finset.univ.filter (fun c' => ¬Disjoint (clauseVarSet Φ c) (clauseVarSet Φ c'))

/-- Bridge: Finset.filter card on Fin indices = List.filter length.
    Both count positions where predicate holds. -/
private theorem fin_filter_card_eq {α : Type*} (l : List α) (p : α → Bool) :
    (Finset.univ.filter (fun i : Fin l.length => p (l.get i) = true)).card =
    (l.filter p).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    -- Use Fin.cons to decompose: Fin (n+1) = {0} ∪ succ(Fin n)
    -- Key: Finset.univ on Fin (n+1) = {0} ∪ image(succ, Fin n)
    have hsplit : (Finset.univ : Finset (Fin (a :: t).length)) =
        {0} ∪ Finset.univ.map ⟨Fin.succ, Fin.succ_injective _⟩ := by
      ext i; simp; exact em (i = 0)
    rw [hsplit, Finset.filter_union, Finset.filter_singleton,
      Finset.filter_map, Finset.card_union_of_disjoint]
    · -- The mapped filter: map succ (filter (pred ∘ succ) univ)
      -- has card = filter (pred ∘ succ) univ = filter on t = ih
      rw [Finset.card_map]
      have hcomp : (Finset.filter ((fun i => p ((a :: t).get i) = true) ∘
          (⟨Fin.succ, Fin.succ_injective _⟩ : Fin t.length ↪ Fin (a :: t).length))
          Finset.univ) = Finset.univ.filter (fun i : Fin t.length =>
          p (t.get i) = true) := by
        ext i; simp [Function.comp]
      rw [hcomp, ih, List.filter_cons]
      split_ifs <;> simp_all <;> omega
    · rw [Finset.disjoint_left]
      intro x hx hx_map
      simp only [Finset.mem_map] at hx_map
      obtain ⟨y, _, hy⟩ := hx_map
      split_ifs at hx with h
      · simp only [Finset.mem_singleton] at hx
        subst hx
        exact absurd hy (by simp [Fin.ext_iff])
      · simp at hx

theorem bounded_occurrence_fin (Φ : TseitinFormula) (v : ℕ) :
    (Finset.univ.filter (fun i : Fin Φ.clauses.length =>
      let c := Φ.clauses.get i
      c.var1 = v ∨ c.var2 = v ∨ c.var3 = v)).card ≤ 10 := by
  -- Convert Prop predicate to Bool for the bridge
  have h := fin_filter_card_eq Φ.clauses
    (fun c => decide (c.var1 = v ∨ c.var2 = v ∨ c.var3 = v))
  -- Show the two filter predicates are the same
  have heq : (Finset.univ.filter (fun i : Fin Φ.clauses.length =>
      let c := Φ.clauses.get i; c.var1 = v ∨ c.var2 = v ∨ c.var3 = v)) =
    (Finset.univ.filter (fun i : Fin Φ.clauses.length =>
      decide ((Φ.clauses.get i).var1 = v ∨ (Φ.clauses.get i).var2 = v ∨
        (Φ.clauses.get i).var3 = v) = true)) := by
    ext i; simp [decide_eq_true_eq]
  rw [heq, h]
  exact Φ.bounded_occurrence v

/-- Each clause conflicts with at most 30 others (including itself).
    Proof: conflicting c ⊆ F₁ ∪ F₂ ∪ F₃ where Fᵢ filters on varᵢ.
    Each |Fᵢ| ≤ 10 by bounded_occurrence_fin. Union bound: ≤ 30. -/
theorem conflicting_card_le (Φ : TseitinFormula) (c : Fin Φ.clauses.length) :
    (conflicting Φ c).card ≤ 30 := by
  set cl := Φ.clauses.get c
  -- Three filters: clause indices sharing var1, var2, var3 with c
  set F1 := Finset.univ.filter (fun c' : Fin Φ.clauses.length =>
    cl.var1 ∈ clauseVarSet Φ c')
  set F2 := Finset.univ.filter (fun c' : Fin Φ.clauses.length =>
    cl.var2 ∈ clauseVarSet Φ c')
  set F3 := Finset.univ.filter (fun c' : Fin Φ.clauses.length =>
    cl.var3 ∈ clauseVarSet Φ c')
  -- Step 1: conflicting c ⊆ F1 ∪ F2 ∪ F3
  have hsub : conflicting Φ c ⊆ F1 ∪ F2 ∪ F3 := by
    intro c' hc'
    simp only [conflicting, Finset.mem_filter, Finset.mem_univ, true_and] at hc'
    rw [Finset.not_disjoint_iff] at hc'
    obtain ⟨v, hv_c, hv_c'⟩ := hc'
    rw [mem_clauseVarSet] at hv_c
    rcases hv_c with rfl | rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv_c'⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv_c'⟩))
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv_c'⟩)
  -- Step 2: Each Fi ⊆ bounded_occurrence_fin filter, so card ≤ 10
  have hF1 : F1.card ≤ 10 := by
    calc F1.card
        ≤ (Finset.univ.filter (fun i : Fin Φ.clauses.length =>
            let c' := Φ.clauses.get i
            c'.var1 = cl.var1 ∨ c'.var2 = cl.var1 ∨ c'.var3 = cl.var1)).card := by
          apply Finset.card_le_card; intro i hi
          have hi' : cl.var1 ∈ clauseVarSet Φ i := Finset.mem_filter.mp hi |>.2
          rw [mem_clauseVarSet] at hi'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rcases hi' with h | h | h <;> simp [h]
      _ ≤ 10 := bounded_occurrence_fin Φ cl.var1
  have hF2 : F2.card ≤ 10 := by
    calc F2.card
        ≤ (Finset.univ.filter (fun i : Fin Φ.clauses.length =>
            let c' := Φ.clauses.get i
            c'.var1 = cl.var2 ∨ c'.var2 = cl.var2 ∨ c'.var3 = cl.var2)).card := by
          apply Finset.card_le_card; intro i hi
          have hi' : cl.var2 ∈ clauseVarSet Φ i := Finset.mem_filter.mp hi |>.2
          rw [mem_clauseVarSet] at hi'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rcases hi' with h | h | h <;> simp [h]
      _ ≤ 10 := bounded_occurrence_fin Φ cl.var2
  have hF3 : F3.card ≤ 10 := by
    calc F3.card
        ≤ (Finset.univ.filter (fun i : Fin Φ.clauses.length =>
            let c' := Φ.clauses.get i
            c'.var1 = cl.var3 ∨ c'.var2 = cl.var3 ∨ c'.var3 = cl.var3)).card := by
          apply Finset.card_le_card; intro i hi
          have hi' : cl.var3 ∈ clauseVarSet Φ i := Finset.mem_filter.mp hi |>.2
          rw [mem_clauseVarSet] at hi'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rcases hi' with h | h | h <;> simp [h]
      _ ≤ 10 := bounded_occurrence_fin Φ cl.var3
  -- Step 3: union bound
  calc (conflicting Φ c).card
      ≤ (F1 ∪ F2 ∪ F3).card := Finset.card_le_card hsub
    _ ≤ (F1 ∪ F2).card + F3.card := Finset.card_union_le _ _
    _ ≤ (F1.card + F2.card) + F3.card := by linarith [Finset.card_union_le F1 F2]
    _ ≤ 10 + 10 + 10 := by linarith
    _ = 30 := by omega

/-- Generic greedy packing on a finite set with bounded conflicts.
    If every element conflicts with ≤ k others, greedy gives ≥ |S|/k elements. -/
theorem greedy_packing_finset {α : Type*} [DecidableEq α] [Fintype α] [LinearOrder α]
    (S : Finset α) (R : α → α → Prop) [DecidableRel R]
    (hrefl : ∀ a, R a a)
    (hsymm : ∀ a b, R a b → R b a)
    (k : ℕ) (hk : k ≥ 1)
    (hbound : ∀ a ∈ S, (S.filter (R a)).card ≤ k) :
    ∃ P : Finset α, P ⊆ S ∧
      (∀ a ∈ P, ∀ b ∈ P, a ≠ b → ¬R a b) ∧
      P.card * k ≥ S.card := by
  -- By strong induction on S.card
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hne : S.Nonempty
    · set c := S.min' hne
      set bad := S.filter (R c)
      have hc_mem : c ∈ S := Finset.min'_mem _ _
      have hc_bad : c ∈ bad := Finset.mem_filter.mpr ⟨hc_mem, hrefl c⟩
      have hbad_card : bad.card ≤ k := hbound c hc_mem
      have hss : S \ bad ⊂ S :=
        Finset.sdiff_ssubset (Finset.filter_subset _ _) ⟨c, hc_bad⟩
      -- Recurse on S \ bad
      have hbound' : ∀ a ∈ S \ bad, ((S \ bad).filter (R a)).card ≤ k := by
        intro a ha
        calc ((S \ bad).filter (R a)).card
            ≤ (S.filter (R a)).card := Finset.card_le_card (Finset.filter_subset_filter _
                Finset.sdiff_subset)
          _ ≤ k := hbound a (Finset.sdiff_subset ha)
      obtain ⟨P, hPsub, hPdisj, hPsize⟩ := ih (S \ bad) hss hbound'
      refine ⟨{c} ∪ P, ?_, ?_, ?_⟩
      · -- {c} ∪ P ⊆ S
        intro x hx
        simp only [Finset.mem_union, Finset.mem_singleton] at hx
        rcases hx with rfl | hx
        · exact hc_mem
        · exact Finset.sdiff_subset (hPsub hx)
      · -- Pairwise non-R
        intro a ha b hb hab
        simp only [Finset.mem_union, Finset.mem_singleton] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd rfl hab
        · -- c vs b∈P: b ∈ S \ bad, so b ∉ bad, so ¬R c b
          intro hRcb
          have hb_sdiff := hPsub hb
          have hb_not_bad := (Finset.mem_sdiff.mp hb_sdiff).2
          exact hb_not_bad (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hb_sdiff).1, hRcb⟩)
        · -- a∈P vs c: symmetric
          intro hRac
          have ha_sdiff := hPsub ha
          have ha_not_bad := (Finset.mem_sdiff.mp ha_sdiff).2
          exact ha_not_bad (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp ha_sdiff).1, hsymm _ _ hRac⟩)
        · exact hPdisj a ha b hb hab
      · -- Size bound: ({c} ∪ P).card * k ≥ S.card
        have hc_notin_P : c ∉ P := by
          intro hc_in
          have hc_sdiff := hPsub hc_in
          exact (Finset.mem_sdiff.mp hc_sdiff).2
            (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hc_sdiff).1, hrefl c⟩)
        rw [Finset.card_union_of_disjoint (by
          rwa [Finset.disjoint_singleton_left]),
          Finset.card_singleton]
        -- (1 + P.card) * k ≥ S.card
        -- P.card * k ≥ (S \ bad).card
        -- S.card = bad.card + (S \ bad).card
        -- bad.card ≤ k
        have hsplit := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (R c) S)
        nlinarith
    · -- Empty S
      refine ⟨∅, Finset.empty_subset _, fun _ h => absurd h (by simp), ?_⟩
      simp [Finset.not_nonempty_iff_eq_empty.mp hne]

/-- Greedy packing existence via bounded-occurrence argument. -/
noncomputable def disjoint_packing_exists (Φ : TseitinFormula) (hn : Φ.graph.numVertices ≥ 100) :
    DisjointPacking Φ := by
  -- Define the conflict relation
  let R : Fin Φ.clauses.length → Fin Φ.clauses.length → Prop :=
    fun a b => ¬Disjoint (clauseVarSet Φ a) (clauseVarSet Φ b)
  have hrefl : ∀ a, R a a := fun a => by
    simp only [R, Finset.not_disjoint_iff]
    exact ⟨(Φ.clauses.get a).var1, Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩
  have hsymm : ∀ a b, R a b → R b a := fun a b h => by
    simp only [R, Finset.not_disjoint_iff] at h ⊢
    obtain ⟨v, hv1, hv2⟩ := h; exact ⟨v, hv2, hv1⟩
  -- Apply generic greedy packing
  have hex := greedy_packing_finset Finset.univ R hrefl hsymm 30
    (by omega) (fun a _ => by
      calc (Finset.univ.filter (R a)).card
          = (conflicting Φ a).card := by rfl
        _ ≤ 30 := conflicting_card_le Φ a)
  choose P hPsub hPdisj hPsize using hex
  exact {
    selected := P.toList
    selected_nodup := Finset.nodup_toList P
    vars_disjoint := by
      intro i j hij
      have hnd := Finset.nodup_toList P
      have hi_mem : P.toList.get i ∈ P := by
        rw [← Finset.mem_toList]; exact List.get_mem P.toList i
      have hj_mem : P.toList.get j ∈ P := by
        rw [← Finset.mem_toList]; exact List.get_mem P.toList j
      have hne : P.toList.get i ≠ P.toList.get j := by
        intro heq; exact hij (hnd.injective_get heq)
      have h := hPdisj _ hi_mem _ hj_mem hne
      exact not_not.mp h
    size_bound := by
      rw [Finset.length_toList]
      have hcard : Finset.univ.card = Φ.clauses.length := Finset.card_fin _
      rw [hcard] at hPsize
      have := Φ.num_clauses_lower
      omega
  }

/-! ## Polynomial Definitions (§8.4) -/

def tseitinNumVars (Φ : TseitinFormula) : ℕ :=
  Φ.graph.numEdges + 3 * Φ.clauses.length + Φ.clauses.length

noncomputable def literalPoly {m : ℕ} (F : Type*) [CommRing F]
    (v : Fin m) (positive : Bool) : MvPolynomial (Fin m) F :=
  if positive then X v else 1 - X v

noncomputable def clauseGadget (F : Type*) [CommRing F]
    (Φ : TseitinFormula) (c : Fin Φ.clauses.length) :
    MvPolynomial (Fin (tseitinNumVars Φ)) F :=
  let cl := Φ.clauses.get c
  have hpos : tseitinNumVars Φ > 0 := by
    unfold tseitinNumVars; have := c.isLt; omega
  let v1 : Fin (tseitinNumVars Φ) := ⟨cl.var1 % tseitinNumVars Φ, Nat.mod_lt _ hpos⟩
  let v2 : Fin (tseitinNumVars Φ) := ⟨cl.var2 % tseitinNumVars Φ, Nat.mod_lt _ hpos⟩
  let v3 : Fin (tseitinNumVars Φ) := ⟨cl.var3 % tseitinNumVars Φ, Nat.mod_lt _ hpos⟩
  (1 - literalPoly F v1 cl.sign1) *
  (1 - literalPoly F v2 cl.sign2) *
  (1 - literalPoly F v3 cl.sign3)

def selectorIdx (Φ : TseitinFormula) (c : Fin Φ.clauses.length) :
    Fin (tseitinNumVars Φ) :=
  ⟨Φ.graph.numEdges + 3 * Φ.clauses.length + c.val,
   by unfold tseitinNumVars; omega⟩

theorem selectorIdx_injective (Φ : TseitinFormula) :
    Function.Injective (selectorIdx Φ) := by
  intro a b h; simp [selectorIdx, Fin.ext_iff] at h; exact Fin.ext (by omega)

noncomputable def coupledVerifier (F : Type*) [CommRing F]
    (Φ : TseitinFormula) :
    MvPolynomial (Fin (tseitinNumVars Φ)) F :=
  (Finset.univ : Finset (Fin Φ.clauses.length)).prod (fun c =>
    1 - X (selectorIdx Φ c) * clauseGadget F Φ c)

/-! ## Clause gadget variable bounds -/

private theorem literalPoly_vars_subset {m : ℕ} (F : Type*) [CommRing F] [Nontrivial F]
    (v : Fin m) (s : Bool) :
    (literalPoly F v s).vars ⊆ {v} := by
  cases s
  · show ((1 : MvPolynomial (Fin m) F) - X v).vars ⊆ {v}
    intro w hw
    have hsub := vars_sub_subset (1 : MvPolynomial (Fin m) F) hw
    rw [vars_one, vars_X, Finset.empty_union] at hsub
    exact hsub
  · show (X v : MvPolynomial (Fin m) F).vars ⊆ {v}
    rw [vars_X]

private theorem one_sub_literalPoly_vars_subset {m : ℕ} (F : Type*) [CommRing F] [Nontrivial F]
    (v : Fin m) (s : Bool) (w : Fin m)
    (hw : w ∈ ((1 : MvPolynomial (Fin m) F) - literalPoly F v s).vars) :
    w ∈ ({v} : Finset (Fin m)) := by
  have hsub : w ∈ (1 : MvPolynomial (Fin m) F).vars ∪ (literalPoly F v s).vars :=
    vars_sub_subset _ hw
  rw [vars_one, Finset.empty_union] at hsub
  exact literalPoly_vars_subset F v s hsub

theorem clauseGadget_vars_subset (F : Type*) [CommRing F] [Nontrivial F]
    (Φ : TseitinFormula) (c : Fin Φ.clauses.length) :
    let cl := Φ.clauses.get c
    let hpos : tseitinNumVars Φ > 0 := by unfold tseitinNumVars; have := c.isLt; omega
    let v1 : Fin (tseitinNumVars Φ) := ⟨cl.var1 % tseitinNumVars Φ, Nat.mod_lt _ hpos⟩
    let v2 : Fin (tseitinNumVars Φ) := ⟨cl.var2 % tseitinNumVars Φ, Nat.mod_lt _ hpos⟩
    let v3 : Fin (tseitinNumVars Φ) := ⟨cl.var3 % tseitinNumVars Φ, Nat.mod_lt _ hpos⟩
    (clauseGadget F Φ c).vars ⊆ {v1, v2, v3} := by
  set cl := Φ.clauses.get c
  have hpos : tseitinNumVars Φ > 0 := by unfold tseitinNumVars; have := c.isLt; omega
  set v1 : Fin (tseitinNumVars Φ) := ⟨cl.var1 % tseitinNumVars Φ, Nat.mod_lt _ hpos⟩
  set v2 : Fin (tseitinNumVars Φ) := ⟨cl.var2 % tseitinNumVars Φ, Nat.mod_lt _ hpos⟩
  set v3 : Fin (tseitinNumVars Φ) := ⟨cl.var3 % tseitinNumVars Φ, Nat.mod_lt _ hpos⟩
  -- clauseGadget is definitionally equal to triple product of (1 - literalPoly).
  -- We prove vars ⊆ {v1,v2,v3} using vars_mul and one_sub_literalPoly_vars_subset.
  -- Use a helper that avoids name clashes with let-bound variables.
  have key : ∀ x ∈ (clauseGadget F Φ c).vars, x ∈ ({v1, v2, v3} : Finset _) := by
    intro x hx
    -- clauseGadget is definitionally (1-lit1)*(1-lit2)*(1-lit3)
    have hx' := MvPolynomial.vars_mul _ _ hx
    rw [Finset.mem_union] at hx'
    rcases hx' with hx_ab | hx_c
    · have hx'' := MvPolynomial.vars_mul _ _ hx_ab
      rw [Finset.mem_union] at hx''
      rcases hx'' with hx_a | hx_b
      · have := one_sub_literalPoly_vars_subset F v1 cl.sign1 x hx_a
        simp only [Finset.mem_singleton] at this; subst this
        exact Finset.mem_insert_self _ _
      · have := one_sub_literalPoly_vars_subset F v2 cl.sign2 x hx_b
        simp only [Finset.mem_singleton] at this; subst this
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _))
    · have := one_sub_literalPoly_vars_subset F v3 cl.sign3 x hx_c
      simp only [Finset.mem_singleton] at this; subst this
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_singleton.mpr rfl))))
  exact key

theorem clauseGadget_vars_bound (F : Type*) [CommRing F] [Nontrivial F]
    (Φ : TseitinFormula) (c : Fin Φ.clauses.length) :
    ∀ v ∈ (clauseGadget F Φ c).vars,
      v.val < Φ.graph.numEdges + 3 * Φ.clauses.length := by
  intro w hw
  have hcl := Φ.clause_vars_bound (Φ.clauses.get c) (List.getElem_mem c.isLt)
  obtain ⟨hcl1, hcl2, hcl3⟩ := hcl
  have hsub := clauseGadget_vars_subset F Φ c hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsub
  rcases hsub with rfl | rfl | rfl
  · show (Φ.clauses.get c).var1 % tseitinNumVars Φ < Φ.graph.numEdges + 3 * Φ.clauses.length
    rw [Nat.mod_eq_of_lt (by unfold tseitinNumVars; omega)]; exact hcl1
  · show (Φ.clauses.get c).var2 % tseitinNumVars Φ < Φ.graph.numEdges + 3 * Φ.clauses.length
    rw [Nat.mod_eq_of_lt (by unfold tseitinNumVars; omega)]; exact hcl2
  · show (Φ.clauses.get c).var3 % tseitinNumVars Φ < Φ.graph.numEdges + 3 * Φ.clauses.length
    rw [Nat.mod_eq_of_lt (by unfold tseitinNumVars; omega)]; exact hcl3

theorem selector_not_in_gadget (F : Type*) [CommRing F] [Nontrivial F]
    (Φ : TseitinFormula) (c c' : Fin Φ.clauses.length) :
    selectorIdx Φ c ∉ (clauseGadget F Φ c').vars := by
  intro hmem
  have hlt := clauseGadget_vars_bound F Φ c' _ hmem
  simp [selectorIdx] at hlt

end Tseitin
