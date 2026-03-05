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
  vertices_eq : ∀ n, (graph n).numVertices = n
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

/-- Each clause conflicts with at most 29 others (plus itself = 30 total) -/
theorem conflicting_card_le (Φ : TseitinFormula) (c : Fin Φ.clauses.length) :
    (conflicting Φ c).card ≤ 30 := by
  -- Proof sketch: conflicting c ⊆ ⋃_{v ∈ clauseVarSet c} {c' | v ∈ clauseVarSet c'}
  -- |clauseVarSet c| ≤ 3 (it's {var1, var2, var3})
  -- Each variable appears in ≤ 10 clauses (bounded_occurrence)
  -- Union bound: |conflicting c| ≤ 3 × 10 = 30
  sorry

/-- Greedy packing algorithm via well-founded recursion on remaining clause count -/
noncomputable def greedyPack (Φ : TseitinFormula) (remaining : Finset (Fin Φ.clauses.length)) :
    List (Fin Φ.clauses.length) :=
  if h : remaining.Nonempty then
    let c := remaining.min' h
    let bad := remaining.filter (fun c' => ¬Disjoint (clauseVarSet Φ c) (clauseVarSet Φ c'))
    have : (remaining \ bad).card < remaining.card := by
      apply Finset.card_lt_card
      apply Finset.sdiff_ssubset (Finset.filter_subset _ _)
      exact ⟨c, Finset.mem_filter.mpr ⟨Finset.min'_mem _ _, by
        rw [Finset.not_disjoint_iff]
        exact ⟨(Φ.clauses.get c).var1, Finset.mem_insert_self _ _,
               Finset.mem_insert_self _ _⟩⟩⟩
    c :: greedyPack Φ (remaining \ bad)
  else []
termination_by remaining.card

/-- Greedy pack produces nodup list -/
theorem greedyPack_nodup (Φ : TseitinFormula) (remaining : Finset (Fin Φ.clauses.length)) :
    (greedyPack Φ remaining).Nodup := by
  sorry

/-- Greedy pack elements are pairwise var-disjoint -/
theorem greedyPack_disjoint (Φ : TseitinFormula) (remaining : Finset (Fin Φ.clauses.length)) :
    ∀ (i j : Fin (greedyPack Φ remaining).length), i ≠ j →
    Disjoint (clauseVarSet Φ ((greedyPack Φ remaining).get i))
             (clauseVarSet Φ ((greedyPack Φ remaining).get j)) := by
  sorry

/-- Greedy pack has size ≥ |remaining| / 30 -/
theorem greedyPack_size (Φ : TseitinFormula) (remaining : Finset (Fin Φ.clauses.length)) :
    (greedyPack Φ remaining).length ≥ remaining.card / 30 := by
  sorry

noncomputable def disjoint_packing_exists (Φ : TseitinFormula) (hn : Φ.graph.numVertices ≥ 100) :
    DisjointPacking Φ where
  selected := greedyPack Φ Finset.univ
  selected_nodup := greedyPack_nodup Φ Finset.univ
  vars_disjoint := greedyPack_disjoint Φ Finset.univ
  size_bound := by
    calc (greedyPack Φ Finset.univ).length
        ≥ Finset.univ.card / 30 := greedyPack_size Φ Finset.univ
      _ = Φ.clauses.length / 30 := by simp [Finset.card_univ, Fintype.card_fin]
      _ ≥ Φ.graph.numVertices / 30 := Nat.div_le_div_right Φ.num_clauses_lower

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
