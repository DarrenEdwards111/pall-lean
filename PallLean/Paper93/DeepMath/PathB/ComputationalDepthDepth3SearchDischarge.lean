import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DTRefutationBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingHastad

/-!
# Semantic discharge of the Search labelling

The relabelling bridge (`boolDT_to_ldderiv_of_valid`) reduces "a refuting decision tree yields a
resolution refutation" to the `ValidSearch` predicate: at every reachable leaf with accumulated
false-literal set `F`, the labelled clause `lab F` is an axiom *falsified by the path* (`lab F ⊆ F`).
This file discharges that **semantic** obligation.

## The literal model

We fix the concrete resolution-literal model the switching machinery induces: a literal is a pair
`(i, b) : Fin n × Bool` ("variable `i` takes value `b`"), with complement flipping the bit.  A
`Rung4Literal` maps in by `resLit` (`pos i ↦ (i,true)`, `neg i ↦ (i,false)`), and `falseSet σ` is
the set of literals *forced false* by a partial restriction `σ`.

## The kernel (general)

`resClause_subset_falseSet` is the heart: **a clause every literal of which is `σ`-false has its
resolution image `⊆ falseSet σ`.**  This is exactly `lab F ⊆ F` with `F = falseSet σ` and
`lab = resClause (violated axiom)` — the path-falsifies-the-axiom half of `ValidSearch`, proved
generally from `litFalse`.

## A genuine end-to-end instance (non-vacuity)

The bridge's `∀ F` form was over-strong (it demanded `∅` be an axiom); `ValidSearch` is the
satisfiable form.  To show the whole chain is *non-vacuous* — that a real unsatisfiable axiom set
does discharge `ValidSearch` and produce an actual `∅`-containing resolution refutation — we work the
smallest genuinely unsatisfiable CNF, the two unit clauses `{x}` and `{¬x}` over one variable
(`egAxiom`).  Its one-query Search tree (`egTree`) satisfies `ValidSearch` (`eg_validSearch`), and
`eg_refutation` extracts a valid `LDeriv` over those axioms that contains the empty clause —
`resolvent` of `{x}` and `{¬x}` on the pivot is literally `∅`.

## Honest scope

What remains to connect this kernel to the *canonical* tree of the switching argument is the
**threading coupling**: that the relabelling's accumulated `F` along `canonicalDT`'s path equals
`falseSet σ` for that path's restriction `σ`, and that each leaf of the (tautological-DNF) canonical
tree exposes a satisfied term whose De Morgan–dual clause is the violated axiom.  That coupling is
bookkeeping over the shared tree structure; the *semantic* fact it rests on is exactly
`resClause_subset_falseSet`, discharged here, and the end-to-end instance shows the discharge is
real, not vacuous.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SearchDischarge

variable {n : ℕ}

/-- A resolution literal: variable `i` takes value `b`. -/
abbrev RLit (n : ℕ) := Fin n × Bool

/-- Literal complement: flip the bit. -/
def rcompl : RLit n → RLit n := fun p => (p.1, !p.2)

/-- The positive literal of a variable ("`i` is true"). -/
def rpos (i : Fin n) : RLit n := (i, true)

/-- Embed a `Rung4Literal` into the resolution-literal model. -/
def resLit : Rung4Literal n → RLit n
  | .pos i => (i, true)
  | .neg i => (i, false)

/-- The set of resolution literals forced *false* by a partial restriction `σ`: `(i,b)` is false
when `σ i = some (!b)`. -/
def falseSet (σ : Fin n → Option Bool) : Finset (RLit n) :=
  Finset.univ.filter (fun p => σ p.1 = some (!p.2))

theorem mem_falseSet {σ : Fin n → Option Bool} {p : RLit n} :
    p ∈ falseSet σ ↔ σ p.1 = some (!p.2) := by
  simp [falseSet]

/-- **A `σ`-false literal maps into the false-set.**  Connects `litFalse` (the switching notion)
to membership in `falseSet`. -/
theorem resLit_mem_falseSet {σ : Fin n → Option Bool} {ℓ : Rung4Literal n}
    (h : SwitchingCounting.litFalse σ ℓ = true) : resLit ℓ ∈ falseSet σ := by
  cases ℓ with
  | pos i =>
    rw [mem_falseSet]
    simp only [resLit]
    -- litFalse (pos i): litFixedVal = σ i, = some false
    cases hσ : σ i with
    | none => simp [SwitchingCounting.litFalse, Depth3.litFixedVal, hσ] at h
    | some b => cases b with
      | false => simp [hσ]
      | true => simp [SwitchingCounting.litFalse, Depth3.litFixedVal, hσ] at h
  | neg i =>
    rw [mem_falseSet]
    simp only [resLit]
    -- litFalse (neg i): litFixedVal = (σ i).map not, = some false  ⟺  σ i = some true
    cases hσ : σ i with
    | none => simp [SwitchingCounting.litFalse, Depth3.litFixedVal, hσ] at h
    | some b => cases b with
      | true => simp [hσ]
      | false => simp [SwitchingCounting.litFalse, Depth3.litFixedVal, hσ] at h

/-- The resolution clause of a list of `Rung4Literal`s. -/
def resClause (C : List (Rung4Literal n)) : ResolutionClause (RLit n) := (C.map resLit).toFinset

/-- **The semantic kernel.**  If every literal of a clause `C` is forced false by `σ` (i.e. `C` is
falsified by the path), then its resolution image is `⊆ falseSet σ`.  This is precisely the
`lab F ⊆ F` half of `ValidSearch` for `F = falseSet σ`. -/
theorem resClause_subset_falseSet {σ : Fin n → Option Bool} {C : List (Rung4Literal n)}
    (h : ∀ ℓ ∈ C, SwitchingCounting.litFalse σ ℓ = true) : resClause C ⊆ falseSet σ := by
  intro p hp
  simp only [resClause, List.mem_toFinset, List.mem_map] at hp
  obtain ⟨ℓ, hℓ, rfl⟩ := hp
  exact resLit_mem_falseSet (h ℓ hℓ)

/-! ### A genuine end-to-end instance: `{x} ∧ {¬x}` over one variable -/

/-- The two unit clauses `{x}` and `{¬x}` — an unsatisfiable axiom set over one variable. -/
def egAxiom : ResolutionClause (RLit 1) → Prop :=
  fun C => C = {((0 : Fin 1), true)} ∨ C = {((0 : Fin 1), false)}

/-- Identity labelling: the false-set at a leaf *is* the violated unit clause. -/
def egLab : ResolutionClause (RLit 1) → ResolutionClause (RLit 1) := id

/-- The one-query Search tree: branch on the variable; each leaf's path violates a unit clause. -/
def egTree : BoolDecisionTree 1 := .query (0 : Fin 1) (.leaf false) (.leaf false)

/-- The Search tree solves the axiom Search problem: descending to `x = false` violates `{x}`,
descending to `x = true` violates `{¬x}`. -/
theorem eg_validSearch : ValidSearch rpos rcompl egLab egAxiom ∅ egTree := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact Or.inl (by decide)
  · decide
  · exact Or.inr (by decide)
  · decide

/-- **The discharge, end-to-end.**  The Search tree maps to a *valid* `LDeriv` over the unit-clause
axioms that *contains the empty clause* — a genuine resolution refutation, demonstrating the
labelling discharge is non-vacuous. -/
theorem eg_refutation :
    LDeriv rcompl egAxiom (DTRef.toList rcompl (relabel rpos rcompl egLab ∅ egTree)) ∧
      (∅ : ResolutionClause (RLit 1)) ∈
        DTRef.toList rcompl (relabel rpos rcompl egLab ∅ egTree) := by
  have h := boolDT_to_ldderiv_of_valid rpos rcompl egLab egTree eg_validSearch
  exact ⟨h.1, h.2.1⟩

end SearchDischarge

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SearchDischarge.resClause_subset_falseSet
#print axioms PallLean.Paper93.DeepMath.PathB.SearchDischarge.eg_refutation
