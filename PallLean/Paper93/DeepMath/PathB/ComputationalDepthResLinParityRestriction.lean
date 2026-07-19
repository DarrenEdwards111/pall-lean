import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResLinParityDAG
import Mathlib.Tactic.Ring

/-!
# Restrictions for resolution over parities

A partial assignment substitutes fixed `𝔽₂` values into affine equations.  This file proves the
semantic substitution lemma and the algebra needed by proof restrictions: false constants are
fixed, weakening commutes with restriction, and linear resolution commutes exactly.  Restricted
Boolean axioms are proved tautological; a later proof transformer may delete those source lines or
replace them by their constant tautology.
-/

namespace PallLean.Paper93.DeepMath.PathB.ResLinParity

open Classical BigOperators

/-- A partial Boolean assignment. -/
abbrev Restriction (n : ℕ) := Fin n → Option (ZMod 2)

/-- A total assignment extends a restriction when it agrees on every fixed coordinate. -/
def Extends {n : ℕ} (x : Fin n → ZMod 2) (ρ : Restriction n) : Prop :=
  ∀ i v, ρ i = some v → x i = v

/-- Contribution already fixed by the partial assignment at one coordinate. -/
def assignedContribution {n : ℕ} (ρ : Restriction n) (e : Equation n) (i : Fin n) : ZMod 2 :=
  match ρ i with
  | none => 0
  | some v => e.coeff i * v

/-- Total affine contribution fixed by a restriction. -/
def assignedPart {n : ℕ} (ρ : Restriction n) (e : Equation n) : ZMod 2 :=
  ∑ i, assignedContribution ρ e i

/-- Substitute the assigned coordinates into an equation, retaining the original variable type
with zero coefficients on fixed coordinates. -/
def restrictEq {n : ℕ} (ρ : Restriction n) (e : Equation n) : Equation n where
  coeff i := match ρ i with | none => e.coeff i | some _ => 0
  rhs := e.rhs - assignedPart ρ e

/-- Restrict every disjunct in a proof line. -/
def restrictClause {n : ℕ} (ρ : Restriction n) (C : Clause n) : Clause n :=
  C.image (restrictEq ρ)

/-- The original affine sum splits into fixed and residual contributions. -/
theorem sum_eq_assigned_add_restricted {n : ℕ} (ρ : Restriction n)
    (e : Equation n) (x : Fin n → ZMod 2) (hx : Extends x ρ) :
    ∑ i, e.coeff i * x i = assignedPart ρ e + ∑ i, (restrictEq ρ e).coeff i * x i := by
  unfold assignedPart
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hρ : ρ i with
  | none => simp [assignedPart, assignedContribution, restrictEq, hρ]
  | some v =>
      have hiv := hx i v hρ
      simp [assignedPart, assignedContribution, restrictEq, hρ, hiv]

/-- **Semantic restriction lemma.**  On extending assignments, an equation and its restriction
have exactly the same truth value. -/
theorem satisfiesEq_restrict_iff {n : ℕ} (ρ : Restriction n)
    (e : Equation n) (x : Fin n → ZMod 2) (hx : Extends x ρ) :
    SatisfiesEq x (restrictEq ρ e) ↔ SatisfiesEq x e := by
  rw [SatisfiesEq, SatisfiesEq, sum_eq_assigned_add_restricted ρ e x hx]
  change (∑ i, (restrictEq ρ e).coeff i * x i) = e.rhs - assignedPart ρ e ↔
    assignedPart ρ e + ∑ i, (restrictEq ρ e).coeff i * x i = e.rhs
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    calc
      (∑ i, (restrictEq ρ e).coeff i * x i) =
          (assignedPart ρ e + ∑ i, (restrictEq ρ e).coeff i * x i) -
            assignedPart ρ e := by ring
      _ = e.rhs - assignedPart ρ e := by rw [h]

/-- Clause satisfaction is preserved exactly under restriction on extending assignments. -/
theorem satisfiesClause_restrict_iff {n : ℕ} (ρ : Restriction n)
    (C : Clause n) (x : Fin n → ZMod 2) (hx : Extends x ρ) :
    SatisfiesClause x (restrictClause ρ C) ↔ SatisfiesClause x C := by
  constructor
  · rintro ⟨e', he', hsat⟩
    rw [restrictClause, Finset.mem_image] at he'
    rcases he' with ⟨e, he, rfl⟩
    exact ⟨e, he, (satisfiesEq_restrict_iff ρ e x hx).mp hsat⟩
  · rintro ⟨e, he, hsat⟩
    exact ⟨restrictEq ρ e, Finset.mem_image.mpr ⟨e, he, rfl⟩,
      (satisfiesEq_restrict_iff ρ e x hx).mpr hsat⟩

/-- Fixed contributions are additive. -/
theorem assignedPart_add {n : ℕ} (ρ : Restriction n) (e f : Equation n) :
    assignedPart ρ (e.add f) = assignedPart ρ e + assignedPart ρ f := by
  unfold assignedPart
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hρ : ρ i <;> simp [assignedContribution, Equation.add, hρ, add_mul]

/-- Restriction commutes exactly with addition of affine equations. -/
theorem restrictEq_add {n : ℕ} (ρ : Restriction n) (e f : Equation n) :
    restrictEq ρ (e.add f) = (restrictEq ρ e).add (restrictEq ρ f) := by
  apply Equation.ext
  · intro i
    cases hρ : ρ i <;> simp [restrictEq, Equation.add, hρ]
  · change (e.rhs + f.rhs) - assignedPart ρ (e.add f) =
      (e.rhs - assignedPart ρ e) + (f.rhs - assignedPart ρ f)
    rw [assignedPart_add]
    ring

/-- Contradictory constants are unchanged by restrictions. -/
theorem restrictEq_falseConstant {n : ℕ} (ρ : Restriction n) (b : ZMod 2) :
    restrictEq ρ (falseConstant n b) = falseConstant n b := by
  apply Equation.ext
  · intro i
    cases hρ : ρ i <;> simp [restrictEq, falseConstant, hρ]
  · change b - assignedPart ρ (falseConstant n b) = b
    have hzero : assignedPart ρ (falseConstant n b) = 0 := by
      unfold assignedPart
      apply Finset.sum_eq_zero
      intro i _
      cases hρ : ρ i <;> simp [assignedContribution, falseConstant, hρ]
    rw [hzero, sub_zero]

/-- Restriction commutes with weakening. -/
theorem restrictClause_insert {n : ℕ} (ρ : Restriction n) (e : Equation n) (C : Clause n) :
    restrictClause ρ (insert e C) = insert (restrictEq ρ e) (restrictClause ρ C) := by
  simp [restrictClause]

/-- Restriction commutes with union of proof lines. -/
theorem restrictClause_union {n : ℕ} (ρ : Restriction n) (C D : Clause n) :
    restrictClause ρ (C ∪ D) = restrictClause ρ C ∪ restrictClause ρ D := by
  simp [restrictClause, Finset.image_union]

/-- The complete linear-resolution conclusion commutes exactly with restriction. -/
theorem restrict_linearResolvent {n : ℕ} (ρ : Restriction n)
    (C D : Clause n) (e f : Equation n) :
    restrictClause ρ (insert (e.add f) (C ∪ D)) =
      insert ((restrictEq ρ e).add (restrictEq ρ f))
        (restrictClause ρ C ∪ restrictClause ρ D) := by
  rw [restrictClause_insert, restrictEq_add, restrictClause_union]

/-- Simplification's false equation remains the same false equation after restriction. -/
theorem restrict_simplification_source {n : ℕ} (ρ : Restriction n)
    (C : Clause n) (b : ZMod 2) :
    restrictClause ρ (insert (falseConstant n b) C) =
      insert (falseConstant n b) (restrictClause ρ C) := by
  rw [restrictClause_insert, restrictEq_falseConstant]

/-- Restricted Boolean sources remain tautologies.  Syntactically they need not remain the literal
Boolean axiom when the variable is fixed; this theorem is the exact cleanup obligation for a full
restricted-dag transformer. -/
theorem restricted_booleanAxiom_valid {n : ℕ} (ρ : Restriction n)
    (x : Fin n → ZMod 2) (hx : Extends x ρ) (i : Fin n) :
    SatisfiesClause x (restrictClause ρ (booleanAxiom n i)) :=
  (satisfiesClause_restrict_iff ρ (booleanAxiom n i) x hx).mpr (booleanAxiom_valid x i)

#print axioms satisfiesEq_restrict_iff
#print axioms satisfiesClause_restrict_iff
#print axioms restrictEq_add
#print axioms restrict_linearResolvent

end PallLean.Paper93.DeepMath.PathB.ResLinParity
