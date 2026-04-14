/-
  AbstractLocalDerivSpace.lean — Abstract local derivative spaces for symmetric power factorization

  ## Overview

  For each constraint type τ, the "local derivative space" W_τ is the span of
  all possible post-mlProj local derivatives of a factor of that type.

  For booleanity: the factor is 1 - v + v² (for variable v). The possible
  derivatives are:
    - 0 derivatives: 1 - v + v²  →  mlProj gives 1 - v
    - 1 derivative:  -1 + 2v      →  mlProj gives -1 + 2v
    - 2 derivatives: 2             →  mlProj gives 2

  These three elements span a 2-dimensional subspace of Q[v]_multilinear ≅ Q².
  (Since 2 and -1+2v are linearly independent, and 1-v = -(1/2)(-1+2v) + (1/2)·2.)

  ## Formalization

  We work in Q² directly (as Fin 2 → Q), representing multilinear polynomials
  in one variable v as pairs (constant term, coefficient of v).

  The three derivative results become:
    - 1 - v  ↔  (1, -1)
    - -1 + 2v ↔  (-1, 2)
    - 2       ↔  (2, 0)

  We prove these three vectors span all of Q² (dimension 2).

  The instantiation map sends (a, b) to the polynomial a + b*v in Q[z₁,...,zₙ],
  where v = zⱼ for some specific variable index j. This map is linear.
-/
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.StdBasis

namespace AbstractLocalDerivSpace

open Finset

/-! ## Part 1: The abstract booleanity local derivative space in Q² -/

/-- Represent multilinear polynomials in one variable as Q².
    Component 0 = constant term, component 1 = coefficient of the variable.
    So (a, b) represents the polynomial a + b*X. -/
abbrev MLPoly1 := Fin 2 → ℚ

/-- The booleanity factor after mlProj with 0 derivatives: 1 - X ↔ (1, -1). -/
def boolDerivAtom0 : MLPoly1 := ![1, -1]

/-- The booleanity factor after mlProj with 1 derivative: -1 + 2X ↔ (-1, 2). -/
def boolDerivAtom1 : MLPoly1 := ![-1, 2]

/-- The booleanity factor after mlProj with 2 derivatives: 2 ↔ (2, 0). -/
def boolDerivAtom2 : MLPoly1 := ![2, 0]

/-- The set of booleanity derivative atoms. -/
def boolDerivAtoms : Finset MLPoly1 :=
  {boolDerivAtom0, boolDerivAtom1, boolDerivAtom2}

/-- Any element of Q² can be written as a linear combination of
    boolDerivAtom2 = (2,0) and boolDerivAtom1 = (-1,2).

    Explicit formula: x = ((x 0 + x 1 / 2) / 2) • (2,0) + (x 1 / 2) • (-1,2). -/
theorem any_in_span_of_boolAtoms (x : MLPoly1) :
    x ∈ Submodule.span ℚ ({boolDerivAtom2, boolDerivAtom1} : Set MLPoly1) := by
  rw [Submodule.mem_span_pair]
  refine ⟨(x 0 + x 1 / 2) / 2, x 1 / 2, ?_⟩
  ext i
  fin_cases i <;> simp [boolDerivAtom2, boolDerivAtom1] <;> ring

/-- The span of the three booleanity derivative atoms equals the full space Q².

    The atoms {(2,0), (-1,2)} already span Q² (any x can be written as a
    linear combination). Adding (1,-1) does not change the span. -/
theorem boolDerivAtoms_span_eq_top :
    Submodule.span ℚ (↑boolDerivAtoms : Set MLPoly1) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  apply Submodule.span_mono _ (any_in_span_of_boolAtoms x)
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  simp only [boolDerivAtoms, Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hv with rfl | rfl <;> simp

/-- The abstract booleanity local derivative space has dimension exactly 2. -/
theorem boolLocalDerivSpace_finrank :
    Module.finrank ℚ MLPoly1 = 2 := by
  change Module.finrank ℚ (Fin 2 → ℚ) = 2
  simp

/-- The booleanity derivative atoms span a space of dimension ≤ 2.
    (In fact exactly 2, but ≤ 2 is what we need for the bound.) -/
theorem boolDerivAtoms_span_finrank_le :
    Module.finrank ℚ (Submodule.span ℚ (↑boolDerivAtoms : Set MLPoly1)) ≤ 2 := by
  rw [boolDerivAtoms_span_eq_top]
  simp [boolLocalDerivSpace_finrank]

/-! ## Part 2: The instantiation map

    The instantiation map sends an abstract multilinear polynomial (a, b) ∈ Q²
    to the concrete polynomial a + b * z_j ∈ Q[z₁,...,zₙ], where j is a
    specific variable index.

    This map is linear, and it preserves the structure: different instantiations
    (at different variable indices j) produce polynomials in disjoint variable sets. -/

/-- Instantiate an abstract multilinear polynomial at variable index j.
    Sends (a, b) to a + b * X_j in MvPolynomial (Fin n) Q. -/
noncomputable def instantiate {n : ℕ} (j : Fin n) (w : MLPoly1) :
    MvPolynomial (Fin n) ℚ :=
  MvPolynomial.C (w 0) + MvPolynomial.C (w 1) * MvPolynomial.X j

/-- The instantiation map is linear. -/
noncomputable def instantiateLinearMap {n : ℕ} (j : Fin n) :
    MLPoly1 →ₗ[ℚ] MvPolynomial (Fin n) ℚ where
  toFun := instantiate j
  map_add' := by
    intro w₁ w₂
    simp only [instantiate, Pi.add_apply, map_add]
    ring
  map_smul' := by
    intro r w
    simp only [instantiate, Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply,
      MvPolynomial.smul_eq_C_mul]
    ring

/-- instantiateLinearMap computes instantiate. -/
theorem instantiateLinearMap_apply {n : ℕ} (j : Fin n) (w : MLPoly1) :
    instantiateLinearMap j w = instantiate j w := rfl

/-- Instantiation at different variables produces polynomials whose
    variable sets are disjoint (assuming the abstract polynomial is nonzero
    in the linear component). This is used in the product factorization
    to show that products of instantiated atoms factor correctly through mlProj. -/
theorem instantiate_vars_subset {n : ℕ} (j : Fin n) (w : MLPoly1) :
    (instantiate j w).vars ⊆ {j} := by
  intro v hv
  simp only [instantiate] at hv
  -- vars(C(w 0) + C(w 1) * X_j) ⊆ vars(C(w 0)) ∪ vars(C(w 1) * X_j)
  have h_add := MvPolynomial.vars_add_subset (MvPolynomial.C (w 0))
    (MvPolynomial.C (w 1) * MvPolynomial.X j) hv
  rw [Finset.mem_union] at h_add
  rcases h_add with h | h
  · -- v ∈ vars(C(w 0)): but vars of a constant polynomial is empty
    simp [MvPolynomial.vars_C] at h
  · -- v ∈ vars(C(w 1) * X_j) ⊆ vars(C(w 1)) ∪ vars(X_j) ⊆ ∅ ∪ {j} = {j}
    have h_mul := MvPolynomial.vars_mul (MvPolynomial.C (w 1)) (MvPolynomial.X j) h
    rw [Finset.mem_union] at h_mul
    rcases h_mul with h' | h'
    · simp [MvPolynomial.vars_C] at h'
    · rw [MvPolynomial.vars_X, Finset.mem_singleton] at h'
      exact Finset.mem_singleton.mpr h'

end AbstractLocalDerivSpace
