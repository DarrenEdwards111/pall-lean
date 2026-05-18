import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedCookLevinAssemblyReduction

/-!
# Rest-factor harmlessness lemmas for Boolean-projected Pi+

This file records the concrete calculus for the non-Boolean Cook--Levin factors
(adjacency and transition skeleton factors) used in the factored Route-C
assembly.  The key point is that every rest factor is a passive constant-one
quadratic edge factor `1 - c XᵢXⱼ`; differentiating it can only expose one of the
two endpoint variables, and higher/rest rows are ordinary SPDP generators of the
rest product.  These lemmas are the rest-side counterpart to the Booleanity
product slice in `PiPlusBooleanProjectedCookLevinAssemblyReduction`.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-- A rest factor whose local constraint has cadjacent form is literally a
constant-one quadratic edge factor. -/
theorem rest_constraint_factor_eq_one_sub_cadj
    {n : Nat} {lc : LocalConstraint n} {c : ℚ} {i j : Fin n}
    (hpoly : lc.poly = MvPolynomial.C c * (MvPolynomial.X i * MvPolynomial.X j)) :
    ((1 : MvPolynomial (Fin n) ℚ) - lc.poly) =
      1 - MvPolynomial.C c * (MvPolynomial.X i * MvPolynomial.X j) := by
  rw [hpoly]

/-- Differentiating a rest edge factor exposes only one of its endpoint
variables.  Away from the two endpoints the derivative is zero. -/
theorem pderiv_rest_constraint_factor_cadj
    {n : Nat} {lc : LocalConstraint n} {c : ℚ} {i j v : Fin n}
    (hij : i ≠ j)
    (hpoly : lc.poly = MvPolynomial.C c * (MvPolynomial.X i * MvPolynomial.X j)) :
    MvPolynomial.pderiv v ((1 : MvPolynomial (Fin n) ℚ) - lc.poly) =
      if v = i then -MvPolynomial.C c * MvPolynomial.X j
      else if v = j then -MvPolynomial.C c * MvPolynomial.X i
      else 0 := by
  rw [hpoly]
  by_cases hvi : v = i
  · subst v
    simp [hij]
  · by_cases hvj : v = j
    · subst v
      simp [hvi]
    · simp [hvi, hvj]

/-- A rest factor has zero second derivative in any variable outside its two
endpoints.  This is the passive-factor form needed when classifying Leibniz
summands: rest derivatives cannot create remote variables. -/
theorem pderiv_rest_constraint_factor_cadj_of_ne_left_right
    {n : Nat} {lc : LocalConstraint n} {c : ℚ} {i j v : Fin n}
    (hvi : v ≠ i) (hvj : v ≠ j)
    (hpoly : lc.poly = MvPolynomial.C c * (MvPolynomial.X i * MvPolynomial.X j)) :
    MvPolynomial.pderiv v ((1 : MvPolynomial (Fin n) ℚ) - lc.poly) = 0 := by
  by_cases hij : i = j
  · subst j
    rw [hpoly]
    simp [hvi]
  · rw [pderiv_rest_constraint_factor_cadj (lc := lc) (c := c) (i := i) (j := j)
      (v := v) hij hpoly]
    simp [hvi, hvj]

/-- Every derivative row of the rest product is, by definition, an inclusive SPDP
row of the rest product itself.  This is the basic rest-side stability fact used
before multiplying back into the full factored product. -/
theorem iterDerivList_restFactorProd_mem_inc
    (M : DTM) (n κ ℓ : Nat) (B : SPDP.BlockPartition n)
    (S : List (Fin n)) (m : MvPolynomial (Fin n) ℚ)
    (hSlen : S.length ≤ κ)
    (hmdeg : m.totalDegree ≤ ℓ)
    (hmvars : m.vars ⊆ S.toFinset)
    (hadm : SPDP.isBlockAdmissible B S) :
    mlProj (m * iterDerivList S (restFactorProd' M n)) ∈
      mlBlockedSpdpSubspaceInc B κ ℓ (restFactorProd' M n) := by
  exact Submodule.subset_span
    ⟨S, m, hSlen, hmdeg, hmvars, hadm, rfl⟩

/-- The full factored Cook--Levin product rows are stable under the enlarged
one-derivative / same-multiplier window.  This is the source-side absorption
lemma used by the row-span classifier: once a Leibniz summand is rewritten as an
ordinary row of `cookLevinFactoredPoly`, it is immediately absorbed by the
`(+1, +0)` inclusive source window. -/
theorem cookLevinFactoredPoly_row_absorb_one_zero
    (M : DTM) (n κ ℓ : Nat) (B : SPDP.BlockPartition n)
    (S : List (Fin n)) (m : MvPolynomial (Fin n) ℚ)
    (hSlen : S.length ≤ κ + 1)
    (hmdeg : m.totalDegree ≤ ℓ)
    (hmvars : m.vars ⊆ S.toFinset)
    (hadm : SPDP.isBlockAdmissible B S) :
    mlProj (m * iterDerivList S (cookLevinFactoredPoly M n)) ∈
      mlBlockedSpdpSubspaceInc B (κ + 1) ℓ (cookLevinFactoredPoly M n) := by
  exact Submodule.subset_span
    ⟨S, m, hSlen, hmdeg, hmvars, hadm, rfl⟩

/-! ## Axiom audit anchors -/

#print axioms rest_constraint_factor_eq_one_sub_cadj
#print axioms pderiv_rest_constraint_factor_cadj
#print axioms pderiv_rest_constraint_factor_cadj_of_ne_left_right
#print axioms iterDerivList_restFactorProd_mem_inc
#print axioms cookLevinFactoredPoly_row_absorb_one_zero

end PallLean.Paper93.DeepMath.PathC
