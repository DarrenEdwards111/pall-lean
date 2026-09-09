import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Field.Rat

/-!
# Two-clause check of the paper's additive-to-coupled extraction step

Paper Definition 6 / Lemma 7 extracts a clause sheet using restrictions,
coordinate selection and block-local affine normalization.  Section 40.6,
Lemma 222, obtains additive separability by summing local gadget polynomials;
Section 40.8, Lemma 224, identifies the verifier component with the product
`Q = product_C (1 - z_C * V_C^2)`.

This check fixes two clause-square values to `1`, retaining their two selector
variables.  The unchanged local factors are then `1 - z_0` and `1 - z_1`.
Their sum has zero mixed partial, while their product has mixed partial `1`.
Every coordinate-wise affine substitution of the additive source still has
zero mixed partial.  Setting an affine slope to zero includes restriction to
a constant; setting both slope and intercept to zero deletes that coordinate.

The result concerns this literal sum of local factors.  It does not rule out
a compiler that already contains the coupled product, a different justified
compiler construction, or every possible God-Move argument.  In particular,
no claim about SAT hardness or the complete SPDP separation follows here.
-/

namespace GodMoveAdditiveExtractionCheck

open MvPolynomial

abbrev SelectorPoly := MvPolynomial (Fin 2) ℚ

noncomputable def localFactor (i : Fin 2) : SelectorPoly :=
  (1 : SelectorPoly) - (X i : SelectorPoly)

noncomputable def additiveSource : SelectorPoly := localFactor 0 + localFactor 1

noncomputable def coupledSheet : SelectorPoly := localFactor 0 * localFactor 1

noncomputable def mixedPartial (p : SelectorPoly) : SelectorPoly :=
  pderiv 1 (pderiv 0 p)

theorem additive_mixedPartial_zero : mixedPartial additiveSource = 0 := by
  simp [mixedPartial, additiveSource, localFactor, map_sub]

theorem coupled_mixedPartial_one : mixedPartial coupledSheet = 1 := by
  simp [mixedPartial, coupledSheet, localFactor, map_sub]

theorem additive_ne_coupled : additiveSource ≠ coupledSheet := by
  intro h
  have hderiv := congrArg mixedPartial h
  rw [additive_mixedPartial_zero, coupled_mixedPartial_one] at hderiv
  exact zero_ne_one hderiv

/-- Independent affine substitutions in the two selector blocks. -/
noncomputable def blockAffine (slope offset : Fin 2 → ℚ) :
    SelectorPoly →ₐ[ℚ] SelectorPoly :=
  aeval (fun i => C (slope i) * X i + C (offset i))

theorem affine_additive_mixedPartial_zero (slope offset : Fin 2 → ℚ) :
    mixedPartial (blockAffine slope offset additiveSource) = 0 := by
  simp [mixedPartial, blockAffine, additiveSource, localFactor, map_sub]

/-- No choice of these block-local affine parameters extracts the product
from the additive source.  The obstruction is already a mixed derivative. -/
theorem affine_additive_ne_coupled (slope offset : Fin 2 → ℚ) :
    blockAffine slope offset additiveSource ≠ coupledSheet := by
  intro h
  have hderiv := congrArg mixedPartial h
  rw [affine_additive_mixedPartial_zero, coupled_mixedPartial_one] at hderiv
  exact zero_ne_one hderiv

end GodMoveAdditiveExtractionCheck

#print axioms GodMoveAdditiveExtractionCheck.additive_mixedPartial_zero
#print axioms GodMoveAdditiveExtractionCheck.coupled_mixedPartial_one
#print axioms GodMoveAdditiveExtractionCheck.affine_additive_ne_coupled
