import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Field.Rat

/-!
# Product-accumulator elimination is a nonlinear substitution

An output accumulator variable can represent the product of two clause
factors. Eliminating that variable substitutes the product for it. This is
an explicit, witness-free algebra homomorphism, but it does not intertwine
the original selector derivatives with the derivatives after elimination.

This check uses the paper's factors with their clause-square values fixed
to one. Variable 0 is the accumulator output; variables 1 and 2 are the
selectors. It checks an algebraic obligation that an SPDP rank-transport
argument must address, without claiming that failure to commute alone is
a theorem refuting every possible rank inequality or compiler.
-/

namespace GodMoveAccumulatorEliminationCheck

open MvPolynomial

abbrev Poly := MvPolynomial (Fin 3) ℚ

noncomputable def outputWire : Poly := X 0

noncomputable def productSheet : Poly := (1 - X 1) * (1 - X 2)

noncomputable def eliminateOutput : Poly →ₐ[ℚ] Poly :=
  aeval (fun i => if i = 0 then productSheet else X i)

noncomputable def selectorMixedPartial (p : Poly) : Poly :=
  pderiv 2 (pderiv 1 p)

/-- Elimination recovers the intended product exactly. -/
theorem elimination_recovers_product :
    eliminateOutput outputWire = productSheet := by
  simp [eliminateOutput, outputWire]

/-- The output wire has no selector mixed derivative before elimination. -/
theorem output_mixedPartial_zero :
    selectorMixedPartial outputWire = 0 := by
  simp [selectorMixedPartial, outputWire]

/-- The recovered product has a nonzero selector mixed derivative. -/
theorem eliminated_mixedPartial_one :
    selectorMixedPartial (eliminateOutput outputWire) = 1 := by
  rw [elimination_recovers_product]
  simp [selectorMixedPartial, productSheet, map_sub]

/-- A common derivative-transport identity fails for this actual elimination. -/
theorem elimination_does_not_commute_with_selector_mixedPartial :
    ¬ ∀ p : Poly, selectorMixedPartial (eliminateOutput p) =
      eliminateOutput (selectorMixedPartial p) := by
  intro h
  have hw := h outputWire
  rw [eliminated_mixedPartial_one, output_mixedPartial_zero, map_zero] at hw
  exact one_ne_zero hw

end GodMoveAccumulatorEliminationCheck

#print axioms GodMoveAccumulatorEliminationCheck.elimination_recovers_product
#print axioms GodMoveAccumulatorEliminationCheck.eliminated_mixedPartial_one
#print axioms GodMoveAccumulatorEliminationCheck.elimination_does_not_commute_with_selector_mixedPartial
