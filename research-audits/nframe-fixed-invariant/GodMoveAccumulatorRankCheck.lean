import PallLean.MultilinearSPDP
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Actual SPDP rank increases under nonlinear accumulator elimination

This check uses the repository's `mlBlockedSpdpRank` without altering its
definition.  Its strict derivative convention is `|S| = kappa`; here
`kappa = 2`, `ell = 0`, with a separate block for each of three variables.
Variable 0 is the accumulator output and variables 1,2 are selectors.

The witness-free substitution `X_0 -> (1-X_1)(1-X_2)` recovers the product
of two paper factors with their clause-square values fixed to one.  Before
substitution the output wire has SPDP rank zero.  Afterwards an admissible
second-derivative row is the nonzero constant one, so the rank is positive.
This is a rank inequality counterexample, not merely failure of derivative
commutation.

The result disproves unrestricted rank monotonicity for this nonlinear
elimination on this rank convention and this fixed partition.  It does not
rule out a tailored compiler/transport theorem with additional hypotheses,
nor claim a result for the inclusive derivative convention or every possible
God-Move construction.  No SAT separation is asserted.
-/

namespace GodMoveAccumulatorRankCheck

open MvPolynomial SPDP MultilinearSPDP

abbrev Poly := MvPolynomial (Fin 3) ℚ

def discreteBlocks : BlockPartition 3 where
  numBlocks := 3
  assign := id

noncomputable def outputWire : Poly := X 0

noncomputable def productSheet : Poly := (1 - X 1) * (1 - X 2)

noncomputable def eliminateOutput : Poly →ₐ[ℚ] Poly :=
  aeval (fun i => if i = 0 then productSheet else X i)

theorem elimination_recovers_product : eliminateOutput outputWire = productSheet := by
  simp [eliminateOutput, outputWire]

theorem output_rank_zero : mlBlockedSpdpRank discreteBlocks 2 0 outputWire = 0 := by
  have h := mlBlockedSpdpRank_add_lowDeg ℚ discreteBlocks 2 0 (0 : Poly) outputWire
    (by simp [outputWire])
  simpa [mlBlockedSpdpRank_zero] using h

theorem selector_list_admissible :
    isBlockAdmissible discreteBlocks ([1, 2] : List (Fin 3)) := by
  constructor
  · decide
  · intro b
    fin_cases b <;> simp [discreteBlocks]

theorem product_second_derivative :
    iterDerivList ([1, 2] : List (Fin 3)) productSheet = 1 := by
  simp [iterDerivList, productSheet, map_sub]

theorem one_mem_product_subspace :
    (1 : Poly) ∈ mlBlockedSpdpSubspace discreteBlocks 2 0 productSheet := by
  apply Submodule.subset_span
  refine ⟨[1, 2], (1 : Poly), rfl, by simp, by simp,
    selector_list_admissible, ?_⟩
  rw [product_second_derivative, one_mul]
  symm
  apply mlProj_of_isMultilinear
  intro a ha i
  have ha0 : a = 0 := by simpa [MvPolynomial.coeff_one, eq_comm] using ha
  simp [ha0]

theorem product_rank_pos : 0 < mlBlockedSpdpRank discreteBlocks 2 0 productSheet := by
  unfold mlBlockedSpdpRank
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨⟨1, one_mem_product_subspace⟩, ?_⟩
  intro h
  exact one_ne_zero (congrArg Subtype.val h)

theorem elimination_strictly_increases_rank :
    mlBlockedSpdpRank discreteBlocks 2 0 outputWire <
      mlBlockedSpdpRank discreteBlocks 2 0 (eliminateOutput outputWire) := by
  rw [output_rank_zero, elimination_recovers_product]
  exact product_rank_pos

/-- Nonlinear accumulator elimination is not a rank-monotone map on all
polynomials, even at these fixed parameters and this fixed partition. -/
theorem elimination_not_rank_monotone :
    ¬ ∀ p : Poly,
      mlBlockedSpdpRank discreteBlocks 2 0 (eliminateOutput p) ≤
        mlBlockedSpdpRank discreteBlocks 2 0 p := by
  intro h
  exact (not_le_of_gt elimination_strictly_increases_rank) (h outputWire)

end GodMoveAccumulatorRankCheck

#print axioms GodMoveAccumulatorRankCheck.output_rank_zero
#print axioms GodMoveAccumulatorRankCheck.product_rank_pos
#print axioms GodMoveAccumulatorRankCheck.elimination_strictly_increases_rank
#print axioms GodMoveAccumulatorRankCheck.elimination_not_rank_monotone
