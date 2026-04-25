import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeKeepFOB
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeKeepFirstMoves

/-!
# Keep-FOB moves the real Cook-Levin compiled polynomial

This file proves the paper-faithful `keepFOB` projection moves the real
product-form `compiledPoly (cook_levin_compilation ...)`.

The witness is the same second-variable coefficient used for `keepFirst`: in
the original compiled product that coefficient is `-1`, while `keepFOB` kills
the second variable because its flat index is `1`, and `3 ∤ 1`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

private theorem satDeciderGaugeKeepFOBProjection_coeff_secondVar_image
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (p : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) Rat) :
    MvPolynomial.coeff (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 1)
      (satDeciderGaugeKeepFOBProjection M n hn2 htb hns p) = 0 := by
  by_contra hcoeff
  have hmem :
      Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 1 ∈
        (satDeciderGaugeKeepFOBProjection M n hn2 htb hns p).support :=
    MvPolynomial.mem_support_iff.mpr hcoeff
  have hnot_keep :
      ¬ PiStarConcrete.keepFOB
          (satDeciderGaugeSecondVar M n hn2 htb hns) := by
    simp [PiStarConcrete.keepFOB, satDeciderGaugeSecondVar]
  have hnotvars :
      satDeciderGaugeSecondVar M n hn2 htb hns ∉
        (satDeciderGaugeKeepFOBProjection M n hn2 htb hns p).vars := by
    unfold satDeciderGaugeKeepFOBProjection PiStarConcrete.piZero
    exact PiStarConcrete.notMem_vars_piSubst
      PiStarConcrete.keepFOB 0 hnot_keep p
  have hzero := MvPolynomial.mem_support_notMem_vars_zero hmem hnotvars
  simp at hzero

/-- The paper-faithful `keepFOB` projection moves the real product-form
`compiledPoly`. -/
theorem satDeciderGaugeKeepFOBProjection_moves_compiledPoly
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    satDeciderGaugeKeepFOBProjection M n hn2 htb hns
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≠
      compiledPoly (cook_levin_compilation M n hn2 htb hns) := by
  intro hfix
  have hcoeff := congrArg
    (fun p => MvPolynomial.coeff
      (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 1) p) hfix
  dsimp at hcoeff
  rw [satDeciderGaugeKeepFOBProjection_coeff_secondVar_image,
    compiledPoly_coeff_secondVar] at hcoeff
  norm_num at hcoeff

/-- The paper-faithful `keepFOB` projection satisfies the candidate core. -/
theorem satDeciderGaugeKeepFOBProjection_candidateCore
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    SATDeciderGaugeCandidateCore M n hn2 htb hns
      (satDeciderGaugeKeepFOBProjection M n hn2 htb hns) := by
  rw [satDeciderGaugeKeepFOBProjection_candidateCore_iff_moves_compiledPoly]
  exact satDeciderGaugeKeepFOBProjection_moves_compiledPoly M n hn2 htb hns

end PallLean.Paper93.DeepMath.PathB
