import PallLean.Paper93.Paper283.RouteBMonomialProductSourceWitness
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeKeepFirstMoves
import Mathlib.Tactic

/-!
# The spaced monomial product is not the flat compiled polynomial

The Route B spaced monomial source uses only the variables with indices
`3 * i`.  In particular its coefficient at the second Cook-Levin variable is
zero, while the real flat product-form `compiledPoly` has coefficient `-1`
there.
-/

namespace PallLean.Paper93.Paper283

open MvPolynomial
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open PallLean.Paper93.DeepMath.PathB
open TuringMachine

namespace RouteBMonomialProductNonFlat

attribute [local instance] Classical.dec

private theorem secondVar_not_mem_spacedVarSet
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    satDeciderGaugeSecondVar M n hn2 htb hns ∉
      RouteBMonomialProductSourceWitness.spacedVarSet M n hn2 htb hns := by
  intro hmem
  simp only [RouteBMonomialProductSourceWitness.spacedVarSet,
    Finset.mem_map, Finset.mem_univ, true_and] at hmem
  obtain ⟨i, hi⟩ := hmem
  have hval : 3 * i.val = 1 := by
    have hraw :
        (RouteBMonomialProductSourceWitness.spacedU
          M n hn2 htb hns i).val =
          (satDeciderGaugeSecondVar M n hn2 htb hns).val :=
      congrArg Fin.val hi
    change 3 * i.val = 1 at hraw
    exact hraw
  omega

/-- The source-side spaced monomial has zero linear coefficient at the second
Cook-Levin variable, because its support contains only indices `3 * i`. -/
theorem spacedMonomialProduct_coeff_secondVar
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    MvPolynomial.coeff
        (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 1)
      (RouteBMonomialProductSourceWitness.spacedMonomialProduct
        M n hn2 htb hns) = 0 := by
  unfold RouteBMonomialProductSourceWitness.spacedMonomialProduct
  by_contra hcoeff
  have hsupport :
      Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 1 ∈
        ((RouteBMonomialProductSourceWitness.spacedVarSet M n hn2 htb hns).prod
          fun i => X i : MvPolynomial
            (Fin (flatCookLevinUVSplit M n hn2 htb hns).numU) ℚ).support :=
    MvPolynomial.mem_support_iff.mpr hcoeff
  have hnotvars :
      satDeciderGaugeSecondVar M n hn2 htb hns ∉
        ((RouteBMonomialProductSourceWitness.spacedVarSet M n hn2 htb hns).prod
          fun i => X i : MvPolynomial
            (Fin (flatCookLevinUVSplit M n hn2 htb hns).numU) ℚ).vars := by
    intro hvar
    have hvar' := MvPolynomial.vars_prod
      (s := RouteBMonomialProductSourceWitness.spacedVarSet M n hn2 htb hns)
      (f := fun i => (X i : MvPolynomial
        (Fin (flatCookLevinUVSplit M n hn2 htb hns).numU) ℚ)) hvar
    simp [MvPolynomial.vars_X] at hvar'
    exact secondVar_not_mem_spacedVarSet M n hn2 htb hns hvar'
  have hzero := MvPolynomial.mem_support_notMem_vars_zero hsupport hnotvars
  simp at hzero

/-- After flat embedding, the spaced monomial still has zero coefficient at
the second Cook-Levin variable. -/
theorem embed_spacedMonomialProduct_coeff_secondVar
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    MvPolynomial.coeff
        (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 1)
        (CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns)
          (RouteBMonomialProductSourceWitness.spacedMonomialProduct
            M n hn2 htb hns)) = 0 := by
  unfold CoupledSheetPoly.embed
  have hidx :
      (flatCookLevinUVSplit M n hn2 htb hns).inlU =
        (id :
          Fin (flatCookLevinUVSplit M n hn2 htb hns).numU ->
            Fin (flatCookLevinUVSplit M n hn2 htb hns).total) := by
    funext i
    exact Fin.ext rfl
  rw [hidx]
  simpa using spacedMonomialProduct_coeff_secondVar M n hn2 htb hns

/-- The embedded spaced monomial product is not the flat Cook-Levin compiled
polynomial. -/
theorem embed_spacedMonomialProduct_ne_compiledPoly
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns)
        (RouteBMonomialProductSourceWitness.spacedMonomialProduct
          M n hn2 htb hns) ≠
      compiledPoly (cook_levin_compilation M n hn2 htb hns) := by
  intro h
  have hcoeff := congrArg
    (fun p =>
      MvPolynomial.coeff
        (Finsupp.single (satDeciderGaugeSecondVar M n hn2 htb hns) 1) p) h
  dsimp at hcoeff
  rw [embed_spacedMonomialProduct_coeff_secondVar,
    compiledPoly_coeff_secondVar] at hcoeff
  norm_num at hcoeff

end RouteBMonomialProductNonFlat

end PallLean.Paper93.Paper283
