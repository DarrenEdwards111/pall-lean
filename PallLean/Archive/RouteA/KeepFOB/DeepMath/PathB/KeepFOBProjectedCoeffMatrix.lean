import PallLean.Archive.RouteA.KeepFOB.DeepMath.PathB.SATDeciderGaugeKeepFOB
import PallLean.PiStarConcrete
import PallLean.GodMoveReal
import PallLean.CrossTermVanishing

/-!
# Coefficient matrix for the keep-FOB projected compiled polynomial

This file proves that the first-of-block zero-substitution projection preserves
the CrossTermVanishing coefficient matrix on first-of-block derivative/tag
families.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open SPDP
open MultilinearSPDP
open SymmetricPower
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-- `piZero` preserves the coefficient of any monomial supported only on kept
variables. -/
theorem coeff_piZero_of_monomial_kept {N : ℕ}
    (keep : Fin N → Prop) [DecidablePred keep]
    (α : Fin N →₀ ℕ)
    (hα : ∀ i, ¬ keep i → α i = 0)
    (p : MvPolynomial (Fin N) Rat) :
    coeff α (PiStarConcrete.piZero keep p) = coeff α p := by
  induction p using MvPolynomial.induction_on' with
  | monomial β c =>
      rw [PiStarConcrete.piZero_monomial]
      by_cases hβ : ∀ i, ¬ keep i → β i = 0
      · simp only [if_pos hβ]
      · rw [if_neg hβ, coeff_zero]
        have hβα : β ≠ α := by
          intro h
          apply hβ
          intro i hi
          rw [h]
          exact hα i hi
        rw [coeff_monomial, if_neg hβα]
  | add p q hp hq =>
      rw [map_add (PiStarConcrete.piZero keep), coeff_add, coeff_add, hp, hq]

/-- A first-of-block tag monomial is supported only on `keepFOB` variables. -/
theorem tagMonomial_keepFOB_supported {n : ℕ}
    (S : Finset (Fin n))
    (hS_fob : ∀ v ∈ S, 3 ∣ v.val) :
    ∀ i, ¬ PiStarConcrete.keepFOB i → tagMonomial S i = 0 := by
  intro i hi
  rw [tagMonomial_apply]
  by_cases his : i ∈ S
  · exfalso
    exact hi (PiStarConcrete.fob_subset_keepFOB S hS_fob i his)
  · simp [his]

/-- `piZero keepFOB` preserves coefficients at first-of-block tag monomials. -/
theorem coeff_piZero_keepFOB_tagMonomial {n : ℕ}
    (S : Finset (Fin n))
    (hS_fob : ∀ v ∈ S, 3 ∣ v.val)
    (p : MvPolynomial (Fin n) Rat) :
    coeff (tagMonomial S) (PiStarConcrete.piZero PiStarConcrete.keepFOB p) =
      coeff (tagMonomial S) p :=
  coeff_piZero_of_monomial_kept PiStarConcrete.keepFOB (tagMonomial S)
    (tagMonomial_keepFOB_supported S hS_fob) p

/-- The projected keep-FOB coefficient matrix agrees with the original
CrossTermVanishing matrix on same-size first-of-block subsets. -/
theorem coeff_mlProj_keepFOBProjection_compiled_samesize
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S T : Finset (Fin n))
    (hcardST : S.card = T.card)
    (hS_fob : ∀ v ∈ S, 3 ∣ v.val)
    (hT_fob : ∀ v ∈ T, 3 ∣ v.val) :
    coeff (tagMonomial S)
      (mlProj (iterDerivList T.toList
        (satDeciderGaugeKeepFOBProjection M n hn htb hns
          (compiledPoly (cook_levin_compilation M n hn htb hns))))) =
    (2 : Rat) ^ (S ∩ T).card := by
  have hT_kept : ∀ i ∈ T.toList, PiStarConcrete.keepFOB i :=
    PiStarConcrete.fobList_allKept T hT_fob
  have hderiv :
      iterDerivList T.toList
        (satDeciderGaugeKeepFOBProjection M n hn htb hns
          (compiledPoly (cook_levin_compilation M n hn htb hns))) =
        PiStarConcrete.piZero PiStarConcrete.keepFOB
          (iterDerivList T.toList
            (compiledPoly (cook_levin_compilation M n hn htb hns))) := by
    unfold satDeciderGaugeKeepFOBProjection
    exact PiStarConcrete.iterDerivList_piSubst_allKept
      PiStarConcrete.keepFOB (0 : Fin n → Rat) T.toList hT_kept
      (compiledPoly (cook_levin_compilation M n hn htb hns))
  rw [hderiv, PiStarConcrete.mlProj_piZero_comm]
  rw [coeff_piZero_keepFOB_tagMonomial S hS_fob]
  exact CrossTermVanishing.coeff_mlProj_compiled_samesize
    M n hn htb hns S T hcardST hS_fob hT_fob

end PallLean.Paper93.DeepMath.PathB
