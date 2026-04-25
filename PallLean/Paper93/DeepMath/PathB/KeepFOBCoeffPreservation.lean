import PallLean.PiStarConcrete
import PallLean.CrossTermVanishing
import Mathlib.Tactic

/-!
# Coefficient preservation for the keep-FOB projection

This file isolates coefficient-level consequences of
`PiStarConcrete.piZero PiStarConcrete.keepFOB` at first-of-block tag
monomials.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open MultilinearSPDP
open SymmetricPower
open SPDP
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

namespace KeepFOBCoeffPreservation

/-- Coefficient formula for `piZero`: it keeps exactly the coefficients of
kept-supported monomials and sends all other target coefficients to zero. -/
theorem coeff_piZero
    {N : ℕ} (keep : Fin N → Prop) [DecidablePred keep]
    (α : Fin N →₀ ℕ) (p : MvPolynomial (Fin N) ℚ) :
    MvPolynomial.coeff α (PiStarConcrete.piZero keep p) =
      if ∀ i, ¬ keep i → α i = 0 then MvPolynomial.coeff α p else 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial β c =>
      rw [PiStarConcrete.piZero_monomial]
      by_cases hβ : ∀ i, ¬ keep i → β i = 0
      · rw [if_pos hβ]
        by_cases hα : ∀ i, ¬ keep i → α i = 0
        · rw [if_pos hα]
        · rw [if_neg hα]
          rw [MvPolynomial.coeff_monomial]
          split_ifs with hβα
          · subst hβα
            exact False.elim (hα hβ)
          · rfl
      · rw [if_neg hβ]
        by_cases hα : ∀ i, ¬ keep i → α i = 0
        · rw [if_pos hα]
          rw [MvPolynomial.coeff_zero, MvPolynomial.coeff_monomial]
          split_ifs with hβα
          · subst hβα
            exact False.elim (hβ hα)
          · rfl
        · rw [if_neg hα, MvPolynomial.coeff_zero]
  | add p q hp hq =>
      rw [map_add, MvPolynomial.coeff_add, hp, hq, MvPolynomial.coeff_add]
      by_cases hα : ∀ i, ¬ keep i → α i = 0
      · repeat rw [if_pos hα]
      · repeat rw [if_neg hα]
        simp

/-- A support-level all-kept hypothesis gives the kept-supported predicate
used by `coeff_piZero`. -/
theorem keptSupported_of_support_subset
    {N : ℕ} {keep : Fin N → Prop} {α : Fin N →₀ ℕ}
    (hα : ∀ i ∈ α.support, keep i) :
    ∀ i, ¬ keep i → α i = 0 := by
  intro i hkeep
  by_contra hαi
  exact hkeep (hα i (Finsupp.mem_support_iff.mpr hαi))

/-- `piZero keepFOB` preserves the coefficient of any monomial whose support
is entirely first-of-block. -/
theorem coeff_piZero_keepFOB_of_support
    {N : ℕ} (α : Fin N →₀ ℕ) (p : MvPolynomial (Fin N) ℚ)
    (hα : ∀ i ∈ α.support, PiStarConcrete.keepFOB i) :
    MvPolynomial.coeff α
        (PiStarConcrete.piZero PiStarConcrete.keepFOB p) =
      MvPolynomial.coeff α p := by
  rw [coeff_piZero]
  exact if_pos (keptSupported_of_support_subset hα)

/-- First-of-block sets produce first-of-block tag monomials. -/
theorem tagMonomial_support_keepFOB_of_fob
    {N : ℕ} (T : Finset (Fin N)) (hT : ∀ v ∈ T, 3 ∣ v.val) :
    ∀ i ∈ (tagMonomial T).support, PiStarConcrete.keepFOB i := by
  intro i hi
  have hnonzero : tagMonomial T i ≠ 0 := Finsupp.mem_support_iff.mp hi
  rw [tagMonomial_apply] at hnonzero
  by_cases hiT : i ∈ T
  · simpa [PiStarConcrete.keepFOB] using hT i hiT
  · simp [hiT] at hnonzero

/-- At a first-of-block tag monomial, `piZero keepFOB` preserves coefficients. -/
theorem coeff_tagMonomial_piZero_keepFOB
    {N : ℕ} (T : Finset (Fin N)) (p : MvPolynomial (Fin N) ℚ)
    (hT : ∀ v ∈ T, 3 ∣ v.val) :
    MvPolynomial.coeff (tagMonomial T)
        (PiStarConcrete.piZero PiStarConcrete.keepFOB p) =
      MvPolynomial.coeff (tagMonomial T) p :=
  coeff_piZero_keepFOB_of_support (tagMonomial T) p
    (tagMonomial_support_keepFOB_of_fob T hT)

/-- The same coefficient preservation after multilinear projection, using the
commutation of `mlProj` with `piZero`. -/
theorem coeff_tagMonomial_mlProj_piZero_keepFOB
    {N : ℕ} (T : Finset (Fin N)) (p : MvPolynomial (Fin N) ℚ)
    (hT : ∀ v ∈ T, 3 ∣ v.val) :
    MvPolynomial.coeff (tagMonomial T)
        (mlProj (PiStarConcrete.piZero PiStarConcrete.keepFOB p)) =
      MvPolynomial.coeff (tagMonomial T) (mlProj p) := by
  rw [PiStarConcrete.mlProj_piZero_comm]
  exact coeff_tagMonomial_piZero_keepFOB T (mlProj p) hT

/-- Since tag monomials are multilinear, the projected version also agrees
with the original coefficient. -/
theorem coeff_tagMonomial_mlProj_piZero_keepFOB_eq_coeff
    {N : ℕ} (T : Finset (Fin N)) (p : MvPolynomial (Fin N) ℚ)
    (hT : ∀ v ∈ T, 3 ∣ v.val) :
    MvPolynomial.coeff (tagMonomial T)
        (mlProj (PiStarConcrete.piZero PiStarConcrete.keepFOB p)) =
      MvPolynomial.coeff (tagMonomial T) p := by
  rw [coeff_tagMonomial_mlProj_piZero_keepFOB T p hT]
  exact coeff_mlProj_of_isMultilinear_mono p (tagMonomial T)
    (tagMonomial_isMultilinear T)

/-- CrossTerm coefficient identity with an inserted `piZero keepFOB` before
`mlProj`. -/
theorem coeff_mlProj_piZero_keepFOB_compiled_samesize
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (S T : Finset (Fin n))
    (hcardST : S.card = T.card)
    (hS_fob : ∀ v ∈ S, 3 ∣ v.val)
    (hT_fob : ∀ v ∈ T, 3 ∣ v.val) :
    MvPolynomial.coeff (tagMonomial S)
      (mlProj
        (PiStarConcrete.piZero PiStarConcrete.keepFOB
          (iterDerivList T.toList
            (compiledPoly (cook_levin_compilation M n hn htb hns))))) =
    (2 : ℚ) ^ (S ∩ T).card := by
  rw [coeff_tagMonomial_mlProj_piZero_keepFOB S
    (iterDerivList T.toList
      (compiledPoly (cook_levin_compilation M n hn htb hns))) hS_fob]
  exact CrossTermVanishing.coeff_mlProj_compiled_samesize
    M n hn htb hns S T hcardST hS_fob hT_fob

end KeepFOBCoeffPreservation

end PallLean.Paper93.DeepMath.PathB
