import PallLean.SelConCoeffReduction
import Mathlib.Tactic

/-!
# SelConClosedCoeffDecomp

Further decomposition of the remaining NP coefficient core.

After `SelConCoeffReduction`, the remaining frontier is to prove diagonal and
off-diagonal coefficients for one explicit closed form. This file splits that
again into two concrete sub-obligations:

1. `mlProj` does not disturb the target coefficient for the tagged monomial;
2. the complementary product of `selConGadget`s contributes no extra copies of the tag.

That leaves only bare monomial-support bookkeeping on the closed form.
-/

namespace SelConClosedCoeffDecomp

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open LatentCompiler
open LatentWitnessMinorDecomp
open SelConCoeffReduction

/-- The bare closed form before `mlProj` is applied. -/
noncomputable def selCon_closedForm (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n))) :
    MvPolynomial (Fin (latentNumVars M n)) ℚ :=
  C ((-1 : ℚ)^ks.length) *
    (ks.map (Xcon M n)).prod *
    (∏ i ∈ (Finset.univ \ ks.toFinset), selConGadget M n i)

/-- Reduction of the diagonal coefficient statement to the raw closed form. -/
axiom selCon_diag_mlProj_preserves_coeff (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n))) :
    MvPolynomial.coeff (selCon_tagMono M n ks)
      (mlProj (selCon_closedForm M n ks)) =
    MvPolynomial.coeff (selCon_tagMono M n ks)
      (selCon_closedForm M n ks)

/-- Reduction of the off-diagonal coefficient statement to the raw closed form. -/
axiom selCon_offdiag_mlProj_preserves_coeff (M : DTM) (n : ℕ)
    (ksi ksj : List (Fin (latentBaseVars M n))) :
    MvPolynomial.coeff (selCon_tagMono M n ksi)
      (mlProj (selCon_closedForm M n ksj)) =
    MvPolynomial.coeff (selCon_tagMono M n ksi)
      (selCon_closedForm M n ksj)

/-- The complementary `selConGadget` product contributes no extra `Xcon`-tag mass on the diagonal.
So the target coefficient is determined entirely by the sign and the explicit `Xcon` product. -/
axiom selCon_diag_complement_support (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n))) :
    MvPolynomial.coeff (selCon_tagMono M n ks)
      (selCon_closedForm M n ks) = selCon_signOfList ks

/-- For distinct selector lists, the target tag does not appear in the other row's closed form. -/
axiom selCon_offdiag_complement_support (M : DTM) (n : ℕ)
    (ksi ksj : List (Fin (latentBaseVars M n))) :
    ksi ≠ ksj →
    MvPolynomial.coeff (selCon_tagMono M n ksi)
      (selCon_closedForm M n ksj) = 0

/-- Assembled diagonal closed-form statement. -/
theorem selCon_diag_closed_form_from_decomp (M : DTM) (n : ℕ) :
    selCon_diag_closed_form_statement M n := by
  intro ks hnd hlen
  -- Goal is coeff tag (mlProj (C(-1)^len * Xcon-prod * complement-prod)) = sign
  -- This equals coeff tag (mlProj (selCon_closedForm)) by definition
  change MvPolynomial.coeff (selCon_tagMono M n ks)
    (mlProj (selCon_closedForm M n ks)) = selCon_signOfList ks
  rw [selCon_diag_mlProj_preserves_coeff M n ks]
  exact selCon_diag_complement_support M n ks

/-- Assembled off-diagonal closed-form statement. -/
theorem selCon_offdiag_closed_form_from_decomp (M : DTM) (n : ℕ) :
    selCon_offdiag_closed_form_statement M n := by
  intro ksi ksj hndi hndj hleni hlenj hneq
  change MvPolynomial.coeff (selCon_tagMono M n ksi)
    (mlProj (selCon_closedForm M n ksj)) = 0
  rw [selCon_offdiag_mlProj_preserves_coeff M n ksi ksj]
  exact selCon_offdiag_complement_support M n ksi ksj hneq

/-- Therefore the original Kronecker coefficient law follows from the finer decomposition. -/
theorem selCon_kronecker_coeff_law_logscale_from_finer_decomp
    (M : DTM) (n : ℕ) (hn804 : n ≥ 2 ^ 804)
    (idxList : Fin (Nat.choose (latentBaseVars M n) (Nat.log 2 n)) →
      List (Fin (latentBaseVars M n)))
    (hnd : ∀ i, (idxList i).Nodup)
    (hlen : ∀ i, (idxList i).length = Nat.log 2 n)
    (hinj : Function.Injective idxList) :
    selCon_kronecker_coeff_law_logscale M n hn804 := by
  exact selCon_kronecker_coeff_law_logscale_from_closed_forms
    M n hn804 idxList hnd hlen hinj
    (selCon_diag_closed_form_from_decomp M n)
    (selCon_offdiag_closed_form_from_decomp M n)

end SelConClosedCoeffDecomp
