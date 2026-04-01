import PallLean.LatentWitnessMinorDecomp
import Mathlib.Tactic

/-!
# SelConCoeffReduction

This file pushes on the remaining NP hard core by reducing the diagonal/off-diagonal
Kronecker coefficient equations to coefficient computations on the explicit closed form
for `selCon_rowPoly`.

The point is to eliminate derivative/product-rule complexity from the frontier:
after these reductions, what remains is concrete monomial support bookkeeping.
-/

namespace SelConCoeffReduction

open SPDP MultilinearSPDP NPWitness Compiler TuringMachine MvPolynomial
open LatentCompiler
open LatentWitnessMinorDecomp

/-- Closed form for a selector-list row polynomial inside the latent SPDP space. -/
theorem selCon_rowPoly_eq_closed_form_from_list
    (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n)))
    (hnd : ks.Nodup)
    (hlen : ks.length = Nat.log 2 n) :
    selCon_rowPoly M n ks =
      mlProj
        (C ((-1 : ℚ)^ks.length) *
          (ks.map (Xcon M n)).prod *
          (∏ i ∈ (Finset.univ \ ks.toFinset), selConGadget M n i)) := by
  unfold selCon_rowPoly
  rw [iterDerivList_selSlot_latentCompiled_eq_selCon M n ks (by
    intro hnil
    have : ks.length = 0 := List.length_eq_zero.mp hnil
    omega)]
  rw [iterDeriv_selConSheet_eq M n ks hnd]

/-- Diagonal coefficient law reduces to the explicit closed form. -/
theorem selCon_diag_reduced_goal
    (M : DTM) (n : ℕ)
    (ks : List (Fin (latentBaseVars M n)))
    (hnd : ks.Nodup)
    (hlen : ks.length = Nat.log 2 n) :
    MvPolynomial.coeff (selCon_tagMono M n ks) (selCon_rowPoly M n ks) =
      MvPolynomial.coeff (selCon_tagMono M n ks)
        (mlProj
          (C ((-1 : ℚ)^ks.length) *
            (ks.map (Xcon M n)).prod *
            (∏ i ∈ (Finset.univ \ ks.toFinset), selConGadget M n i))) := by
  rw [selCon_rowPoly_eq_closed_form_from_list M n ks hnd hlen]

/-- Off-diagonal coefficient law reduces to the explicit pair of closed forms. -/
theorem selCon_offdiag_reduced_goal
    (M : DTM) (n : ℕ)
    (ksi ksj : List (Fin (latentBaseVars M n)))
    (hndi : ksi.Nodup) (hndj : ksj.Nodup)
    (hleni : ksi.length = Nat.log 2 n)
    (hlenj : ksj.length = Nat.log 2 n) :
    MvPolynomial.coeff (selCon_tagMono M n ksi) (selCon_rowPoly M n ksj) =
      MvPolynomial.coeff (selCon_tagMono M n ksi)
        (mlProj
          (C ((-1 : ℚ)^ksj.length) *
            (ksj.map (Xcon M n)).prod *
            (∏ i ∈ (Finset.univ \ ksj.toFinset), selConGadget M n i))) := by
  rw [selCon_rowPoly_eq_closed_form_from_list M n ksj hndj hlenj]

/-- The remaining diagonal hard core is now purely a closed-form coefficient statement. -/
def selCon_diag_closed_form_statement (M : DTM) (n : ℕ) : Prop :=
  ∀ ks : List (Fin (latentBaseVars M n)),
    ks.Nodup →
    ks.length = Nat.log 2 n →
    MvPolynomial.coeff (selCon_tagMono M n ks)
      (mlProj
        (C ((-1 : ℚ)^ks.length) *
          (ks.map (Xcon M n)).prod *
          (∏ i ∈ (Finset.univ \ ks.toFinset), selConGadget M n i)))
      = selCon_signOfList ks

/-- The remaining off-diagonal hard core is now purely a closed-form coefficient statement. -/
def selCon_offdiag_closed_form_statement (M : DTM) (n : ℕ) : Prop :=
  ∀ ksi ksj : List (Fin (latentBaseVars M n)),
    ksi.Nodup → ksj.Nodup →
    ksi.length = Nat.log 2 n →
    ksj.length = Nat.log 2 n →
    ksi ≠ ksj →
    MvPolynomial.coeff (selCon_tagMono M n ksi)
      (mlProj
        (C ((-1 : ℚ)^ksj.length) *
          (ksj.map (Xcon M n)).prod *
          (∏ i ∈ (Finset.univ \ ksj.toFinset), selConGadget M n i)))
      = 0

/-- Assembled reduction: the original Kronecker coefficient law follows from the two
closed-form coefficient statements above. -/
theorem selCon_kronecker_coeff_law_logscale_from_closed_forms
    (M : DTM) (n : ℕ) (hn804 : n ≥ 2 ^ 804)
    (idxList : Fin (Nat.choose (latentBaseVars M n) (Nat.log 2 n)) →
      List (Fin (latentBaseVars M n)))
    (hnd : ∀ i, (idxList i).Nodup)
    (hlen : ∀ i, (idxList i).length = Nat.log 2 n)
    (hdiag_cf : selCon_diag_closed_form_statement M n)
    (hoff_cf : selCon_offdiag_closed_form_statement M n) :
    selCon_kronecker_coeff_law_logscale M n hn804 := by
  apply selCon_kronecker_coeff_law_logscale_from_index_lists M n hn804 idxList hnd hlen
  · intro i
    have hred := selCon_diag_reduced_goal M n (idxList i) (hnd i) (hlen i)
    rw [hred]
    exact hdiag_cf (idxList i) (hnd i) (hlen i)
  · intro i j hij
    have hred := selCon_offdiag_reduced_goal M n (idxList i) (idxList j) (hnd i) (hnd j) (hlen i) (hlen j)
    rw [hred]
    exact hoff_cf (idxList i) (idxList j) (hnd i) (hnd j) (hlen i) (hlen j) (by
      intro hEq
      apply hij
      subst hEq
      rfl)

end SelConCoeffReduction
