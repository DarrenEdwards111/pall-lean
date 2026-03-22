/-
  VarsIterDeriv.lean — vars(iterDerivList S V) ⊆ vars(V)
-/
import PallLean.SPDPDefs
import PallLean.ProfileCompression
import Mathlib.Tactic

namespace VarsIterDeriv

open MvPolynomial

theorem vars_iterDerivList_subset {N : ℕ} {F : Type*} [CommRing F]
    (S : List (Fin N)) (V : MvPolynomial (Fin N) F) :
    (SPDP.iterDerivList S V).vars ⊆ V.vars := by
  induction S generalizing V with
  | nil => simp [SPDP.iterDerivList]; exact Finset.Subset.refl _
  | cons i T ih =>
    simp only [SPDP.iterDerivList, List.foldl_cons]
    exact (ih (pderiv i V)).trans (ProfileCompression.vars_pderiv_subset i V)

end VarsIterDeriv
