import PallLean.SPDPDefs
import Mathlib.Tactic
/-!
# R4 PROVED: Constant shift invariance

Using the concrete spdpRank from SPDPDefs.
-/

namespace SPDP.R4

open SPDP MvPolynomial

variable {F : Type*} [CommRing F] {n : ℕ}

/-- iterDerivList is additive -/
theorem iterDerivList_add (indices : List (Fin n)) (p q : MvPolynomial (Fin n) F) :
    iterDerivList indices (p + q) = iterDerivList indices p + iterDerivList indices q := by
  induction indices generalizing p q with
  | nil => simp [iterDerivList]
  | cons i rest ih =>
    simp only [iterDerivList, List.foldl_cons, map_add]
    exact ih _ _

/-- iterDerivList of constant = 0 when list nonempty -/
theorem iterDerivList_C_zero (i : Fin n) (rest : List (Fin n)) (c : F) :
    iterDerivList (i :: rest) (MvPolynomial.C c : MvPolynomial (Fin n) F) = 0 := by
  simp only [iterDerivList, List.foldl_cons, MvPolynomial.pderiv_C]
  exact foldl_pderiv_zero rest

/-- **R4: spdpSubspace(p + C c) = spdpSubspace(p) when κ ≥ 1** -/
theorem spdpSubspace_add_const (κ : ℕ) (hκ : κ ≥ 1) (p : MvPolynomial (Fin n) F) (c : F) :
    spdpSubspace κ (p + MvPolynomial.C c) = spdpSubspace κ p := by
  unfold spdpSubspace; congr 1; ext q; simp only [Set.mem_setOf_eq]
  constructor <;> rintro ⟨indices, hlen, hq⟩
  · refine ⟨indices, hlen, ?_⟩
    rw [hq, iterDerivList_add]
    obtain ⟨i, rest, rfl⟩ : ∃ i rest, indices = i :: rest := by
      cases indices with | nil => simp at hlen; omega | cons i r => exact ⟨i, r, rfl⟩
    rw [iterDerivList_C_zero i rest c, add_zero]
  · refine ⟨indices, hlen, ?_⟩
    rw [hq, iterDerivList_add]
    obtain ⟨i, rest, rfl⟩ : ∃ i rest, indices = i :: rest := by
      cases indices with | nil => simp at hlen; omega | cons i r => exact ⟨i, r, rfl⟩
    rw [iterDerivList_C_zero i rest c, add_zero]

/-- **R4: spdpRank invariant under constant shift when κ ≥ 1** -/
theorem rank_eq_add_const [Nontrivial F] (κ : ℕ) (hκ : κ ≥ 1)
    (p : MvPolynomial (Fin n) F) (c : F) :
    spdpRank κ (p + MvPolynomial.C c) = spdpRank κ p := by
  unfold spdpRank; rw [spdpSubspace_add_const κ hκ p c]

end SPDP.R4
