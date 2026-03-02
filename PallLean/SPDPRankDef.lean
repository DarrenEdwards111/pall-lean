import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic
/-!
# Concrete SPDP Rank — R4 Proved
-/

namespace SPDP.Concrete

open MvPolynomial

variable {F : Type*} [CommRing F]
variable {n : ℕ}

/-- Iterated partial derivative along a list of variable indices -/
noncomputable def iterDerivList (indices : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    MvPolynomial (Fin n) F :=
  indices.foldl (fun q i => MvPolynomial.pderiv i q) p

/-- The SPDP subspace -/
noncomputable def spdpSubspace (κ : ℕ) (p : MvPolynomial (Fin n) F) :
    Submodule F (MvPolynomial (Fin n) F) :=
  Submodule.span F
    { q | ∃ (indices : List (Fin n)) (m : MvPolynomial (Fin n) F),
        indices.length = κ ∧ q = m * iterDerivList indices p }

noncomputable def spdpRankConcrete [Nontrivial F] (κ : ℕ) (p : MvPolynomial (Fin n) F) : ℕ :=
  Module.finrank F (spdpSubspace κ p)

/-- foldl of pderiv over any list, applied to 0, gives 0 -/
theorem foldl_pderiv_zero (indices : List (Fin n)) :
    List.foldl (fun (q : MvPolynomial (Fin n) F) i => MvPolynomial.pderiv i q) 0 indices = 0 := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.foldl_cons, map_zero]
    exact ih

/-- iterDerivList is additive -/
theorem iterDerivList_add (indices : List (Fin n)) (p q : MvPolynomial (Fin n) F) :
    iterDerivList indices (p + q) = iterDerivList indices p + iterDerivList indices q := by
  induction indices generalizing p q with
  | nil => simp [iterDerivList]
  | cons i rest ih =>
    simp only [iterDerivList, List.foldl_cons, map_add]
    exact ih _ _

/-- iterDerivList of a constant is zero when list is nonempty -/
theorem iterDerivList_C_zero (i : Fin n) (rest : List (Fin n)) (c : F) :
    iterDerivList (i :: rest) (MvPolynomial.C c : MvPolynomial (Fin n) F) = 0 := by
  simp only [iterDerivList, List.foldl_cons, MvPolynomial.pderiv_C]
  exact foldl_pderiv_zero rest

/-- **R4: spdpSubspace(p + C c) = spdpSubspace(p) when κ ≥ 1** -/
theorem spdpSubspace_add_const (κ : ℕ) (hκ : κ ≥ 1) (p : MvPolynomial (Fin n) F) (c : F) :
    spdpSubspace κ (p + MvPolynomial.C c) = spdpSubspace κ p := by
  unfold spdpSubspace
  congr 1; ext q; simp only [Set.mem_setOf_eq]
  constructor <;> rintro ⟨indices, m, hlen, hq⟩
  · refine ⟨indices, m, hlen, ?_⟩
    rw [hq, iterDerivList_add]
    obtain ⟨i, rest, rfl⟩ : ∃ i rest, indices = i :: rest := by
      cases indices with
      | nil => simp at hlen; omega
      | cons i rest => exact ⟨i, rest, rfl⟩
    rw [iterDerivList_C_zero i rest c, add_zero]
  · refine ⟨indices, m, hlen, ?_⟩
    rw [hq, iterDerivList_add]
    obtain ⟨i, rest, rfl⟩ : ∃ i rest, indices = i :: rest := by
      cases indices with
      | nil => simp at hlen; omega
      | cons i rest => exact ⟨i, rest, rfl⟩
    rw [iterDerivList_C_zero i rest c, add_zero]

/-- **R4 PROVED: rank invariant under constant shift** -/
theorem rank_eq_add_const [Nontrivial F] (κ : ℕ) (hκ : κ ≥ 1)
    (p : MvPolynomial (Fin n) F) (c : F) :
    spdpRankConcrete κ (p + MvPolynomial.C c) = spdpRankConcrete κ p := by
  unfold spdpRankConcrete; rw [spdpSubspace_add_const κ hκ p c]

end SPDP.Concrete
