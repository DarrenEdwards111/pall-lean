import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.PDeriv
import PallLean.SPDPDefs

/-!
# Iterated Leibniz for iterDerivList
-/

open MvPolynomial SPDP

namespace IterLeibniz

variable {n : ℕ} {F : Type*} [CommRing F]

/-- iterDerivList is additive. -/
theorem iterDerivList_add (S : List (Fin n)) (p q : MvPolynomial (Fin n) F) :
    iterDerivList S (p + q) = iterDerivList S p + iterDerivList S q := by
  induction S generalizing p q with
  | nil => rfl
  | cons i rest ih =>
    simp only [iterDerivList, List.foldl_cons]
    rw [map_add (pderiv i)]; exact ih _ _

/-- Prepending index to iterDerivList. -/
theorem iterDerivList_cons (i : Fin n) (S : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    iterDerivList (i :: S) p = iterDerivList S (pderiv i p) := by
  simp [iterDerivList, List.foldl_cons]

/-- iterDerivList S (a * b) lies in the span of products
    g * iterDerivList T b where T is a sublist of S and
    g.totalDegree ≤ a.totalDegree. -/
theorem iterDerivList_mul_mem_span (S : List (Fin n)) (a b : MvPolynomial (Fin n) F) :
    iterDerivList S (a * b) ∈
      Submodule.span F { q | ∃ (T : List (Fin n)) (g : MvPolynomial (Fin n) F),
        T.Sublist S ∧ g.totalDegree ≤ a.totalDegree ∧
        q = g * iterDerivList T b } := by
  induction S generalizing a b with
  | nil =>
    apply Submodule.subset_span
    exact ⟨[], a, List.nil_sublist _, le_refl _, rfl⟩
  | cons i rest ih =>
    rw [iterDerivList_cons, pderiv_mul, iterDerivList_add]
    apply Submodule.add_mem
    · -- Term 1: iterDerivList rest ((pderiv i a) * b)
      have h1 := ih (pderiv i a) b
      apply Submodule.span_mono _ h1
      intro q ⟨T, g, hT, hg, hq⟩
      exact ⟨T, g, List.Sublist.cons i hT, le_trans hg (totalDegree_pderiv_le i a), hq⟩
    · -- Term 2: iterDerivList rest (a * (pderiv i b))
      have h2 := ih a (pderiv i b)
      apply Submodule.span_mono _ h2
      intro q ⟨T, g, hT, hg, hq⟩
      refine ⟨i :: T, g, List.Sublist.cons₂ i hT, hg, ?_⟩
      rw [hq, iterDerivList_cons]

end IterLeibniz
