import PallLean.SPDPRankDef
import PallLean.PDerivEval
import Mathlib.Tactic
/-!
# R1: Variable Restriction Cannot Increase SPDP Rank
-/

namespace SPDP.Restriction

open SPDP.Concrete PDerivEval MvPolynomial

variable {F : Type*} [CommRing F] [Nontrivial F]
variable {n : ℕ}

noncomputable def evalLin (i : Fin n) (c : F) :
    MvPolynomial (Fin n) F →ₗ[F] MvPolynomial (Fin n) F where
  toFun := evalAt i c
  map_add' := map_add _
  map_smul' := fun r x => by
    simp only [RingHom.id_apply, Algebra.smul_def, map_mul]
    congr 1; exact evalAt_C i c r

/-- iterDerivList on (evalAt p) is always in the image of evalAt -/
theorem iterDerivList_evalAt_in_image (i : Fin n) (c : F)
    (indices : List (Fin n)) (p : MvPolynomial (Fin n) F) :
    ∃ q, iterDerivList indices (evalAt i c p) = evalAt i c q := by
  induction indices generalizing p with
  | nil => exact ⟨p, rfl⟩
  | cons j rest ih =>
    simp only [iterDerivList, List.foldl_cons]
    by_cases hji : j = i
    · subst hji
      rw [pderiv_evalAt_self]
      have := foldl_pderiv_zero rest
      rw [this]
      exact ⟨0, by simp [evalAt]⟩
    · rw [pderiv_comm_evalAt i j hji c p]
      exact ih (pderiv j p)

/-- R1 sorry: the SPDP subspace containment.
    The remaining gap: shift monomial m in the restricted ring may not
    factor as evalAt(m'). Need to show m * evalAt(q') = evalAt(m' * q'). -/
theorem restriction_rank_le (κ : ℕ) (p : MvPolynomial (Fin n) F)
    (i : Fin n) (c : F) :
    spdpRankConcrete κ (evalAt i c p) ≤ spdpRankConcrete κ p := by
  sorry

end SPDP.Restriction
