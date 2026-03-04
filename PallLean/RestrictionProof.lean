import PallLean.SPDPDefs
import PallLean.CoeffBridge
import PallLean.FiniteSPDP
import Mathlib.Tactic
/-!
# Restriction Monotonicity — Pall §2 Basic Property 3
-/

namespace RestrictionProof

open MvPolynomial SPDP

variable {n : ℕ} {F : Type*} [Field F]

noncomputable def evalAtHom (i : Fin n) (c : F) :
    MvPolynomial (Fin n) F →ₐ[F] MvPolynomial (Fin n) F :=
  aeval (fun j => if j = i then C c else X j)

set_option maxHeartbeats 800000 in
theorem pderiv_evalAtHom_comm (i v : Fin n) (hvi : v ≠ i) (c : F)
    (p : MvPolynomial (Fin n) F) :
    pderiv v (evalAtHom i c p) = evalAtHom i c (pderiv v p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [evalAtHom, pderiv_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p u h =>
    simp only [evalAtHom] at h ⊢
    by_cases hu : u = i
    · subst hu
      -- Now i is gone, replaced by u. v ≠ u.
      have hvi' : u ≠ v := hvi.symm
      simp only [map_mul, aeval_X, if_pos rfl, ite_true, Derivation.leibniz,
        pderiv_C, pderiv_X, Pi.single_apply, hvi, hvi', ite_false, smul_eq_mul,
        mul_zero, add_zero, zero_mul, map_add, map_mul, map_zero, zero_add,
        map_one, mul_one]
      exact congrArg (C c * ·) h
    · by_cases huv : u = v
      · subst huv
        simp only [map_mul, aeval_X, if_neg hu, Derivation.leibniz,
          pderiv_X, Pi.single_apply, if_pos rfl, ite_true, smul_eq_mul,
          mul_one, map_add, map_mul, map_one]
        rw [h]
      · simp only [map_mul, aeval_X, if_neg hu, Derivation.leibniz,
          pderiv_X, Pi.single_apply, huv, ite_false, smul_eq_mul,
          mul_zero, zero_add, map_add, map_mul, map_zero, add_zero, h]

theorem restriction_rank_le' (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) (i : Fin n) (c : F) :
    spdpRank κ ℓ ((evalAtHom i c) p) ≤ spdpRank κ ℓ p := by
  sorry

end RestrictionProof
