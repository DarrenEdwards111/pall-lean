import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic
/-!
# pderiv commutes with evaluation at a DIFFERENT variable — PROVED

∂_j(p|_{x_i=c}) = (∂_j p)|_{x_i=c}  when j ≠ i.
-/

namespace PDerivEval

open MvPolynomial

variable {F : Type*} [CommRing F] {n : ℕ}

noncomputable def evalAt (i : Fin n) (c : F) :
    MvPolynomial (Fin n) F →+* MvPolynomial (Fin n) F :=
  eval₂Hom C (fun j => if j = i then C c else X j)

@[simp] theorem evalAt_C (i : Fin n) (c : F) (a : F) :
    evalAt i c (C a) = C a := by simp [evalAt, eval₂Hom_C]

@[simp] theorem evalAt_X_ne (i : Fin n) (c : F) (j : Fin n) (h : j ≠ i) :
    evalAt i c (X j) = X j := by simp [evalAt, eval₂Hom_X', if_neg h]

@[simp] theorem evalAt_X_self (i : Fin n) (c : F) :
    evalAt i c (X i) = C c := by simp [evalAt, eval₂Hom_X']

/-- **pderiv j commutes with evalAt i when j ≠ i** — PROVED by induction -/
theorem pderiv_comm_evalAt (i j : Fin n) (hij : j ≠ i) (c : F)
    (p : MvPolynomial (Fin n) F) :
    pderiv j (evalAt i c p) = evalAt i c (pderiv j p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [pderiv_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p k ih =>
    simp only [map_mul]
    rw [pderiv_mul, pderiv_mul]
    simp only [map_add, map_mul]
    -- Goal: pderiv j (evalAt p) * evalAt(X k) + evalAt(p) * pderiv j (evalAt(X k))
    --     = evalAt(pderiv j p) * evalAt(X k) + evalAt(p) * evalAt(pderiv j (X k))
    -- First part follows from ih, second from X k case
    have h_deriv : pderiv j (evalAt i c (X k)) = evalAt i c (pderiv j (X k)) := by
      by_cases hki : k = i
      · subst hki
        simp [pderiv_C, pderiv_X_of_ne (Ne.symm hij)]
      · rw [evalAt_X_ne _ _ _ hki]
        by_cases hkj : k = j
        · subst hkj; simp [pderiv_X_self]
        · simp [pderiv_X_of_ne hkj]
    rw [ih, h_deriv]

end PDerivEval
