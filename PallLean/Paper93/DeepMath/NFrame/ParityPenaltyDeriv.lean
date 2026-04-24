/-
  PallLean/Paper93/DeepMath/NFrame/ParityPenaltyDeriv.lean

  Partial derivative of the N-Frame parity penalty `parityPenalty` in
  the `k`-th coordinate at a point `φ` with `φ_k ≠ 0`. Since
  `Real.sign` is locally constant away from zero (see
  `SignLocallyConst`), each per-vertex term `parityTerm` depends on
  `φ_k` only through `Real.sign φ_k`, which is locally constant at any
  `φ_k ≠ 0`. The remaining terms (indexed by `i ≠ k`) do not depend on
  `φ_k` at all. Hence the partial derivative vanishes.

  Kernel-only; no `sorry`, no bespoke axioms, no `True`.
-/
import PallLean.Paper93.DeepMath.NFrame.ParityTermDeriv
import Mathlib.Analysis.Calculus.Deriv.Add

namespace PallLean.Paper93.DeepMath.NFrame

open scoped BigOperators

/-- The per-index summand of the parity penalty, viewed as a function of
    the updated `k`-th coordinate, has derivative `0` at `t = φ_k`
    whenever `φ_k ≠ 0`.

    * If `i = k`, the summand equals `parityTerm (chi k) t`, whose
      derivative at `φ_k ≠ 0` is `0` by
      `parityTerm_hasDerivAt_of_pos` / `parityTerm_hasDerivAt_of_neg`.
    * If `i ≠ k`, the summand is the constant `parityTerm (chi i) (phi i)`
      in `t`, so its derivative is `0`. -/
theorem parityPenalty_summand_hasDerivAt_zero {n : ℕ} (chi phi : Fin n → ℝ)
    (k : Fin n) (h : phi k ≠ 0) (i : Fin n) :
    HasDerivAt
      (fun t => parityTerm (chi i) (Function.update phi k t i))
      0 (phi k) := by
  by_cases hik : i = k
  · -- i = k: summand is parityTerm (chi k) t (after update_self)
    subst hik
    -- Rewrite the function as `fun t => parityTerm (chi i) t` using update_self.
    have heq :
        (fun t => parityTerm (chi i) (Function.update phi i t i)) =
          (fun t => parityTerm (chi i) t) := by
      funext t
      simp [Function.update_self]
    rw [heq]
    -- Now split on the sign of phi i ≠ 0.
    rcases lt_or_gt_of_ne h with hlt | hgt
    · exact parityTerm_hasDerivAt_of_neg (chi i) (phi i) hlt
    · exact parityTerm_hasDerivAt_of_pos (chi i) (phi i) hgt
  · -- i ≠ k: summand is the constant parityTerm (chi i) (phi i).
    have heq :
        (fun t => parityTerm (chi i) (Function.update phi k t i)) =
          (fun _t : ℝ => parityTerm (chi i) (phi i)) := by
      funext t
      rw [Function.update_of_ne (Ne.symm (fun h' => hik h'.symm)) t phi]
    rw [heq]
    exact hasDerivAt_const (phi k) (parityTerm (chi i) (phi i))

/-- `parityPenalty chi` has partial derivative `0` in the `k`-th
    component `φ_k` whenever `φ_k ≠ 0`. On the smooth region
    `{φ_k ≠ 0}`, `Real.sign` is locally constant in `φ_k`, so each
    summand is locally constant in `φ_k` and the penalty as a whole has
    vanishing partial derivative in that coordinate. -/
theorem parityPenalty_partial_zero_of_ne_zero {n : ℕ} (chi : Fin n → ℝ)
    (phi : Fin n → ℝ) (k : Fin n) (h : phi k ≠ 0) :
    HasDerivAt (fun t => parityPenalty chi (Function.update phi k t)) 0 (phi k) := by
  -- Unfold parityPenalty and commute the sum outside the `t`-function.
  have hsum :
      (fun t => parityPenalty chi (Function.update phi k t)) =
        (fun t => ∑ i : Fin n,
          parityTerm (chi i) (Function.update phi k t i)) := by
    funext t
    rfl
  rw [hsum]
  -- The zero derivative written as a sum of zeros.
  have hzero_sum : (0 : ℝ) = ∑ _i : Fin n, (0 : ℝ) := by
    simp
  rw [hzero_sum]
  -- Apply HasDerivAt.sum with per-index derivative zero.
  exact HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n)))
    (A := fun i t => parityTerm (chi i) (Function.update phi k t i))
    (A' := fun _ => (0 : ℝ))
    (fun i _hi => parityPenalty_summand_hasDerivAt_zero chi phi k h i)

end PallLean.Paper93.DeepMath.NFrame
