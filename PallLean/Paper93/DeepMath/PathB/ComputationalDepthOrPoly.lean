import Mathlib

/-!
# The OR-gate approximating polynomial (PROVED: definition + degree) — the heart of `caOr`

The `OR`-gate constructor of the term-carrying circuit approximation substitutes the children's approximating
polynomials `P : Fin k → 𝔽_p[x]` into the `t`-fold OR-approximator with random subsets `Ss : Fin t → Finset (Fin k)`:

  `orPoly P Ss = 1 - ∏ⱼ (1 - (Σ_{i∈Sⱼ} Pᵢ)^(p-1))`.

  `orPoly_totalDegree_le` — if every child has degree `≤ B`, then `orPoly P Ss` has total degree
        `≤ t·(p-1)·B` — exactly the `degApprox` gate bound `D·(max child)` with `D = t(p-1)`.

This is the degree half of `caOr`: the gate's polynomial is built and its degree is bounded by the recurrence.
The remaining half is the gate's correctness (`ApproxOn`): off the children's bad sets and the gate's bad set
(from `GateApprox.exists_good_forms_gen`), `orPoly` evaluates to the `OR` of the children — chaining the children's
approximations with the chosen forms.  That `eval`/`ApproxOn` half completes `caOr`.
-/

open MvPolynomial

namespace PallLean.Paper93.DeepMath.PathB.OrPoly

variable {n p k t : ℕ}

/-- The OR-gate approximating polynomial: the children's polynomials `P` substituted into the `t`-fold
OR-approximator with random subsets `Ss`. -/
noncomputable def orPoly (P : Fin k → MvPolynomial (Fin n) (ZMod p)) (Ss : Fin t → Finset (Fin k)) :
    MvPolynomial (Fin n) (ZMod p) :=
  1 - ∏ j : Fin t, (1 - (∑ i ∈ Ss j, P i) ^ (p - 1))

/-- **Degree of the OR-gate polynomial.**  If every child polynomial has total degree `≤ B`, then `orPoly P Ss`
has total degree `≤ t·(p-1)·B`: each random linear form has degree `≤ B`, its `(p-1)`-th power degree `≤ (p-1)·B`,
the product over `t` forms degree `≤ t·(p-1)·B`, and subtracting from `1` does not raise it. -/
theorem orPoly_totalDegree_le (P : Fin k → MvPolynomial (Fin n) (ZMod p))
    (Ss : Fin t → Finset (Fin k)) (B : ℕ) (hP : ∀ i, (P i).totalDegree ≤ B) :
    (orPoly P Ss).totalDegree ≤ t * (p - 1) * B := by
  rw [orPoly]
  refine le_trans (totalDegree_sub _ _) ?_
  rw [totalDegree_one]
  refine max_le (Nat.zero_le _) (le_trans (totalDegree_finset_prod _ _) ?_)
  calc ∑ j : Fin t, (1 - (∑ i ∈ Ss j, P i) ^ (p - 1)).totalDegree
      ≤ ∑ _j : Fin t, (p - 1) * B := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        refine le_trans (totalDegree_sub _ _) ?_
        rw [totalDegree_one]
        refine max_le (Nat.zero_le _) (le_trans (totalDegree_pow _ _) ?_)
        refine Nat.mul_le_mul_left (p - 1) (le_trans (totalDegree_finset_sum _ _) ?_)
        exact Finset.sup_le (fun i _ => hP i)
    _ = t * (p - 1) * B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_assoc]

end PallLean.Paper93.DeepMath.PathB.OrPoly

#print axioms PallLean.Paper93.DeepMath.PathB.OrPoly.orPoly_totalDegree_le
