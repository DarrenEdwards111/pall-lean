import PallLean.Paper93.DeepMath.PathB.ComputationalDepthOrApprox
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

/-- **Evaluation of the OR-gate polynomial.**  At a point, `orPoly P Ss` equals the `OR`-indicator over the
random forms: `0` if *all* forms vanish on the value-vector `v i = eval point (Pᵢ)`, else `1`.  Proof: `eval` is a
ring hom (commutes with `1 - ∏(1 - (Σ·)^(p-1))`); Fermat (`pow_card_sub_one`) turns each `(linForm)^(p-1)` into
`[linForm ≠ 0]`, and `prod_boole` turns the product of `[linForm = 0]`-indicators into `[∀ j, linForm = 0]`. -/
theorem orPoly_eval [Fact p.Prime] (P : Fin k → MvPolynomial (Fin n) (ZMod p))
    (Ss : Fin t → Finset (Fin k)) (point : Fin n → ZMod p) :
    eval point (orPoly P Ss)
      = if (∀ j, OrApprox.linForm (fun i => eval point (P i)) (Ss j) = 0) then 0 else 1 := by
  rw [orPoly, map_sub, map_one, map_prod]
  have hfac : ∀ j : Fin t, eval point (1 - (∑ i ∈ Ss j, P i) ^ (p - 1))
      = if OrApprox.linForm (fun i => eval point (P i)) (Ss j) = 0 then 1 else 0 := by
    intro j
    rw [map_sub, map_one, map_pow, map_sum]
    show (1 : ZMod p) - (OrApprox.linForm (fun i => eval point (P i)) (Ss j)) ^ (p - 1)
        = if OrApprox.linForm (fun i => eval point (P i)) (Ss j) = 0 then 1 else 0
    rw [OrApprox.pow_card_sub_one]
    split <;> simp
  simp_rw [hfac]
  rw [Finset.prod_boole]
  by_cases h : ∀ j, OrApprox.linForm (fun i => eval point (P i)) (Ss j) = 0 <;> simp [h]

/-- **The OR-gate pointwise correctness.**  At a point where the children's polynomials equal the children's true
`0/1` outputs `b` (i.e. off the children's bad sets), and where the forms do *not* disagree (off the gate's bad
set), `orPoly P Ss` evaluates to the `OR` of the children: `0` if all `bᵢ` are `false`, else `1`.  Proof: by
`orPoly_eval` the value is `[∃ j, linForm = 0]`; if the boolean vector is `0` (all false) all forms vanish and
both sides are `0`; otherwise `¬disagree` forces some form nonzero and both sides are `1`. -/
theorem orPoly_eval_eq_or [Fact p.Prime] (P : Fin k → MvPolynomial (Fin n) (ZMod p))
    (Ss : Fin t → Finset (Fin k)) (point : Fin n → ZMod p) (b : Fin k → Bool)
    (hv : ∀ i, eval point (P i) = ((b i).toNat : ZMod p))
    (hdis : ¬ ((∀ j, OrApprox.linForm (fun i => ((b i).toNat : ZMod p)) (Ss j) = 0)
              ∧ (fun i => ((b i).toNat : ZMod p)) ≠ 0)) :
    eval point (orPoly P Ss) = if (∀ i, b i = false) then (0 : ZMod p) else 1 := by
  rw [orPoly_eval, funext hv]
  by_cases hb0 : (fun i => ((b i).toNat : ZMod p)) = 0
  · have hall : ∀ j, OrApprox.linForm (fun i => ((b i).toNat : ZMod p)) (Ss j) = 0 := by
      intro j; rw [hb0]; simp [OrApprox.linForm]
    have hbf : ∀ i, b i = false := by
      intro i
      by_contra hbi
      simp only [Bool.not_eq_false] at hbi
      have hc := congrFun hb0 i
      rw [Pi.zero_apply, hbi] at hc
      simp at hc
    rw [if_pos hall, if_pos hbf]
  · have hnall : ¬ ∀ j, OrApprox.linForm (fun i => ((b i).toNat : ZMod p)) (Ss j) = 0 :=
      fun hall => hdis ⟨hall, hb0⟩
    have hbf : ¬ ∀ i, b i = false := by
      intro hbf
      exact hb0 (funext (fun i => by rw [hbf i]; simp))
    rw [if_neg hnall, if_neg hbf]

end PallLean.Paper93.DeepMath.PathB.OrPoly

#print axioms PallLean.Paper93.DeepMath.PathB.OrPoly.orPoly_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.OrPoly.orPoly_eval
#print axioms PallLean.Paper93.DeepMath.PathB.OrPoly.orPoly_eval_eq_or
