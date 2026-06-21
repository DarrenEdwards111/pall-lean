import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0AndPoly

/-!
# Brick (OR-approx) — the Razborov–Smolensky random-linear-form `OR` approximator (proved, deterministic core)

The genuine low-degree approximate representation of `OR` over `F_p`.  For `a : Fin n → F_p`, the polynomial
`orApprox a = (∑ᵢ aᵢ Xᵢ)^{p-1}` has total degree `≤ p-1` (independent of fan-in!) and, by Fermat's little theorem,
evaluates to `[∑ᵢ aᵢ xᵢ ≠ 0]` on Boolean inputs.  Hence:

* on the all-false input it is `0` (= `OR`), and
* whenever the random linear form `∑ᵢ aᵢ xᵢ ≠ 0` it is `1` (= `OR`, since a nonzero form forces a nonzero input).

So a *single* random linear form already computes `OR` *exactly off a "bad set"* — the inputs `x ≠ 0` with `∑ aᵢ xᵢ = 0` —
with degree only `p-1`, not the fan-in `n`.  This is the deterministic skeleton of the RS probabilistic polynomial that
makes `AND`/`OR` composable at low degree (unlike the exact `andPoly`, whose degree is the fan-in).

**Honest:** the *probabilistic* completion — that the bad set has measure `≤ 1/p` over random `a` (balancedness of a nonzero
linear functional), `t`-fold amplification to error `p^{-t}` at degree `t(p-1)`, and the averaging/existence of one good
polynomial — is the remaining genuine content and is **not** built here, **not** faked.  `AND` follows by De Morgan.

## What is proved (clean axioms, no `sorry`)

* **`orApprox_totalDegree_le`** (PROVED) — `(orApprox p n a).totalDegree ≤ p-1` (degree independent of fan-in).
* **`orApprox_eval`** (PROVED) — `eval (Boolean x) (orApprox p n a) = (∑ᵢ aᵢ [xᵢ])^{p-1}`.
* **`orApprox_eval_allFalse`** (PROVED) — `(∀ i, x i = false) → eval = 0`.
* **`orApprox_eval_of_form_ne_zero`** (PROVED) — `(∑ᵢ aᵢ [xᵢ]) ≠ 0 → eval = 1`.

## Honest scope

This is the **deterministic** RS single-form `OR` approximator (degree `p-1`, exact off the bad set).  It does **not** prove
the probabilistic error bound, `t`-fold amplification, existence of a good polynomial, cross-prime nesting, prime-power
composition, nor `composite_BT_degree`.  General YBT remains open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0OrApprox

open MvPolynomial

/-- **The RS random-linear-form `OR` approximator:** `(∑ᵢ aᵢ Xᵢ)^{p-1}` over `F_p`. -/
noncomputable def orApprox (p n : ℕ) (a : Fin n → ZMod p) : MvPolynomial (Fin n) (ZMod p) :=
  (∑ i, C (a i) * X i) ^ (p - 1)

/-- **The approximator has degree `≤ p-1`, independent of the fan-in (PROVED).** -/
theorem orApprox_totalDegree_le (p n : ℕ) [Fact p.Prime] (a : Fin n → ZMod p) :
    (orApprox p n a).totalDegree ≤ p - 1 := by
  have hsum : (∑ i : Fin n, (C (a i) * X i : MvPolynomial (Fin n) (ZMod p))).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_finset_sum _ _) ?_
    refine Finset.sup_le (fun i _ => ?_)
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    rw [MvPolynomial.totalDegree_C, zero_add, MvPolynomial.totalDegree_X]
  rw [orApprox]
  refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
  calc (p - 1) * (∑ i, (C (a i) * X i : MvPolynomial (Fin n) (ZMod p))).totalDegree
      ≤ (p - 1) * 1 := Nat.mul_le_mul_left _ hsum
    _ = p - 1 := Nat.mul_one _

/-- **Evaluation at a Boolean input is `(∑ᵢ aᵢ [xᵢ])^{p-1}` (PROVED).** -/
theorem orApprox_eval (p n : ℕ) (a : Fin n → ZMod p) (x : Fin n → Bool) :
    eval (fun i => if x i then (1 : ZMod p) else 0) (orApprox p n a)
      = (∑ i, a i * (if x i then (1 : ZMod p) else 0)) ^ (p - 1) := by
  rw [orApprox, map_pow, map_sum]
  refine congrArg (· ^ (p - 1)) (Finset.sum_congr rfl (fun i _ => ?_))
  rw [map_mul, eval_C, eval_X]

/-- **On the all-false input the approximator is `0` (= `OR`) (PROVED).** -/
theorem orApprox_eval_allFalse (p n : ℕ) [Fact p.Prime] (a : Fin n → ZMod p) (x : Fin n → Bool)
    (hx : ∀ i, x i = false) :
    eval (fun i => if x i then (1 : ZMod p) else 0) (orApprox p n a) = 0 := by
  rw [orApprox_eval]
  have hz : (∑ i, a i * (if x i then (1 : ZMod p) else 0)) = 0 :=
    Finset.sum_eq_zero (fun i _ => by rw [hx i]; simp)
  rw [hz]
  exact zero_pow (by have := (Fact.out : p.Prime).two_le; omega)

/-- **Whenever the linear form is nonzero the approximator is `1` (= `OR`) (PROVED).** -/
theorem orApprox_eval_of_form_ne_zero (p n : ℕ) [Fact p.Prime] (a : Fin n → ZMod p) (x : Fin n → Bool)
    (h : (∑ i, a i * (if x i then (1 : ZMod p) else 0)) ≠ 0) :
    eval (fun i => if x i then (1 : ZMod p) else 0) (orApprox p n a) = 1 := by
  rw [orApprox_eval]
  exact ZMod.pow_card_sub_one_eq_one h

/-!
**The deterministic RS `OR` approximator, proved.**  `(∑ aᵢXᵢ)^{p-1}` has degree `p-1` (not fan-in), is `0` on the
all-false input, and `1` whenever the random linear form is nonzero — exact `OR` off the bad set.  This is what makes
`AND`/`OR` low-degree under composition.  Remaining (open, not faked): the probabilistic bad-set bound (`≤ 1/p`),
`t`-fold amplification, and existence of one good polynomial.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0OrApprox

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0OrApprox.orApprox_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0OrApprox.orApprox_eval_of_form_ne_zero
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0OrApprox.orApprox_eval_allFalse
