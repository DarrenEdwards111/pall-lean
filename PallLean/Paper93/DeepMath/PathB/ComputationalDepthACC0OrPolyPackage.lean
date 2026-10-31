import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0OrApprox
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0UnionBound

/-!
# Brick (OR package) — one degree-`t(p-1)` polynomial computing `OR` everywhere (proved)

The packaging of the Razborov–Smolensky approximate `OR` into a single `MvPolynomial`.  Given `t` coefficient vectors,
`orPoly a = 1 - ∏ⱼ (1 - orApprox aⱼ)` is the `OR` of the `t` random-linear-form approximators.  It has total degree
`≤ t(p-1)`, evaluates to `0` on the all-zero input, and to `1` on any input where *some* form is nonzero.  Combined with the
union bound (`exists_good_form`), for any test set `X` of nonzero inputs with `|X|·(p^{n-1})^t < (p^n)^t` there is a *fixed*
polynomial `P` of degree `≤ t(p-1)` with `P = 1` on all of `X` and `P(0) = 0`.

Taking `X` = the nonzero inputs and `t` with `p^t > |X|`, this is one fixed low-degree polynomial computing `OR` correctly on
every input — the fully-assembled RS approximate-`OR` polynomial.

## What is proved (clean axioms, no `sorry`)

* **`orPoly`**, **`orPoly_totalDegree_le`** (PROVED) — degree `≤ t(p-1)`.
* **`orPoly_eval_eq_one`** (PROVED) — `(∃ j, ∑ᵢ (aⱼ)ᵢ xᵢ ≠ 0) → eval x (orPoly a) = 1`.
* **`orPoly_eval_zero`** (PROVED) — `eval 0 (orPoly a) = 0`.
* **`exists_orPoly`** (PROVED) — `∃ P, P.totalDegree ≤ t(p-1) ∧ (∀ x ∈ X, eval x P = 1) ∧ eval 0 P = 0`.

## Honest scope

This packages the approximate **`OR`** polynomial.  It does **not** do the prime-power `MOD_{p^e}` composition (the A.3
obstruction — no clean `F_p` representation, *not faked*), nor the `ACC0Circuit`-level assembly of all gate types into
`composite_BT_degree` (which needs that obstruction resolved).  General YBT remains open.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0OrPolyPackage

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ACC0OrApprox (orApprox orApprox_totalDegree_le)
open PallLean.Paper93.DeepMath.PathB.ACC0UnionBound (exists_good_form)

/-- **The packaged `OR` polynomial:** the `OR` of `t` random-linear-form approximators. -/
noncomputable def orPoly (p n t : ℕ) (a : Fin t → (Fin n → ZMod p)) : MvPolynomial (Fin n) (ZMod p) :=
  1 - ∏ j, (1 - orApprox p n (a j))

/-- **`orApprox` evaluated at a general `F_p` input is `(∑ᵢ aᵢ xᵢ)^{p-1}` (PROVED).** -/
theorem orApprox_eval_gen (p n : ℕ) (a : Fin n → ZMod p) (x : Fin n → ZMod p) :
    eval x (orApprox p n a) = (∑ i, a i * x i) ^ (p - 1) := by
  rw [orApprox, map_pow, map_sum]
  refine congrArg (· ^ (p - 1)) (Finset.sum_congr rfl (fun i _ => ?_))
  rw [map_mul, eval_C, eval_X]

/-- **The packaged polynomial has degree `≤ t(p-1)` (PROVED).** -/
theorem orPoly_totalDegree_le (p n t : ℕ) [Fact p.Prime] (a : Fin t → (Fin n → ZMod p)) :
    (orPoly p n t a).totalDegree ≤ t * (p - 1) := by
  rw [orPoly]
  refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
  · rw [MvPolynomial.totalDegree_one]; exact Nat.zero_le _
  · refine le_trans (MvPolynomial.totalDegree_finset_prod _ _) ?_
    calc ∑ j : Fin t, ((1 : MvPolynomial (Fin n) (ZMod p)) - orApprox p n (a j)).totalDegree
        ≤ ∑ _j : Fin t, (p - 1) :=
          Finset.sum_le_sum (fun j _ => le_trans (MvPolynomial.totalDegree_sub _ _)
            (max_le (by rw [MvPolynomial.totalDegree_one]; exact Nat.zero_le _)
              (orApprox_totalDegree_le p n (a j))))
      _ = t * (p - 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **`orPoly` evaluates to `1` when some form is nonzero on the input (PROVED).** -/
theorem orPoly_eval_eq_one (p n t : ℕ) [Fact p.Prime] (a : Fin t → (Fin n → ZMod p)) (x : Fin n → ZMod p)
    (h : ∃ j, (∑ i, (a j) i * x i) ≠ 0) :
    eval x (orPoly p n t a) = 1 := by
  rw [orPoly, map_sub, map_one, map_prod]
  obtain ⟨j, hj⟩ := h
  have hzero : ∏ k, eval x ((1 : MvPolynomial (Fin n) (ZMod p)) - orApprox p n (a k)) = 0 := by
    refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
    rw [map_sub, map_one, orApprox_eval_gen, ZMod.pow_card_sub_one_eq_one hj, sub_self]
  rw [hzero, sub_zero]

/-- **`orPoly` evaluates to `0` on the all-zero input (PROVED).** -/
theorem orPoly_eval_zero (p n t : ℕ) [Fact p.Prime] (a : Fin t → (Fin n → ZMod p)) :
    eval (0 : Fin n → ZMod p) (orPoly p n t a) = 0 := by
  rw [orPoly, map_sub, map_one, map_prod]
  have hone : ∏ k, eval (0 : Fin n → ZMod p) ((1 : MvPolynomial (Fin n) (ZMod p)) - orApprox p n (a k)) = 1 := by
    refine Finset.prod_eq_one (fun k _ => ?_)
    rw [map_sub, map_one, orApprox_eval_gen]
    have hz : (∑ i, (a k) i * (0 : Fin n → ZMod p) i) = 0 := by simp
    rw [hz, zero_pow (by have := (Fact.out : p.Prime).two_le; omega), sub_zero]
  rw [hone, sub_self]

/-- **The packaged RS approximate-`OR` polynomial exists (PROVED): one fixed degree-`t(p-1)` polynomial correct on `X`.** -/
theorem exists_orPoly (p n t : ℕ) [Fact p.Prime] (X : Finset (Fin n → ZMod p)) (hX : ∀ x ∈ X, x ≠ 0)
    (hlt : X.card * (p ^ (n - 1)) ^ t < (p ^ n) ^ t) :
    ∃ P : MvPolynomial (Fin n) (ZMod p),
      P.totalDegree ≤ t * (p - 1) ∧ (∀ x ∈ X, eval x P = 1) ∧ eval 0 P = 0 := by
  obtain ⟨a, ha⟩ := exists_good_form p n t X hX hlt
  refine ⟨orPoly p n t a, orPoly_totalDegree_le p n t a, fun x hxX => ?_, orPoly_eval_zero p n t a⟩
  obtain ⟨j, hj⟩ := ha x hxX
  have hj' : (∑ i, (a j) i * x i) ≠ 0 := by
    have hcomm : (∑ i, x i * (a j) i) = (∑ i, (a j) i * x i) :=
      Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rwa [hcomm] at hj
  exact orPoly_eval_eq_one p n t a x ⟨j, hj'⟩

/-!
**The RS approximate-`OR` polynomial, packaged.**  One fixed `MvPolynomial` of degree `≤ t(p-1)` computes `OR` correctly on a
test set `X` (with `|X| < p^t`) and on `0` — the full assembly of the Razborov–Smolensky construction.  Remaining for general
YBT (open, not faked): prime-power `MOD_{p^e}` composition (A.3 obstruction) and the `ACC0Circuit`-level `composite_BT_degree`.
Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0OrPolyPackage

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0OrPolyPackage.exists_orPoly
