import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PrimeMODLowDegree

/-!
# Brick A.2c — the `MOD_p` indicator as an `MvPolynomial` of total degree `≤ p-1` (proved)

Brick A.2 (`modp_iff_fermat`) gave the prime-`MOD` representation as the *structural* expression `(∑ᵢ [xᵢ])^{p-1}`.  This
file makes the degree claim a **typed theorem**: the explicit multivariate polynomial `modpPoly p n := (∑ᵢ Xᵢ)^{p-1}` over
`F_p` has `MvPolynomial.totalDegree ≤ p-1`, its evaluation at the Boolean indicator point recovers the Fermat form, and
hence `MOD_p` of the weight is decided by a degree-`≤(p-1)` `F_p` polynomial.

## What is proved (clean axioms, no `sorry`)

* **`modpPoly p n`** — the explicit polynomial `(∑ᵢ Xᵢ)^{p-1} : MvPolynomial (Fin n) (ZMod p)`.
* **`modpPoly_totalDegree_le`** (PROVED) — `(modpPoly p n).totalDegree ≤ p - 1`.
* **`modpPoly_eval`** (PROVED) — `eval (fun i => if x i then 1 else 0) (modpPoly p n) = (∑ i, if x i then 1 else 0)^{p-1}`.
* **`modp_iff_modpPoly`** (PROVED) — `(hammingWeight x : ZMod p) = 0 ↔ eval … (modpPoly p n) = 0`: the `MOD_p` gate is
  decided by the degree-`≤(p-1)` polynomial.

## Honest scope

This is the **typed degree bound** for the single prime-`MOD` gate.  It does **not** prove the prime-power (`e≥2`) Toda
lifting, the quasipoly `SYM∘AND` packaging, nor degree-additive depth composition — i.e. general YBT / `composite_BT_degree`
remains open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0PrimeMODMvPoly

open PallLean.Paper93.DeepMath.PathB.ACC0CompositeBT (hammingWeight)
open PallLean.Paper93.DeepMath.PathB.ACC0PrimeMODLowDegree (modp_iff_fermat)
open MvPolynomial

/-- **The `MOD_p` indicator polynomial:** `(∑ᵢ Xᵢ)^{p-1}` over `F_p`. -/
noncomputable def modpPoly (p n : ℕ) : MvPolynomial (Fin n) (ZMod p) :=
  (∑ i, X i) ^ (p - 1)

/-- **The indicator polynomial has total degree `≤ p-1` (PROVED).** -/
theorem modpPoly_totalDegree_le (p n : ℕ) [Fact p.Prime] :
    (modpPoly p n).totalDegree ≤ p - 1 := by
  have hsum : (∑ i : Fin n, (X i : MvPolynomial (Fin n) (ZMod p))).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_finset_sum _ _) ?_
    refine Finset.sup_le (fun i _ => ?_)
    rw [MvPolynomial.totalDegree_X]
  refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
  calc (p - 1) * (∑ i, (X i : MvPolynomial (Fin n) (ZMod p))).totalDegree
      ≤ (p - 1) * 1 := Nat.mul_le_mul_left _ hsum
    _ = p - 1 := Nat.mul_one _

/-- **Evaluation at the Boolean indicator point recovers the Fermat form (PROVED).** -/
theorem modpPoly_eval (p n : ℕ) (x : Fin n → Bool) :
    eval (fun i => if x i then (1 : ZMod p) else 0) (modpPoly p n)
      = (∑ i, (if x i then (1 : ZMod p) else 0)) ^ (p - 1) := by
  rw [modpPoly, map_pow, map_sum]
  refine congrArg (· ^ (p - 1)) (Finset.sum_congr rfl (fun i _ => ?_))
  rw [eval_X]

/-- **The `MOD_p` gate is decided by the degree-`≤(p-1)` polynomial (PROVED).** -/
theorem modp_iff_modpPoly (p n : ℕ) [Fact p.Prime] (x : Fin n → Bool) :
    (hammingWeight x : ZMod p) = 0 ↔ eval (fun i => if x i then (1 : ZMod p) else 0) (modpPoly p n) = 0 := by
  rw [modpPoly_eval]; exact modp_iff_fermat p x

/-!
**The typed degree bound, proved.**  `MOD_p` is decided by `modpPoly`, an `MvPolynomial` over `F_p` of total degree
`≤ p-1` — the degree claim is now a theorem, ready to feed the degree-additive depth composition.  Next: prime-power
`e≥2` Toda lifting, then composition (Brick C).  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0PrimeMODMvPoly

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimeMODMvPoly.modpPoly_totalDegree_le
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0PrimeMODMvPoly.modp_iff_modpPoly
