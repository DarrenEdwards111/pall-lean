import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RSToSymAnd

/-!
# The `MOD_p` gate is *exactly* degree `≤ p−1` over `F_p` (Fermat) — the `AC⁰[p]` ingredient

`…ACC0Mod2Exact` showed `MOD₂` (parity) is the degree-1 linear form over `F₂`.  The general prime-`p` analogue uses
**Fermat's little theorem**: over `F_p`, the count-`≡ 0` indicator is

```
MOD_p(x) = [∑_{i∈S} x_i ≡ 0 (mod p)]  =  1 − (∑_{i∈S} x_i)^{p−1} ,
```

since `a^{p−1} = 1` for `a ≠ 0` and `0^{p−1} = 0` in `F_p`.  This is an **exact** degree-`(p−1)` polynomial — so a `MOD_p`
gate composes into the Razborov–Smolensky `F_p` machinery with degree `p−1` and error `0`, the prime-power ingredient
of `AC⁰[p]`.

## What is proved (clean axioms, no `sorry`)

* `modpPoly` / `modpBool` — the `F_p` polynomial `1 − (∑_{i∈S} X_i)^{p−1}` and the `MOD_p` gate.
* `modp_exact_eval` — `eval (modpPoly S) x = boolToZMod p (modpBool S x)`: the polynomial computes `MOD_p` *exactly*
  (by Fermat).
* `modpPoly_totalDegree_le` (`≤ p − 1`) and **`modp_mem_monoAND_span`** — `MOD_p` lies in the degree-`≤(p−1)`
  monomial-`AND` span over `F_p`.

## Honest scope — prime-power only; composite `MOD` is the barrier

This handles `MOD_p` for **prime** `p` over `F_p` (and prime-powers reduce to `F_{p^k}` by the same Fermat argument).
It does **not** extend to **composite** `m = p·q`: there is no single field in which `MOD_m` is low-degree, because
`a^{m−1}` is not a `{0,1}`-indicator over `F_p` (Fermat fixes the order to `p−1`, not `m−1`).  That is the genuine
`ACC⁰` barrier (`…ACC0Mod2Exact`, and the barrier note in `WHAT_IS_PROVED.md`), the reason the polynomial method
stops at `AC⁰[p^k]`.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md` and `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModPExact

open scoped Classical
open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0RSToSymAnd

variable {n : ℕ}

/-- The `F_p` **`MOD_p` polynomial** `1 − (∑_{i∈S} X_i)^{p−1}`. -/
noncomputable def modpPoly (p : ℕ) (S : Finset (Fin n)) : MvPolynomial (Fin n) (ZMod p) :=
  1 - (∑ i ∈ S, X i) ^ (p - 1)

/-- The **`MOD_p` gate**: the support count is `≡ 0 (mod p)`. -/
def modpBool (p : ℕ) (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide ((∑ i ∈ S, boolToZMod p (x i)) = 0)

variable {p : ℕ} [Fact p.Prime]

/-- **`MOD_p` has total degree `≤ p − 1` (proved).** -/
theorem modpPoly_totalDegree_le (S : Finset (Fin n)) : (modpPoly p S).totalDegree ≤ p - 1 := by
  unfold modpPoly
  refine le_trans (totalDegree_sub _ _) ?_
  rw [totalDegree_one]
  refine max_le (Nat.zero_le _) ?_
  refine le_trans (totalDegree_pow _ _) ?_
  have hlin : (∑ i ∈ S, (X i : MvPolynomial (Fin n) (ZMod p))).totalDegree ≤ 1 := by
    apply totalDegree_finsetSum_le
    intro i _
    exact le_of_eq (totalDegree_X i)
  calc (p - 1) * (∑ i ∈ S, (X i : MvPolynomial (Fin n) (ZMod p))).totalDegree
      ≤ (p - 1) * 1 := Nat.mul_le_mul_left _ hlin
    _ = p - 1 := mul_one _

/-- **`MOD_p` is computed *exactly* by the degree-`(p−1)` polynomial (proved), via Fermat.** -/
theorem modp_exact_eval (x : Fin n → Bool) (S : Finset (Fin n)) :
    eval (fun i => boolToZMod p (x i)) (modpPoly p S) = boolToZMod p (modpBool p S x) := by
  unfold modpPoly modpBool
  rw [eval_sub, map_one, map_pow, eval_sum]
  simp only [eval_X]
  have hp1 : p - 1 ≠ 0 := by have := (Fact.out : p.Prime).two_le; omega
  set s := ∑ i ∈ S, boolToZMod p (x i) with hsdef
  by_cases hs : s = 0
  · rw [hs, zero_pow hp1, sub_zero]
    simp
  · rw [ZMod.pow_card_sub_one_eq_one hs, sub_self]
    simp [hs]

/-- **`MOD_p` lies in the degree-`≤(p−1)` monomial-`AND` span over `F_p` (proved).** -/
theorem modp_mem_monoAND_span (S : Finset (Fin n)) :
    (fun x : Fin n → Bool => boolToZMod p (modpBool p S x))
      ∈ Submodule.span (ZMod p)
        (Set.range (fun T : {T // T ∈ lowDegMonomials n (p - 1)} =>
          fun x : Fin n → Bool => if monoAND T.1 x then (1 : ZMod p) else 0)) := by
  have hkey := lowDegPolyEval_mem_monoAND_span p (p - 1) (modpPoly p S) (modpPoly_totalDegree_le S)
  have hfun : (fun x : Fin n → Bool => boolToZMod p (modpBool p S x))
      = (fun x : Fin n → Bool => eval (fun i => boolToZMod p (x i)) (modpPoly p S)) := by
    funext x
    exact (modp_exact_eval x S).symm
  rw [hfun]
  exact hkey

end PallLean.Paper93.DeepMath.PathB.ACC0ModPExact

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModPExact.modp_exact_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModPExact.modp_mem_monoAND_span
