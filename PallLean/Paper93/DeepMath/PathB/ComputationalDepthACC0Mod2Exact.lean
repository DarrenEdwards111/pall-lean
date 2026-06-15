import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0BasisBridge

/-!
# The `MOD₂` gate is *exactly* degree 1 — no approximation, error 0

`OR` and `AND` needed the probabilistic boosting (they have no exact low-degree polynomial — `…ACC0ExactDegreeNoGo`).
`MOD₂` (parity) is different: over `F₂` it **is** the linear form `⊕_i x_i = ∑_i X_i`, an *exact* degree-1 polynomial.
So the `MOD₂` gate composes into the framework with degree `d = 1` and error `e = 0` — its approximant is exact.

## What is proved (clean axioms, no `sorry`)

* `parityBool` — the `MOD₂`/parity gate (`⊕_i x_i = 1`).
* `mod2_exact_eval` — `eval (linForm univ) x = boolToZMod 2 (parityBool x)`: the degree-1 linear form computes parity
  *exactly*.
* `mod2_totalDegree_le` (`≤ 1`) and **`mod2_mem_monoAND_span`** — `MOD₂` lies in the degree-`≤1` monomial-`AND` span,
  exactly.

## Honest scope — `MOD₂` only, and why composite `MOD_m` is the real barrier

This handles `MOD₂` (so `AC⁰[2]` = `AC⁰` + parity).  It does **not** extend to general `MOD_m`.  The Razborov–Smolensky
polynomial method works over `F_p` for **prime-power** moduli (a `MOD_{p^e}` gate has an exact / low-degree `F_p`
representation via Fermat).  For **composite** `m` with two distinct prime factors (e.g. `MOD₆`), there is *no* known
low-degree polynomial representation over any single field — this is exactly why `ACC⁰` lower bounds are hard, and why
the only known result (`NEXP ⊄ ACC⁰`, Williams) uses a different, algorithmic method, not the polynomial method.  So
the `MOD` part of this BT front half genuinely stops at prime-power moduli; composite-`MOD` `ACC⁰` is the open barrier,
**Wall 1** in its strongest form.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md` and
`WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0Mod2Exact

open scoped Classical
open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0RSToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0ProbabilisticForm
open PallLean.Paper93.DeepMath.PathB.ACC0BasisBridge

variable {m : ℕ}

/-- The **`MOD₂` (parity) gate**: `⊕_i x_i = 1`. -/
def parityBool (x : Fin m → Bool) : Bool := decide (pv x Finset.univ = 1)

/-- **`MOD₂` is computed *exactly* by the degree-1 linear form (proved).** -/
theorem mod2_exact_eval (x : Fin m → Bool) :
    eval (fun i => boolToZMod 2 (x i)) (linForm Finset.univ) = boolToZMod 2 (parityBool x) := by
  rw [eval_linForm]
  unfold parityBool
  exact (by decide : ∀ a : ZMod 2, a = boolToZMod 2 (decide (a = 1))) (pv x Finset.univ)

/-- The `MOD₂` linear form has total degree `≤ 1` (proved). -/
theorem mod2_totalDegree_le : (linForm (Finset.univ : Finset (Fin m))).totalDegree ≤ 1 :=
  linForm_totalDegree_le (Finset.univ : Finset (Fin m))

/-- **`MOD₂` lies in the degree-`≤1` monomial-`AND` span, exactly (proved).** -/
theorem mod2_mem_monoAND_span :
    (fun x : Fin m → Bool => boolToZMod 2 (parityBool x))
      ∈ Submodule.span (ZMod 2)
        (Set.range (fun S : {S // S ∈ lowDegMonomials m 1} =>
          fun x : Fin m → Bool => if monoAND S.1 x then (1 : ZMod 2) else 0)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkey := lowDegPolyEval_mem_monoAND_span 2 1 (linForm (Finset.univ : Finset (Fin m)))
    mod2_totalDegree_le
  have hfun : (fun x : Fin m → Bool => boolToZMod 2 (parityBool x))
      = (fun x : Fin m → Bool => eval (fun i => boolToZMod 2 (x i)) (linForm Finset.univ)) := by
    funext x
    exact (mod2_exact_eval x).symm
  rw [hfun]
  exact hkey

end PallLean.Paper93.DeepMath.PathB.ACC0Mod2Exact

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod2Exact.mod2_exact_eval
#print axioms PallLean.Paper93.DeepMath.PathB.ACC0Mod2Exact.mod2_mem_monoAND_span
