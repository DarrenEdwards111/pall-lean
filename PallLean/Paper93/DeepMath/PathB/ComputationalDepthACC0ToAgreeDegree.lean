import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RSToSymAnd
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Smolensky

/-!
# The `toAgree` approximant lands in the bounded `SYM∘AND` span — degree bound discharged

`…ACC0YBTReduction` showed the *exact* polynomial `toPoly` lands in the monomial-`AND` span **only conditional** on a
degree bound — which `toPoly` does not satisfy (it is exact, hence high-degree).  The Razborov–Smolensky **approximant**
`toAgree` is the fix: Layer3's `toAgree_totalDegree_le` *proves* `deg(toAgree p t R C) ≤ ((p-1)·t)^{depth C}`, so the
degree bound is **discharged, not assumed**.  Feeding it into `lowDegPolyEval_mem_monoAND_span` gives, unconditionally:

```
(x ↦ eval (embed x) (toAgree p t R C))  ∈  ZMod p-span of degree-≤((p-1)t)^{depth} monomial-AND gates.
```

So the approximant is genuinely a bounded `SYM∘AND`: for constant depth and `t` polylog, the degree `((p-1)t)^{depth}`
is polylog and the gate count `∑_{i≤D} C(n,i)` is **quasipolynomial** — the YBT size, for the approximant.

## What is proved (clean axioms, no `sorry`)

* `acc0p_toAgree_in_monoAND_span` — `toAgree p t R C`'s cube evaluation lies in the `ZMod p`-span of the
  degree-`≤((p-1)t)^{depth}` monomial-`AND` indicators (degree bound discharged by `toAgree_totalDegree_le`).

## Honest scope

The degree bound is genuinely discharged here (the difference from the conditional `…ACC0YBTReduction`).  The
remaining gap is purely the **approximate vs exact** one: `toAgree` only *agrees with* the circuit on a `1-ε` fraction
(Layer3's approximation), so this is the approximant's `SYM∘AND` form, not the circuit's exact one.  By
`…ACC0ApproxConsequence`, the approximant bounds the circuit's *solution count*, not its SAT.  The exact polylog-degree
`SYM∘AND` for arbitrary `AC⁰[p]` (true YBT) remains the open wall.  Still the cell/observer model; nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ToAgreeDegree

open scoped Classical
open MvPolynomial
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0RSToSymAnd

variable {n : ℕ}

/-- **The RS approximant lands in the bounded `SYM∘AND` span (proved, degree bound discharged).**  Unlike the exact
`toPoly`, `toAgree`'s degree is bounded by `((p-1)·t)^{depth}` (`toAgree_totalDegree_le`), so its Boolean-cube
evaluation lies in the span of the degree-`≤((p-1)t)^{depth}` monomial-`AND` indicators — the `SYM∘AND` bottom layer,
of quasipolynomial size for constant depth and polylog `t`. -/
theorem acc0p_toAgree_in_monoAND_span (p t : ℕ) [Fact p.Prime] (ht : 1 ≤ t)
    (R : (k : ℕ) → Fin t → Fin k → ZMod p) (C : BoolCircuitSyntax n) :
    (fun x : Fin n → Bool => eval (fun i => boolToZMod p (x i)) (toAgree p t R C))
      ∈ Submodule.span (ZMod p)
        (Set.range (fun S : {S // S ∈ lowDegMonomials n (((p - 1) * t) ^ C.depth)} =>
          fun x : Fin n → Bool => if monoAND S.1 x then (1 : ZMod p) else 0)) :=
  lowDegPolyEval_mem_monoAND_span p (((p - 1) * t) ^ C.depth) (toAgree p t R C)
    (toAgree_totalDegree_le p t ht R C)

end PallLean.Paper93.DeepMath.PathB.ACC0ToAgreeDegree

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ToAgreeDegree.acc0p_toAgree_in_monoAND_span
