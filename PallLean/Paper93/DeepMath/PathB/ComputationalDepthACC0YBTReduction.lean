import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RSToSymAnd
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3AC0pPoly

/-!
# The YBT reduction core: `AC⁰[p]` circuit → `SYM∘AND` bottom span (conditional on the degree bound)

This wires the **exact** circuit→polynomial reduction (Layer3 `toPoly_eval_AC0`: an `AC⁰[p]` circuit `c` satisfies
`eval (embed x) (toPoly p c) = boolToZMod p (c.eval x)` exactly) into the `SYM∘AND` world via the bridge
`squarefreeEvalMonomial_eq_monoAND` (`lowDegPolyEval_mem_monoAND_span`).  The result is the reduction core:

```
(toPoly p c).totalDegree ≤ D   ⇒   (x ↦ boolToZMod p (c.eval x)) ∈ ZMod p-span of degree-≤D monomial-AND gates.
```

i.e. once the circuit's exact polynomial has degree `≤ D`, its (embedded) Boolean function lies in the span of the
`≤ ∑_{i≤D} C(n,i)` monomial-`AND` indicators — the `SYM∘AND` bottom layer.  Combined with the cash-out
(`weightedGateCount_cast_eq` + `weightedSym_searchable`), a circuit meeting the degree bound is SAT-searchable.

## What the degree bound is — and why it is the wall

`toPoly` is **exact** but its degree is **uncontrolled**: an unbounded fan-in `∧` becomes a *product* of its inputs'
polynomials, so the degree grows with fan-in (and with depth, multiplicatively).  The whole content of
Yao–Beigel–Tarui / Razborov–Smolensky is getting the degree down to **polylog** — and that step is **approximate**
(`toAgree`, agreeing on a `1-ε` fraction), not the exact `toPoly`.  So `(toPoly p c).totalDegree ≤ D` holds only for
shallow/small circuits; the *exact* polylog-degree form for arbitrary `AC⁰[p]` is the open structural wall.

## What is proved (clean axioms, no `sorry`)

* `acc0p_circuit_in_monoAND_span` — `IsAC0Syntax c` and `(toPoly p c).totalDegree ≤ D` ⇒ `c`'s embedded eval lies in
  the `ZMod p`-span of the degree-`≤D` monomial-`AND` indicators (the `SYM∘AND` bottom layer).

## Honest scope

This is the EXACT reduction (Layer3) bridged to the `SYM∘AND`-bottom span (mine) — the genuine structural core,
**conditional on the degree bound**.  It does **not** supply the degree bound for arbitrary `AC⁰[p]` (that is the
RS/YBT analytic content, and only *approximately* via `toAgree`).  Extracting the explicit `ZMod p`-combination from
span membership and feeding `weightedSym_searchable` is the remaining mechanical glue; the degree bound is the wall.
Still the cell/observer model; nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See `ACC_THEOREM_MAP.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0YBTReduction

open scoped Classical
open MvPolynomial
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Layer3
open PallLean.Paper93.DeepMath.PathB.ACC0PolyToSymAnd
open PallLean.Paper93.DeepMath.PathB.ACC0RSToSymAnd

variable {n : ℕ}

/-- **The YBT reduction core (proved, conditional on the degree bound).**  An `AC⁰[p]` circuit whose exact polynomial
`toPoly p c` has degree `≤ D` has its (embedded) Boolean function in the `ZMod p`-span of the degree-`≤D`
monomial-`AND` indicators — the `SYM∘AND` bottom layer.  (The degree bound is the open RS/YBT content; `toPoly` itself
is exact but high-degree.) -/
theorem acc0p_circuit_in_monoAND_span (p : ℕ) [Fact p.Prime] (D : ℕ) (c : BoolCircuitSyntax n)
    (hc : BoolCircuitSyntax.IsAC0Syntax c) (hdeg : (toPoly p c).totalDegree ≤ D) :
    (fun x : Fin n → Bool => boolToZMod p (c.eval x))
      ∈ Submodule.span (ZMod p)
        (Set.range (fun S : {S // S ∈ lowDegMonomials n D} =>
          fun x : Fin n → Bool => if monoAND S.1 x then (1 : ZMod p) else 0)) := by
  have h1 : (fun x : Fin n → Bool => boolToZMod p (c.eval x))
      = (fun x : Fin n → Bool => eval (fun i => boolToZMod p (x i)) (toPoly p c)) := by
    funext x
    exact (toPoly_eval_AC0 p x c hc).symm
  rw [h1]
  exact lowDegPolyEval_mem_monoAND_span p D (toPoly p c) hdeg

end PallLean.Paper93.DeepMath.PathB.ACC0YBTReduction

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0YBTReduction.acc0p_circuit_in_monoAND_span
