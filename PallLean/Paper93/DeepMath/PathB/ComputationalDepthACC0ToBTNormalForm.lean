import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ApproxBTInstantiation

/-!
# `acc0_to_bt_normal_form` — ACC⁰ circuit ⟹ explicit sparse SYM∘AND normal form (PROVED)

The named bridge from the Beigel–Tarui ingredients to actual ACC⁰.  For **every** constant-depth
`BoolCircuitSyntax` ACC⁰[p] circuit `C`, the RS approximant `toApprox p t R C` is exhibited as an
**explicit sparse sum of AND-monomials** (the SYM∘AND base), with **quasipolynomial support**:

  `acc0_to_bt_normal_form` —
    `toApprox p t R C = ∑_{d ∈ support} monomial d (coeff d)`  (the SYM∘AND form)
    `∧ totalDegree ≤ L^D`                                       (degree polylog)
    `∧ #{monomial supports} ≤ (n+1)^{L^D}`                      (quasipoly support).

So a constant-depth ACC⁰[p] circuit (unbounded fan-in `AND`/`OR`/`NOT`/`MOD_p`) is, after the RS
approximation, a symmetric (sum) gate over `≤ (n+1)^{L^D}` `AND`-monomials of degree `≤ L^D`.  With
RS error parameter `(p−1)·t = L = polylog` and *constant* depth `D`, this is **degree polylog, support
quasipolynomial** — exactly the BT sparse SYM∘AND normal form.

This packages `MvPolynomial.as_sum` (the explicit monomial decomposition = the SYM∘AND structure) with
`approx_endToEnd_BT` (the degree + quasipoly-support bound) into the single named target.

## Honest scope — which route this is

This is the **RS / polynomial-method** route (the `toApprox` *approximant*): the SYM∘AND form computes
the circuit *up to RS error*, which is what the ACC⁰[p] *lower-bound* (correlation) route uses.  It is
**not** the exact Yao–Beigel–Tarui SYM∘AND used by Williams' *algorithmic* `NEXP ⊄ ACC⁰` route — that
needs the *exact* (error-free) symmetric form plus the SAT-speedup and the NTime-hierarchy contradiction
interface, which are genuinely separate and **not** built here.  Nothing here is `NEXP ⊄ ACC⁰` or
`P ≠ NP`.

## What is proved (clean axioms, no `sorry`)

* `acc0_to_bt_normal_form` — explicit sparse SYM∘AND form + degree + quasipoly support for the RS
  approximant of any constant-depth ACC⁰[p] circuit.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ToBTNormalForm

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.Layer3 (toApprox)

variable {n : ℕ}

/-- **ACC⁰[p] ⟹ sparse SYM∘AND normal form (RS approximant).**  Every constant-depth
`BoolCircuitSyntax` ACC⁰[p] circuit's RS approximant is an explicit sum of `AND`-monomials, of total
degree `≤ L^D`, with `≤ (n+1)^{L^D}` distinct monomial supports — degree polylog, support quasipoly
for constant depth. -/
theorem acc0_to_bt_normal_form (p t : ℕ) [Fact p.Prime] (ht : 1 ≤ t)
    (R : (k : ℕ) → Fin t → Fin k → ZMod p) (C : BoolCircuitSyntax n) (L D : ℕ)
    (hL : 1 ≤ L) (hK : (p - 1) * t ≤ L) (hdepth : C.depth ≤ D) :
    toApprox p t R C
        = ∑ d ∈ (toApprox p t R C).support, monomial d ((toApprox p t R C).coeff d)
      ∧ (toApprox p t R C).totalDegree ≤ L ^ D
      ∧ ((toApprox p t R C).support.image (fun d => d.support)).card ≤ (n + 1) ^ (L ^ D) :=
  ⟨MvPolynomial.as_sum _,
    ACC0ApproxBTInstantiation.approx_endToEnd_BT p t ht R C L D hL hK hdepth⟩

/-!
**ACC⁰[p] ⟹ sparse SYM∘AND normal form proved.**  Explicit monomial-sum (the SYM∘AND base) + degree
`≤ L^D` + quasipoly support `≤ (n+1)^{L^D}`, for the RS approximant of any constant-depth ACC⁰[p]
circuit.  RS / lower-bound route; the exact Williams SYM∘AND + SAT speedup + NTime-hierarchy interface
are separate and not built.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ToBTNormalForm

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ToBTNormalForm.acc0_to_bt_normal_form
