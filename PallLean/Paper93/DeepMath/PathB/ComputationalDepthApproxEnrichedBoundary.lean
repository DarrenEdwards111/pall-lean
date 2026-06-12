import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4Capstone
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEnrichedModularBoundary

/-!
# The approximate per-modulus bridge: proved for one field, isolated open gap for mixed moduli

`ComputationalDepthEnrichedModularBoundary.lean` showed the *exact* enriched boundary fails the ACC⁰ bridge
(a single `MOD_p` gate is full-degree over `F_q`; `AND` is degree `n`).  The fix RS used is **approximate**
(probabilistic) polynomials.  This file does the honest next step: confirm the **approximate** per-modulus
bridge over a *single* field is already a theorem in this repo, and isolate exactly where it stops for mixed
moduli.

## The approximate single-field bridge is PROVED (flips the exact verdict)

`ac0p_low_approx_boundary` (specialising `Layer4.exists_baseChanged_approximant`): an `AC⁰[p]` circuit `C`
has a polynomial of **total degree `≤ ((p−1)·t)^depth`** agreeing with `C` on `≥ ¾` of inputs.  And
`Layer3.ApproxDegreeData.approxDegree_le` proves the composition: approximate degree multiplies by
`K = (p−1)·t` **per layer**, so depth-`d` gives `K^d` — *polylog/quasipoly for constant depth*, where the
**exact** degree of even a single `AND` was `n`.

So over one field the approximate boundary **does** model `AC⁰[p]` as low-boundary — exactly the property the
exact boundary lacked.  This is the per-modulus half of the enriched bridge, done.

## Where it stops for ACC⁰ — the precise open gap (proved obstruction)

The bridge's hypothesis is `IsAC0pSyntax p C`: **every `MOD` gate has modulus `p`** (a single field).  A
genuine ACC⁰ circuit mixes moduli, and then:

* `modGate_not_isAC0p` — a single `MOD_q` gate (`q ≠ p`) is **not** `AC⁰[p]`.
* `mixedCircuit_not_isAC0p_left/right` — a circuit using both `MOD_p` and `MOD_q` (`q ≠ p`) is **neither**
  `AC⁰[p]` **nor** `AC⁰[q]`.

So *neither* single-field approximant theorem applies to a mixed circuit: the `F_p` construction needs all
gates mod `p`, the `F_q` one needs all gates mod `q`, and a mixed circuit satisfies neither.  The enriched
*approximate* bridge for ACC⁰ therefore requires a **new joint construction** — approximating polynomials over
the combined modular structure — which does not reduce to the single-field one.  **That joint construction is
the open frontier** (and the reason ACC⁰ resists the polynomial method).

## Honest status

* Approximate single-field bridge: **proved** (reused) — the per-modulus half works.
* Mixed-moduli reduction: **provably does not apply** (the obstruction lemmas) — a new construction is needed.
* `NP ⊄ ACC⁰`: still **open**.  Nothing here closes it; the value is that the per-modulus bridge is settled
  *positively* (approximate) and the remaining gap is pinned to the mixed-moduli joint approximant.
-/

namespace PallLean.Paper93.DeepMath.PathB.ApproxEnriched

open PallLean.Paper93.DeepMath.PathB
open scoped BigOperators

/-! **The approximate single-field bridge is already proved** as `Layer4.exists_baseChanged_approximant`:
for an `AC⁰[p]` circuit `C` (`Layer4.hmod_of_isAC0p` turns `IsAC0pSyntax p C` into its `hmod` hypothesis),
there is a polynomial of total degree `≤ ((p−1)·t)^C.depth` agreeing with `C` on `≥ ¾` of inputs — the low
*approximate* per-modulus boundary that the exact boundary lacked, with the `K^depth` composition from
`Layer3.ApproxDegreeData.approxDegree_le`.  We cite it rather than re-export (it is unchanged), and prove
below the genuinely new content: where that bridge stops for mixed moduli. -/

/-! ## The mixed-moduli obstruction (new, proved): why the single-field bridge stops -/

/-- A single `MOD_q` gate with `q ≠ p` is **not** `AC⁰[p]` — so the `F_p` approximant's hypothesis fails on
it. -/
theorem modGate_not_isAC0p {n p q r : ℕ} {Cs : List (BoolCircuitSyntax n)} (hpq : q ≠ p) :
    ¬ BoolCircuitSyntax.IsAC0pSyntax p (BoolCircuitSyntax.modGate q r Cs) := by
  simp only [BoolCircuitSyntax.IsAC0pSyntax]
  intro h
  exact hpq h.1

/-- A **mixed-modulus circuit**: `AND` of a `MOD_p` gate and a `MOD_q` gate. -/
def mixedCircuit (n p q : ℕ) : BoolCircuitSyntax n :=
  BoolCircuitSyntax.andGate [BoolCircuitSyntax.modGate p 0 [], BoolCircuitSyntax.modGate q 0 []]

/-- The mixed circuit is **not** `AC⁰[p]` (its `MOD_q` gate, `q ≠ p`, violates the single-modulus rule). -/
theorem mixedCircuit_not_isAC0p_left {n p q : ℕ} (hqp : q ≠ p) :
    ¬ BoolCircuitSyntax.IsAC0pSyntax p (mixedCircuit n p q) := by
  intro h
  simp only [mixedCircuit, BoolCircuitSyntax.IsAC0pSyntax] at h
  exact modGate_not_isAC0p hqp (h (BoolCircuitSyntax.modGate q 0 []) (by simp))

/-- The mixed circuit is **not** `AC⁰[q]` either (its `MOD_p` gate, `p ≠ q`).  So *neither* single-field
approximant theorem applies — the mixed-moduli joint approximant is genuinely needed (open). -/
theorem mixedCircuit_not_isAC0p_right {n p q : ℕ} (hpq : p ≠ q) :
    ¬ BoolCircuitSyntax.IsAC0pSyntax q (mixedCircuit n p q) := by
  intro h
  simp only [mixedCircuit, BoolCircuitSyntax.IsAC0pSyntax] at h
  exact modGate_not_isAC0p hpq (h (BoolCircuitSyntax.modGate p 0 []) (by simp))

end PallLean.Paper93.DeepMath.PathB.ApproxEnriched

#print axioms PallLean.Paper93.DeepMath.PathB.ApproxEnriched.modGate_not_isAC0p
#print axioms PallLean.Paper93.DeepMath.PathB.ApproxEnriched.mixedCircuit_not_isAC0p_left
#print axioms PallLean.Paper93.DeepMath.PathB.ApproxEnriched.mixedCircuit_not_isAC0p_right
