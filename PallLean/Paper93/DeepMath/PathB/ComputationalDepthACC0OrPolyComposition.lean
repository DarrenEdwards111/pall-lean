import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0OrPolyPackage
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DepthDegree

/-!
# Brick (approx wiring) — depth-`d` composition of the approximate-`OR` keeps degree `≤ (t(p-1))^{d+1}` (proved)

The degree side of the Razborov–Smolensky approximate-polynomial wiring through a circuit.  Each `OR` gate is approximated by
`orPoly` of degree `t(p-1)` (Brick OR-package).  Composing such approximators across depth `d` (iterated substitution, Brick
C-iterate) keeps the total degree at `≤ (t(p-1))^{d+1}`.  For `t = polylog` and constant depth `d`, this is `polylog` — and
the multilinearization bridge then caps the `AND`-terms at `(n+1)^{(t(p-1))^{d+1}}` = quasipolynomial.

This is the approximate analogue of the exact `modp_composition_degree` brick: it shows the *approximate*-`OR` degree composes
under depth exactly as the degree machinery (C-iterate) predicts, instantiated at `orPoly`'s proven per-gate degree.

## What is proved (clean axioms, no `sorry`)

* **`orPoly_composition_degree`** (PROVED) —
  `((bind₁ (fun _ => orPoly p n t a))^[d] (orPoly p n t a)).totalDegree ≤ (t·(p-1))^{d+1}`.

## Honest scope

This is the **degree** bound for a depth-`d` composition of approximate-`OR` gates (the wiring's degree accounting).  It does
**not** carry the per-gate *error* accounting through the recursion (the union bound over gates × inputs giving one globally
good coefficient choice — that combinator is `exists_good_form`), nor assemble the full faithful RS-for-circuits theorem with
`MOD` gates / `composite_BT_degree`.  General YBT remains open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0OrPolyComposition

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ACC0OrPolyPackage (orPoly orPoly_totalDegree_le)
open PallLean.Paper93.DeepMath.PathB.ACC0DepthDegree (totalDegree_bind₁_iterate)

/-- **Depth-`d` composition of the approximate-`OR` has degree `≤ (t(p-1))^{d+1}` (PROVED).** -/
theorem orPoly_composition_degree (p n t d : ℕ) [Fact p.Prime] (a : Fin t → (Fin n → ZMod p)) :
    ((bind₁ (fun _ : Fin n => orPoly p n t a))^[d] (orPoly p n t a)).totalDegree
      ≤ (t * (p - 1)) ^ (d + 1) := by
  calc ((bind₁ (fun _ : Fin n => orPoly p n t a))^[d] (orPoly p n t a)).totalDegree
      ≤ (orPoly p n t a).totalDegree * (t * (p - 1)) ^ d :=
        totalDegree_bind₁_iterate _ (t * (p - 1)) (fun _ => orPoly_totalDegree_le p n t a)
          (orPoly p n t a) d
    _ ≤ (t * (p - 1)) * (t * (p - 1)) ^ d := by gcongr; exact orPoly_totalDegree_le p n t a
    _ = (t * (p - 1)) ^ (d + 1) := by rw [pow_succ]; ring

/-!
**Approximate-degree wiring (degree side), proved.**  Composing the degree-`t(p-1)` approximate-`OR` across depth `d` stays
at degree `≤ (t(p-1))^{d+1}` — polylog for `t` polylog and constant `d`, hence quasipolynomial `AND`-term count via the
bridge.  Remaining (open, not faked): per-gate error accounting through the recursion, `MOD`-gate handling, and the full
`composite_BT_degree`.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0OrPolyComposition

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0OrPolyComposition.orPoly_composition_degree
