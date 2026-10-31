import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PrimeMODMvPoly
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0DepthDegree

/-!
# Brick C∘A.2c — same-prime constant-depth `MOD_p` circuit has bounded degree (proved)

A concrete assembly demonstrating the YBT degree machinery composing end-to-end on a real (restricted) circuit class:
a depth-`(d+1)` *uniform same-prime* `MOD_p` circuit — modelled as `d` iterated substitutions of the single-`MOD_p`
polynomial `modpPoly p n = (∑ᵢ Xᵢ)^{p-1}` (Brick A.2c, degree `≤ p-1`) — has total degree `≤ (p-1)^{d+1}`.

For *constant* depth `d` and *constant* prime `p`, this is a **constant** — so (after multilinearization, where Brick D
caps the monomials at `(n+1)^{(p-1)^{d+1}}`) the circuit has a polynomial-size `SYM∘AND` form.  This is the degree control of
Brick C-iterate (`totalDegree_bind₁_iterate`) instantiated at the proven per-gate degree of Brick A.2c — no socket.

## What is proved (clean axioms, no `sorry`)

* **`modp_composition_degree`** (PROVED) — `((bind₁ (fun _ => modpPoly p n))^[d] (modpPoly p n)).totalDegree ≤ (p-1)^{d+1}`.

## Honest scope

This is the **degree** bound for same-prime, constant-depth `MOD_p` circuits — a clean assembly of two proved bricks.  It
does **not** include the multilinearization step that connects this degree to Brick D's subset count, AND/OR gates (whose
exact degree is the fan-in — needs the approximate RS polynomial), cross-prime nesting, prime-power composition, nor the
`ACC0Circuit`-level `composite_BT_degree`.  General YBT remains open.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0ModpCompositionDegree

open MvPolynomial
open PallLean.Paper93.DeepMath.PathB.ACC0PrimeMODMvPoly (modpPoly modpPoly_totalDegree_le)
open PallLean.Paper93.DeepMath.PathB.ACC0DepthDegree (totalDegree_bind₁_iterate)

/-- **A same-prime depth-`(d+1)` `MOD_p` circuit has degree `≤ (p-1)^{d+1}` (PROVED).** -/
theorem modp_composition_degree (p n d : ℕ) [Fact p.Prime] :
    ((bind₁ (fun _ : Fin n => modpPoly p n))^[d] (modpPoly p n)).totalDegree ≤ (p - 1) ^ (d + 1) := by
  calc ((bind₁ (fun _ : Fin n => modpPoly p n))^[d] (modpPoly p n)).totalDegree
      ≤ (modpPoly p n).totalDegree * (p - 1) ^ d :=
        totalDegree_bind₁_iterate _ (p - 1) (fun _ => modpPoly_totalDegree_le p n) (modpPoly p n) d
    _ ≤ (p - 1) * (p - 1) ^ d := by gcongr; exact modpPoly_totalDegree_le p n
    _ = (p - 1) ^ (d + 1) := by rw [pow_succ]; ring

/-!
**Same-prime constant-depth degree bound, proved.**  Brick C-iterate at Brick A.2c's per-gate degree gives degree
`≤ (p-1)^{d+1}` — constant for constant `d, p`, hence polynomial-size `SYM∘AND` after multilinearization.  The remaining
pieces (multilinearization to Brick D, AND/OR via approximate polynomials, cross-prime, prime-power composition, circuit
assembly) are the genuine open content.  Not a separation.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0ModpCompositionDegree

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0ModpCompositionDegree.modp_composition_degree
