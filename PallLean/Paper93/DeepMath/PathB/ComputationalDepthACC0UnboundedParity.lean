import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer3Smolensky
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthLayer4Assembly

/-!
# Bridge (model upgrade) — PARITY needs super-polynomial size in *unbounded-fan-in* `AC⁰[p]` (proved)

The earlier `ACC0Circuit` development uses **binary** `AND`/`OR`, so its "constant depth" means bounded-fan-in formulas
(≤ `2^d` leaves) — a weaker model.  This brick states the *real* Razborov–Smolensky size lower bound in the **unbounded-fan-in**
model `BoolCircuitSyntax` (`List`-based `andGate`/`orGate`, the model of `Layer3`/`Layer4`): for an `AC⁰[p]` circuit
(`IsAC0pSyntax`) of depth `d` computing `PARITY`, the number of distinct subcircuits exceeds `p^t / 4` whenever the window
`8((p−1)t)^d)² ≤ m` holds — i.e. `PARITY` requires **super-polynomial size** in genuine constant-depth `AC⁰[p]`.

This composes the repo's clean `Layer3.parity_function_lower_bound` (the unbounded-fan-in RS bound) with
`Layer4.hmod_of_isAC0p` (the bridge from the structural `IsAC0pSyntax` predicate to the "all `MOD` gates have modulus `p`"
side condition).  It is the genuine Håstad/RS theorem in the real model, upgrading the binary-fan-in `parity_not_ac0`.

## What is proved (clean axioms, no `sorry`)

* **`parity_superpoly_ac0p`** (PROVED) — an unbounded-fan-in `AC⁰[p]` circuit computing `PARITY` at depth `d` has
  `p^t < 4·#{distinct subcircuits}` (in the RS window).

## Honest scope

This is the real (unbounded-fan-in) `PARITY ∉ poly-size AC⁰[p]` size lower bound.  The **Williams cash-out** (`NEXP ⊄ ACC⁰`)
is a different, P≠NP-strength theorem and remains **open** / not faked.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  See
`ACC_THEOREM_MAP.md`, `WHAT_IS_PROVED.md`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0UnboundedParity

open PallLean.Paper93.DeepMath.PathB.Layer3 (subcircuits parity_function_lower_bound)
open PallLean.Paper93.DeepMath.PathB.Layer4 (hmod_of_isAC0p)

open Classical in
/-- **PARITY needs super-polynomial size in unbounded-fan-in `AC⁰[p]` (PROVED).**  Any `AC⁰[p]` circuit (`IsAC0pSyntax`) of
depth `≤ d` computing `PARITY` has `p^t < 4·(subcircuits).toFinset.card` whenever `8((p−1)t)^d)² ≤ m` — the real RS size
lower bound in the genuine (unbounded-fan-in) model. -/
theorem parity_superpoly_ac0p (p : ℕ) [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0) {m d : ℕ}
    (Cir : BoolCircuitSyntax (2 * m + 1)) (hac : BoolCircuitSyntax.IsAC0pSyntax p Cir)
    (hd : Cir.depth ≤ d) (t : ℕ) (ht1 : 1 ≤ t)
    (hparity : ∀ x : Fin (2 * m + 1) → Bool,
      Cir.eval x = decide (Odd (Finset.univ.filter (fun i => x i = true)).card))
    (hm : 8 * (((p - 1) * t) ^ d) ^ 2 ≤ m) :
    p ^ t < 4 * (subcircuits Cir).toFinset.card :=
  parity_function_lower_bound p hp2 Cir hd t ht1 hparity (hmod_of_isAC0p Cir hac) hm

/-!
**PARITY ∉ poly-size unbounded-fan-in `AC⁰[p]`, proved.**  The real Razborov–Smolensky size lower bound in the genuine
constant-depth model (`List`-based unbounded-fan-in gates) — upgrading the binary-fan-in `parity_not_ac0`.  Remaining (open,
not faked): the Williams cash-out to `NEXP ⊄ ACC⁰`.  Not `NEXP ⊄ ACC⁰`, not `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0UnboundedParity

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0UnboundedParity.parity_superpoly_ac0p
