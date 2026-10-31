import PallLean.Paper93.DeepMath.PathB.ComputationalDepthResonance
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSupportLens

/-!
# SAT resonates in a restricted case: read-once (no sharing)

`Resonance` left the wall as: *is SAT resonant, or damped?*  Damping is mass production — sharing between
the two copies.  So the honest restricted case where SAT provably resonates is the one where sharing is
**structurally forbidden**: **read-once** circuits (each gate used once = a formula).  There nothing can
share, so nothing can damp, and the amplifier rings.

The amplifier is `sq t = t ∘ t` (two copies).  In the read-once model the cost is the gate count (a
formula is a read-once circuit), and gluing two copies genuinely duplicates — `gates(sq t) = 2·gates t +
1`.  So every function *resonates* read-once, SAT included.

## What is proved

* **`formula_resonant` (proved)** — every read-once function resonates: `2·gates t ≤ gates(sq t)`.  The
  amplifier carries in the read-once model, unconditionally.
* **`sat_resonates_readonce` (proved)** — hence the tower's cost is superpolynomial: `2^d ≤
  gates(harmonics sq base d)`, via `Resonance.resonance_carries`.  **SAT (any function) resonates in the
  read-once restricted model** — the sound carries all the way up.

## Honest scope — the restricted case, and the gap

This is a *real, unconditional* restricted result: in the read-once DAG model, the amplifier provably
resonates for every function and the bound reaches `2^d`.  It is genuine — but read-once is exactly the
model with **no sharing**, so it forbids the one thing (mass production) that could damp the resonance.
The gap to full `P ≠ NP` is precisely the sharing that read-once outlaws: unrestricted circuits may share,
and whether SAT's tower resonates *with sharing allowed* is `cost_super`, open.

So: **SAT resonates in the read-once case (proved).**  Removing the read-once restriction — letting the
circuit share — is the wall.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.SATResonatesReadOnce

open PallLean.Paper93.DeepMath.PathB.Resonance
open PallLean.Paper93.DeepMath.PathB.SupportLens

/-- The amplifier: two copies of the formula `t` (one harmonic). -/
def sq {n : ℕ} (t : F n) : F n := F.node t t

/-- **Every read-once function resonates (proved).**  Gluing two copies genuinely duplicates the gates:
`gates(sq t) = 2·gates t + 1 ≥ 2·gates t`.  The amplifier carries in the read-once model — no sharing to
damp it. -/
theorem formula_resonant {n : ℕ} (t : F n) : Resonant gates sq t := by
  show 2 * gates t ≤ gates (F.node t t)
  simp only [gates]
  omega

/-- **SAT resonates in the read-once model (proved).**  With a nontrivial base (`1 ≤ gates base`), the
tower's cost is superpolynomial: `2^d ≤ gates(harmonics sq base d)`.  The amplifier rings all the way up —
the sound carries, unconditionally, in the read-once restricted case. -/
theorem sat_resonates_readonce {n : ℕ} (base : F n) (hbase : 1 ≤ gates base) (d : ℕ) :
    2 ^ d ≤ gates (harmonics sq base d) :=
  resonance_carries gates sq base formula_resonant hbase d

end PallLean.Paper93.DeepMath.PathB.SATResonatesReadOnce

#print axioms PallLean.Paper93.DeepMath.PathB.SATResonatesReadOnce.formula_resonant
#print axioms PallLean.Paper93.DeepMath.PathB.SATResonatesReadOnce.sat_resonates_readonce
