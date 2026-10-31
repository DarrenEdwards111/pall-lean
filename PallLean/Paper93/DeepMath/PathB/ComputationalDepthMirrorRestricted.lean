import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSATResonatesReadOnce

/-!
# The mirror transform, found in a restricted case: subformula projection (read-once)

`MirrorDuality` left the wall as: the mirror `Π★` is not known — its existence `⟺` the separation.  But
in a **restricted case** the mirror *can* be written down concretely.  In the read-once / formula model,
`Π★` is the **subformula projection** — project a formula to a designated child — and it is provably
**rank-monotone** for the gate count.  That is a real, explicit `Π★`.

## What is proved

* **`piStar` / `piStar_monotone` (proved)** — the concrete mirror `Π★ = ` (left) subformula projection is
  gate-monotone: `gates(Π★ t) ≤ gates t`.  Projecting to a sub-part never raises the gate count — exactly
  the `Π★` monotonicity the mirror needs.
* **`mirror_transfers_lower_bound` (proved)** — the mirror in action: if `Π★ comp = witness` and the
  witness has a lower bound (`high ≤ gates witness`), that bound **reflects onto the compilation**:
  `high ≤ gates comp`.  The concrete mirror carries hardness from witness to compilation.
* **`concrete_mirror_readonce` (proved)** — a fully explicit instance: `Π★` reflects the read-once
  resonance tower's `2^d` bound onto a larger formula.  `2^d ≤ gates(node (tower d) base)` — a real bound,
  obtained *through* the mirror.

## Honest scope — what this is, and the gap

This is a genuine `Π★`: a concrete, rank-monotone transform that reflects a witness's lower bound onto a
compilation, in the read-once model.  The mirror mechanism *works*, explicitly, when the model is
restricted to formulas (gate count, subformula projection).

The gap to the full God-Move: the real `Π★` must reflect a **P-compilation of SAT** onto the **NP-witness**
in the **general circuit** model, rank-monotone — and there its existence `⟺` the separation
(`DischargePiStar`), the missing Lorentz.  The read-once mirror is a real instance of the *shape*
(monotone projection reflecting a bound), but the general-model mirror that would reflect P-easiness onto
SAT-hardness is the wall.

So: **the mirror transform is found — concretely — in the read-once case.**  The general-circuit mirror,
whose existence is the separation, is not.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.MirrorRestricted

open PallLean.Paper93.DeepMath.PathB.SupportLens
open PallLean.Paper93.DeepMath.PathB.Resonance
open PallLean.Paper93.DeepMath.PathB.SATResonatesReadOnce

/-- The concrete mirror `Π★`: project a formula to its left subformula (identity on variables). -/
def piStar {n : ℕ} : F n → F n
  | F.var i => F.var i
  | F.node a _ => a

/-- **The mirror is rank-monotone (proved).**  `gates(Π★ t) ≤ gates t`: projecting to a sub-part never
raises the gate count — the `Π★` monotonicity the mirror clash needs. -/
theorem piStar_monotone {n : ℕ} (t : F n) : gates (piStar t) ≤ gates t := by
  cases t with
  | var i => simp [piStar]
  | node a b => simp only [piStar, gates]; omega

/-- **The mirror reflects a lower bound (proved).**  If `Π★ comp = witness` and the witness is hard
(`high ≤ gates witness`), the bound reflects onto the compilation: `high ≤ gates comp`.  The concrete
mirror carries hardness from witness to compilation. -/
theorem mirror_transfers_lower_bound {n : ℕ} (comp witness : F n) (high : ℕ)
    (mirror : piStar comp = witness) (witness_high : high ≤ gates witness) :
    high ≤ gates comp := by
  calc high ≤ gates witness := witness_high
    _ = gates (piStar comp) := by rw [mirror]
    _ ≤ gates comp := piStar_monotone comp

/-- **A fully explicit mirror instance (proved).**  `Π★` reflects the read-once resonance tower's `2^d`
bound onto the larger formula `node (tower d) base`: `2^d ≤ gates(node (tower d) base)`.  The mirror is
found, concretely, and it carries the bound. -/
theorem concrete_mirror_readonce {n : ℕ} (base : F n) (hbase : 1 ≤ gates base) (d : ℕ) :
    2 ^ d ≤ gates (F.node (harmonics sq base d) base) :=
  mirror_transfers_lower_bound _ (harmonics sq base d) _ rfl (sat_resonates_readonce base hbase d)

end PallLean.Paper93.DeepMath.PathB.MirrorRestricted

#print axioms PallLean.Paper93.DeepMath.PathB.MirrorRestricted.piStar_monotone
#print axioms PallLean.Paper93.DeepMath.PathB.MirrorRestricted.mirror_transfers_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.MirrorRestricted.concrete_mirror_readonce
