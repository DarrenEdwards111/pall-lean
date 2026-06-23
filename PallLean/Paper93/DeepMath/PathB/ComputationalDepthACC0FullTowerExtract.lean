import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0FullTowerValue
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0TodaExtract

/-!
# Exact extraction for the full `MOD`/`AND`/`OR` tower — first cash-out piece (PROVED)

The cash-out begins by turning the full-tower value congruence (`ACC0FullTowerValue.full_tower`:
`p^{2^k} ∣ (vrep t − vval t)`) into an **exact equality over the common modulus** `ZMod (p^{2^k})`:

  `full_tower_extract` — `(vrep t : ZMod (p^{2^k})) = (vval t : ZMod (p^{2^k}))` — over the common
  modulus, the full tower's Toda/product/De-Morgan representation **is** its Boolean value, with no
  residual error, at arbitrary depth.

With a **uniform `k`** chosen so `p^{2^k} >` the global count (the exact-quasipoly choice), this is the
exact `{0,1}` value of the whole ACC⁰[p] circuit, computed by a polylog-degree (`(max w (3^k(p−1)))^depth`,
by `ACC0FullTowerDegree`) polynomial over `ZMod (p^{2^k})`.  This is the first concrete step of the
Beigel–Tarui cash-out: lifting `ACC0TodaExtract.todaMod_extract` (single gate) to the entire tower.

## What is proved (clean axioms, no `sorry`)

* `full_tower_extract` — the full tower's exact value over `ZMod (p^{2^k})`.

## Honest scope

The exact `ZMod (p^{2^k})` extraction for the full tower — the rep equals the value over the common
modulus.  The remaining cash-out: choosing `2^k` against the global count (so the integer value lands in
`{0,1}` and the support is quasipoly), the `SYM∘AND` form, and the `NEXP ⊄ ACC⁰` contradiction.
Williams-strength, **not** built.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0FullTowerExtract

open PallLean.Paper93.DeepMath.PathB.ACC0FullTowerValue (FMTower vrep vval full_tower)
open PallLean.Paper93.DeepMath.PathB.ACC0TodaExtract (toda_extract)

/-- **Full-tower exact extraction (proved): `(vrep t : ZMod (p^{2^k})) = (vval t : ZMod (p^{2^k}))`.**
Over the common modulus, the full `MOD`/`AND`/`OR` tower's representation equals its Boolean value
exactly. -/
theorem full_tower_extract (p k : ℕ) [Fact p.Prime] (t : FMTower) :
    ((vrep p k t : ℤ) : ZMod (p ^ (2 ^ k))) = ((vval p t : ℤ) : ZMod (p ^ (2 ^ k))) := by
  refine toda_extract ?_
  have h := full_tower p k t
  push_cast
  push_cast at h
  convert h using 2

/-!
**Full-tower exact extraction proved.**  Over `ZMod (p^{2^k})` the full tower's rep is its Boolean value
exactly — the first concrete step of the cash-out.  Choosing `2^k` against the global count, the
`SYM∘AND` form, and the `NEXP ⊄ ACC⁰` contradiction remain.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

end PallLean.Paper93.DeepMath.PathB.ACC0FullTowerExtract

#print axioms PallLean.Paper93.DeepMath.PathB.ACC0FullTowerExtract.full_tower_extract
