import PallLean.Paper93.DeepMath.PathB.ComputationalDepthConservedChargeSpec

/-!
# Can the God-Move gauge break C3 via the N-Frame Lagrangian? No — it presupposes C3

Darren's move: use the God-Move gauge, fuelled by the N-Frame Lagrangian, to *break* C3
(`cbudget(SAT)` superpoly = `cost_super`).  This file machine-checks why that route is closed: the gauge
**presupposes** C3, so it cannot prove it, and the Lagrangian's fuel does not break the circle.

## The circularity

The God-Move gauge *is* a conserved charge (a separating measure).  Its very definition **carries C3** as
a required field (`high_on_sat`).  So:

* **`gauge_presupposes_C3` (proved)** — having the gauge yields C3 for free (`high ≤ Q sat`); the gauge
  cannot *prove* C3 because constructing it already **requires** C3.  Conversely `MinFloorCharge`
  (`floor_gives_conserved_charge`) builds the gauge *from* C3.  So **gauge ⟺ C3**: "break C3 via the
  gauge" is "prove C3 from C3."

## The Lagrangian doesn't break the circle

* **`efficient_gauge_barriered` (proved)** — an efficiently-computable (`L_eff`) gauge is a natural
  property and is barriered (crypto).  So the only fuel the Lagrangian can offer is `L_H`.
* By `NFrameChargeNoether` the `L_H` current is hypercomputational, and by `LevelSegregation` an
  outside-the-question resource cannot supply the **in-model** C3.  So the Lagrangian fuel is either
  barriered (`L_eff`) or outside the question (`L_H`) — neither breaks C3.

## Honest scope

Proved: the gauge presupposes C3 (so it cannot prove it), and an efficient gauge is barriered.  Together
with the earlier bricks, the "gauge + Lagrangian breaks C3" route is **circular** (gauge ⟺ C3) and its
only non-barriered fuel is **outside the model**.  C3 = `cost_super` remains the open in-model wall.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.GaugeCircularity

open PallLean.Paper93.DeepMath.PathB.ConservedChargeSpec

variable {Fn Rep : Type} {computes : Rep → Fn → Prop} {rrank : Rep → ℕ}
  {Easy : Fn → Prop} {sat : Fn}

/-- **The gauge presupposes C3 (proved).**  A conserved charge (the God-Move gauge) carries C3
(`high_on_sat`) as a required field: having the gauge yields `high ≤ Q sat` — C3 — for free.  So the gauge
cannot be used to *prove* C3; constructing it already requires C3.  With `MinFloorCharge`'s converse
(`C3 → gauge`), this is `gauge ⟺ C3`: breaking C3 via the gauge is proving C3 from C3. -/
theorem gauge_presupposes_C3 (cc : ConservedCharge Fn Rep computes rrank Easy sat) :
    cc.high ≤ cc.Q sat :=
  cc.high_on_sat

/-- **An efficient (`L_eff`) gauge is barriered (proved).**  If the gauge's charge is efficiently
computable, the natural-proofs barrier rules it out.  So the Lagrangian's computable current cannot be
the gauge; only the hypercomputational `L_H` current is left — which is outside the in-model question. -/
theorem efficient_gauge_barriered {Efficient : (Fn → ℕ) → Prop} {Crypto : Prop}
    (barrier : ChargeBarrier Fn Rep computes rrank Easy sat Efficient Crypto) (hC : Crypto)
    (cc : ConservedCharge Fn Rep computes rrank Easy sat) (heff : Efficient cc.Q) : False :=
  charge_forces_non_natural barrier hC cc heff

end PallLean.Paper93.DeepMath.PathB.GaugeCircularity

#print axioms PallLean.Paper93.DeepMath.PathB.GaugeCircularity.gauge_presupposes_C3
#print axioms PallLean.Paper93.DeepMath.PathB.GaugeCircularity.efficient_gauge_barriered
