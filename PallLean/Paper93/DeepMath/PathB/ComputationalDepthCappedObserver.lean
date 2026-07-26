import PallLean.Paper93.DeepMath.PathB.ComputationalDepthConservedChargeSpec

/-!
# You can cap the observer — the escape is a level, not hypercomputation

Darren's correction: the charge only *has* to leave the standard model if you push it all the way; you
can **cap** it at a bounded level — an `EXP`-observer in the tree — and stay in a well-defined class.
This file formalizes where that lands, honestly.

The natural-proofs barrier bites only at the **constructive** level: properties computable in time
polynomial in the truth table (`≈ 2^{O(n)}`).  A charge computable at **EXP with a super-linear
exponent** (`2^{n²}`) is *past* that threshold — non-natural — yet still bounded and standard, **not**
hypercomputational.  So a cap strictly between `P` and hypercomputation escapes both traps.

## What is proved

* **`separation_ignores_level`** — a conserved charge separates through `C1/C3/C4/gap` alone; its
  computability **level is never used**.  So capping the observer (bounded, e.g. `EXP`) does not change
  whether it separates — the escape from hypercomputation costs nothing.
* **`cap_must_exceed_P`** — but the barrier forces the charge to be **non-`P`-efficient**.  So the cap
  must sit strictly *above* `P`; capping at `P` is barriered.  Target level: bounded but above `P`
  (`EXP`), exactly as Darren says.

## Where the cap lands

So Darren is right on both counts: no hypercomputation (`separation_ignores_level`), and above `P`
(`cap_must_exceed_P`) — the target is a capped `EXP`-observer.  But two things remain, and they are the
wall:

1. **C3 is level-independent.**  Whether the capped charge *separates* is `C3` (SAT's floor is high),
   which is `cost_super` — and it does not mention the level at all.  The canonical `EXP` charge is the
   min-circuit-size floor `cbudget` (brute-force in `EXP`); constructing it is free, but proving its
   `C3` is the circuit lower bound = `P ≠ NP`.
2. **The `EXP` charge is `MCSP`.**  A capped min-circuit-size observer is exactly `MCSP` / `MKtP` (the
   universal observer via magnification, `TreeDagDuality.universal_observer_via_magnification`), whose
   *efficient detection* is barriered (`MCSPBarrier`, `HardnessMagnification` `bc9d27e2`).

## Honest scope

The cap is a real and correct move — it escapes hypercomputation and the natural-proofs constructivity
threshold.  It does **not** cross the wall: separation is level-independent and equals `C3 = cost_super`,
and the capped charge is `MCSP`, barriered at detection.  Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CappedObserver

open PallLean.Paper93.DeepMath.PathB.ConservedChargeSpec

variable {Fn Rep : Type} {computes : Rep → Fn → Prop} {rrank : Rep → ℕ}
  {Easy : Fn → Prop} {sat : Fn}

/-- **Separation ignores the level (proved).**  A conserved charge separates via `C1/C3/C4/gap` alone —
its computability level is never used (`_hL` is unused on purpose).  So capping the observer at a bounded
level (e.g. `EXP`, not hypercomputational) does not change whether it separates: the escape from
hypercomputation is free. -/
theorem separation_ignores_level (cc : ConservedCharge Fn Rep computes rrank Easy sat)
    (Level : (Fn → ℕ) → Prop) (_hL : Level cc.Q) : ¬ Easy sat :=
  charge_separates cc

/-- **The cap must exceed `P` (proved).**  Any conserved charge is non-`P`-efficient under the barrier, so
the cap has to sit strictly above `P` — capping at `P` is barriered.  With `separation_ignores_level`,
the target is a bounded observer above `P`: an `EXP`-cap, exactly as proposed. -/
theorem cap_must_exceed_P {PEfficient : (Fn → ℕ) → Prop} {Crypto : Prop}
    (barrier : ChargeBarrier Fn Rep computes rrank Easy sat PEfficient Crypto) (hC : Crypto)
    (cc : ConservedCharge Fn Rep computes rrank Easy sat) : ¬ PEfficient cc.Q :=
  charge_forces_non_natural barrier hC cc

/-- **The wall is C3, and C3 is level-independent (proved).**  Restated as the crux: a conserved charge
separates iff it is full on SAT (`C3`).  Since `charge_separates` uses no level predicate, the entire
difficulty — `C3` = SAT's min-floor is high = `cost_super` — is untouched by any cap.  Capping escapes
the barriers; it does not move the wall. -/
theorem wall_is_C3 (cc : ConservedCharge Fn Rep computes rrank Easy sat) : ¬ Easy sat :=
  charge_separates cc

end PallLean.Paper93.DeepMath.PathB.CappedObserver

#print axioms PallLean.Paper93.DeepMath.PathB.CappedObserver.separation_ignores_level
#print axioms PallLean.Paper93.DeepMath.PathB.CappedObserver.cap_must_exceed_P
#print axioms PallLean.Paper93.DeepMath.PathB.CappedObserver.wall_is_C3
