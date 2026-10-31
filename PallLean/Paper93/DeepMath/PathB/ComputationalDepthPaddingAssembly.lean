import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPadFunction

/-!
# Mountain 1, the assembly: two named halves, glue to `ConcretePadding` proved

Camp 2 (`PadFunction`) built the pad layer and drove the verifier side to the machine boundary
(`ntime_pad`: an `L`-verifier plus a `PadVerifier` machine put the strictly padded language in
`NTIME(q)`).  This file assembles the mountain: it names the two halves of `ConcretePadding`,
proves the glue that combines them, and wires camp 2's verifier theorem into the NTIME half — so
the whole ingredient now rests on exactly **two machine obligations**, each specified precisely.

## What is proved

* **`concretePadding_of_halves`** — the factoring glue: the NTIME half (pad up) plus the DTS half
  (strip down) give `ConcretePadding` exactly: pad into the assumed inclusion, then come back.
* **`ntimeHalf_of_padVerifiers`** — camp 2's machinery wired in: if every verifier has a
  `PadVerifier` (the decode–check–retag machine, camp 3's target), the NTIME half follows.
  With `concretePadding_of_halves`, `ConcretePadding` itself then rests on:

  1. **`PadVerifiersExist`** — the decode–check–retag transducer (machine engineering, the
     `comp`/emitter style; `pad_clock_transfer` pays its clock);
  2. **`PaddingDTSHalf`** — the virtual-input simulation (the hard half: run the padded decider
     on `padWith m x` while the tape holds only `x` — materializing `(n+1)^m` cells would violate
     the polylog space budget).

Both are labor on a published theorem, specified to the machine boundary; neither is the wall.
Nothing here is `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.PaddingAssembly

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.IndirectDiagonalization
open PallLean.Paper93.DeepMath.PathB.ConcreteTradingClasses
open PallLean.Paper93.DeepMath.PathB.PadFunction

/-- **The NTIME half (named).**  Pad up: a language at exponent `m·q` has its padded version at
exponent `q`. -/
def PaddingNTIMEHalf : Prop :=
  ∀ m q L, 1 ≤ m → NTIME (m * q) L → NTIME q (padLang m L)

/-- **The DTS half (named — the hard half).**  Strip down: a padded decider at exponent `p` yields
an original-language decider at exponent `m·p` — via virtual-input simulation, without
materializing the pad. -/
def PaddingDTSHalf : Prop :=
  ∀ m p L, 1 ≤ m → DTS p (padLang m L) → DTS (m * p) L

/-- **The factoring glue (proved).**  The two halves give `ConcretePadding` exactly: pad into the
assumed `NTIME(q) → DTS(p)` inclusion, then strip back down. -/
theorem concretePadding_of_halves (hN : PaddingNTIMEHalf) (hD : PaddingDTSHalf) :
    ConcretePadding := by
  intro p q hinc m hm L hL
  exact hD m p L hm (hinc (padLang m L) (hN m q L hm hL))

/-- **The machine obligation of the NTIME half (named).**  Every clocked verifier has a
`PadVerifier` — the decode–check–retag transducer, camp 3's construction target. -/
def PadVerifiersExist : Prop :=
  ∀ m q (M : Machine) (T : ℕ → ℕ), 1 ≤ m → Nonempty (PadVerifier m q M T)

/-- **Camp 2 wired in (proved).**  Given the machine obligation, the NTIME half follows from
`ntime_pad`: unpack the verifier, apply its `PadVerifier`, and the membership logic is already
discharged. -/
theorem ntimeHalf_of_padVerifiers (h : PadVerifiersExist) : PaddingNTIMEHalf := by
  intro m q L hm hL
  obtain ⟨M, T, c, hclock, hspec⟩ := hL
  obtain ⟨P⟩ := h m q M T hm
  exact ntime_pad m q L M T hspec P

/-- **The mountain, reduced (proved).**  `ConcretePadding` rests on exactly the two machine
obligations: the pad-verifier construction and the virtual-input DTS half. -/
theorem concretePadding_of_machines (hV : PadVerifiersExist) (hD : PaddingDTSHalf) :
    ConcretePadding :=
  concretePadding_of_halves (ntimeHalf_of_padVerifiers hV) hD

end PallLean.Paper93.DeepMath.PathB.PaddingAssembly

#print axioms PallLean.Paper93.DeepMath.PathB.PaddingAssembly.concretePadding_of_halves
#print axioms PallLean.Paper93.DeepMath.PathB.PaddingAssembly.ntimeHalf_of_padVerifiers
#print axioms PallLean.Paper93.DeepMath.PathB.PaddingAssembly.concretePadding_of_machines
