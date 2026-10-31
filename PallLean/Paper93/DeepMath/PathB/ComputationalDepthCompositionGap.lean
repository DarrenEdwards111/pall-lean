import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDischargePiStar
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthWilliamsPpolyCashout

/-!
# Does "God-Move ∘ Williams bridge ∘ holographic projection" close P vs NP?

The honest test of Darren's proposed composition: use the Williams meta-complexity bridge (which
outputs a separation) to supply the holographic projection / God-Move `Π★`, and read off `SAT ∉ P`.
We write the composition in Lean and let the type checker show *exactly* what is missing.

The verdict is machine-checked below: the composition is **exactly one bridge short**, and that bridge
is provably the whole problem.  Two walls, both already on the map:

1. **The circularity wall.**  The composition needs a bridge whose *target* is a separating measure.
   By `DischargePiStar.separating_iff_not_PComp`, a separating measure exists **iff** `SAT ∉ P`.  So the
   bridge's conclusion *is* the separation — it cannot be a free lemma; producing it is producing the
   answer.  This is the God-Move's open piece: `Π★`.

2. **The ceiling wall.**  The Williams bridge's actual output is `¬ NEXPinPpoly` = `NEXP ⊄ P/poly` — a
   statement at the *nondeterministic exponential* level.  Nothing maps `¬ NEXPinPpoly` to `¬ PComp sat`
   for free; that step is the `NEXP → NP` down-scaling, a separate open problem.  This is Williams' own
   ceiling.

The relocation from `ObserverClashViaTree` is exactly why the two pieces do **not** cancel: the
God-Move's open piece is the projection `Π★`, Williams' open piece is the algorithm, and Williams'
*proven* projection (the easy witness) is a **different** map — `NEXP`-bulk ⟶ poly-boundary — not the
rank-monotone `Π★` the God-Move needs, and it arrives conditioned on the very assumption being refuted.

## What is proved here

* **`free_bridge_would_be_the_separation` (proved)** — constructing the separating measure *is* `SAT ∉ P`.
  The projection is the destination, not a tool.
* **`composition_with_bridge_closes` (proved)** — the composition *does* close **given the bridge**:
  `(¬ NEXPinPpoly) → (¬ NEXPinPpoly → Nonempty SeparatingMeasure) → ¬ PComp sat`.  Honest — it shows the
  shape is coherent, and isolates the bridge as the one missing input.
* **`composition_via_williams` (proved)** — plug in the *actual* `williams_cashout` with its algorithm
  socket discharged: you still need the bridge.  The algorithm removes Williams' open piece and leaves
  the God-Move's untouched — the two open pieces are genuinely distinct.
* **`bridge_target_is_the_separation` (proved)** — the bridge's target `⟺ ¬ PComp sat`.  The bridge is
  P≠NP-strength; its conclusion is the whole problem.

**Honest scope.**  This does **not** prove `P ≠ NP` — it proves the opposite of a closure: the proposed
composition reduces, exactly, to a bridge whose existence is equivalent to the separation itself, on top
of the unbridged `NEXP → NP` gap.  Both walls are the map's walls.  Nothing here crosses them; the file
is the machine-checked reason the composition is a restatement of the problem, not a solution to it.
-/

namespace PallLean.Paper93.DeepMath.PathB.CompositionGap

open PallLean.Paper93.DeepMath.PathB.DischargePiStar
open PallLean.Paper93.DeepMath.PathB.WilliamsPpolyCashout

/-- **Constructing the projection IS the separation (proved).**  A separating measure (a working `Π★`)
gives `SAT ∉ P` outright — by `separating_iff_not_PComp`.  So the holographic projection the composition
wants to "supply" is the destination itself, not an ingredient one obtains along the way. -/
theorem free_bridge_would_be_the_separation
    {Obj : Type} (PComp : Obj → Prop) (sat : Obj)
    (measure : Nonempty (SeparatingMeasure Obj PComp sat)) :
    ¬ PComp sat :=
  (separating_iff_not_PComp PComp sat).mp measure

/-- **The composition closes — but only given the bridge (proved).**  From the Williams output
`¬ NEXPinPpoly` and a proposed bridge that turns it into a separating measure, we do get `SAT ∉ P`.  This
makes the shape coherent and isolates `bridge` as the single missing input: the map from Williams'
`NEXP`-level separation to an `NP`-level `Π★`. -/
theorem composition_with_bridge_closes
    {Obj : Type} (PComp : Obj → Prop) (sat : Obj) (NEXPinPpoly : Prop)
    (williams : ¬ NEXPinPpoly)
    (bridge : ¬ NEXPinPpoly → Nonempty (SeparatingMeasure Obj PComp sat)) :
    ¬ PComp sat :=
  (separating_iff_not_PComp PComp sat).mp (bridge williams)

/-- **Plug in the real Williams cash-out — the bridge survives (proved).**  Even with the Circuit-SAT
algorithm `hAlg` and *all* of Williams' proven sockets discharged, producing `¬ PComp sat` still requires
the `bridge`.  Discharging Williams' open piece (the algorithm) does nothing to the God-Move's open piece
(the projection): they are distinct, and the composition needs the second one supplied independently. -/
theorem composition_via_williams
    {Obj : Type} (PComp : Obj → Prop) (sat : Obj)
    (NEXPinPpoly CircuitSATFast EasyWitness FastNEXPAlg : Prop)
    (ikw_easy_witness : NEXPinPpoly → EasyWitness)
    (algorithmic_speedup : CircuitSATFast → EasyWitness → FastNEXPAlg)
    (nondet_time_hierarchy : FastNEXPAlg → False)
    (hAlg : CircuitSATFast)
    (bridge : ¬ NEXPinPpoly → Nonempty (SeparatingMeasure Obj PComp sat)) :
    ¬ PComp sat :=
  (separating_iff_not_PComp PComp sat).mp
    (bridge (williams_cashout NEXPinPpoly CircuitSATFast EasyWitness FastNEXPAlg
      ikw_easy_witness algorithmic_speedup nondet_time_hierarchy hAlg))

/-- **The bridge is the whole problem (proved).**  The bridge's *target* is logically the separation:
`Nonempty (SeparatingMeasure …) ↔ ¬ PComp sat`.  So any such bridge has `SAT ∉ P` as its conclusion — it
is not a lemma one proves for free.  The composition is a restatement of the problem, not a route
around it. -/
theorem bridge_target_is_the_separation
    {Obj : Type} (PComp : Obj → Prop) (sat : Obj) :
    Nonempty (SeparatingMeasure Obj PComp sat) ↔ ¬ PComp sat :=
  separating_iff_not_PComp PComp sat

end PallLean.Paper93.DeepMath.PathB.CompositionGap

#print axioms PallLean.Paper93.DeepMath.PathB.CompositionGap.free_bridge_would_be_the_separation
#print axioms PallLean.Paper93.DeepMath.PathB.CompositionGap.composition_with_bridge_closes
#print axioms PallLean.Paper93.DeepMath.PathB.CompositionGap.composition_via_williams
#print axioms PallLean.Paper93.DeepMath.PathB.CompositionGap.bridge_target_is_the_separation
