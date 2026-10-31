import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverClashViaTree
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDischargePiStar

/-!
# Entanglement via the tree — real correlation, but no channel

Darren's read: expanding Williams through the tree entangles the two observer clashes, "like quantum
entanglement," and that link might carry the missing projection across.  The physics analogy is exactly
right — and it is exactly why the composition still does not close.  Entanglement gives **correlation**,
the **no-communication theorem** says correlation is **not a channel**, and both halves are provable
here.

## The dictionary

| quantum | here |
|---|---|
| entangled pair sharing a hidden state | two observer clashes sharing the tree `H` |
| perfect correlation of outcomes | both clashes resolve from the same `H` |
| no-communication theorem | a resolved clash cannot *emit* a projection |
| the classical channel you still need | the bridge (`CompositionGap`) — payload = the separation |

## What is proved

* **`entangled_resolution` (proved)** — one shared hypothesis `H` (the tree) drives both observers;
  either clash gives `¬ H`.  The correlation is real.
* **`entangled_conclusions_coincide` (proved, by proof irrelevance)** — the two entangled outcomes are
  literally *equal* proofs of `¬ H`.  The second "measurement" returns the same value as the first — the
  correlation transmits **no new witness**.  This is the no-signalling content in its sharpest form.
* **`resolution_does_not_inhabit_projection` (proved)** — a concrete world where the Williams side is
  fully resolved (`¬ NEXPinPpoly` holds) yet **no** separating measure / `Π★` exists
  (`¬ Nonempty (SeparatingMeasure …)`).  The entangled resolution and the projection are logically
  independent: having the one does not hand you the other.  No channel.

## Why the arrows can't be reversed

Every observer clash *consumes* a projection (it takes `H → M` as a hypothesis) and *emits* only `¬ H`.
No clash — however entangled — has a projection in its conclusion.  So no amount of composing entangled
clashes will manufacture the projection the God-Move is missing; the arrows point the wrong way.  To get
a projection you must inject one — the bridge — and by `CompositionGap.bridge_target_is_the_separation`
its payload is `SAT ∉ P` itself.

**Honest scope.**  This does **not** prove `P ≠ NP`.  It formalizes the entanglement intuition faithfully
and shows it yields correlation without communication: the tree links the two faces into one shape, but
the link carries no witness across, and the classical channel that would (the bridge) is the separation.
Nothing here crosses the wall.
-/

namespace PallLean.Paper93.DeepMath.PathB.EntanglementNoChannel

open PallLean.Paper93.DeepMath.PathB.ObserverClashViaTree
open PallLean.Paper93.DeepMath.PathB.DischargePiStar

/-- **The entanglement is real (proved).**  A single shared hypothesis `H` — the tree — feeds two
observers (the Williams reader on `MW`, the God-Move reader on `MG`).  Either one resolves the shared
`H`: the outcomes are perfectly correlated because they are readings of the *same* substrate. -/
theorem entangled_resolution {H MW MG : Prop}
    (projW : H → MW) (obsW : MW → False)
    (projG : H → MG) (obsG : MG → False) :
    ¬ H :=
  two_observer_clash projW obsW

/-- **No-signalling, sharpest form (proved by proof irrelevance).**  The two entangled clashes conclude
the *same* proposition `¬ H`, and — `¬ H` being a `Prop` — their proofs are literally equal.  Reading the
second observer returns exactly the first observer's value: the correlation transmits **no new
information**.  Entanglement, not a channel. -/
theorem entangled_conclusions_coincide {H MW MG : Prop}
    (projW : H → MW) (obsW : MW → False)
    (projG : H → MG) (obsG : MG → False) :
    two_observer_clash projW obsW = two_observer_clash projG obsG :=
  rfl

/-- **No-communication theorem, concretely (proved).**  There is a world in which the Williams side is
fully resolved — `¬ NEXPinPpoly` holds — yet **no** separating measure (no `Π★`) exists at all.  Take a
model where `SAT ∈ P` (`PComp sat` true): by `separating_iff_not_PComp` the separating-measure type is
then empty, regardless of any `NEXP` fact.  So the entangled resolution and the projection are logically
independent — the correlation is not a channel that delivers the projection. -/
theorem resolution_does_not_inhabit_projection :
    ∃ (Obj : Type) (PComp : Obj → Prop) (sat : Obj) (NEXPinPpoly : Prop),
      (¬ NEXPinPpoly) ∧ ¬ Nonempty (SeparatingMeasure Obj PComp sat) :=
  ⟨Unit, (fun _ => True), (), False, not_false,
    fun hne => absurd trivial ((separating_iff_not_PComp (fun _ => True) ()).mp hne)⟩

end PallLean.Paper93.DeepMath.PathB.EntanglementNoChannel

#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementNoChannel.entangled_resolution
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementNoChannel.entangled_conclusions_coincide
#print axioms PallLean.Paper93.DeepMath.PathB.EntanglementNoChannel.resolution_does_not_inhabit_projection
