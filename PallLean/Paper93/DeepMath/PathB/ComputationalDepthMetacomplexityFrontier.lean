import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDimensionalObserverBoundary

/-!
# Metacomplexity frontier: the N-frame observer boundary as a K^t / MCSP obstruction

**STATUS: FRAMEWORK / FAITHFUL BRIDGE, NOT A PROOF.**

This file plants the N-frame observer program on the live metacomplexity frontier
and states, precisely, what it does and does not contribute.  It does **not**
prove `P ≠ NP`, and a clean `#print axioms` here is documentation, not progress.

The mapping is exact at the level we can actually prove: the N-frame observer
boundary (the dimensional/communication force at a channel gap) is *equivalent*
to "no decider in the supplied polynomial-time class" — the SAT-in-P face of the
MCSP / time-bounded-Kolmogorov (`K^t`) obstruction.  K^t asks "what is the
shortest program producing this object within a time budget?", which is the same
question as "what can a bounded observer describe/produce within its budget" —
so the observer/`K^t` correspondence is genuine, not a metaphor.

## 1. What is known (cited literature, not formalized here)

* **Hirahara (2018):** worst-case → average-case reductions for approximate MCSP
  / GapMINKT.
* **Liu–Pass (2020):** one-way functions exist **iff** time-bounded Kolmogorov
  complexity (MINKT / `K^t`) is mildly hard on average.
* **Carmosino–Impagliazzo–Kabanets–Kolokolova (2016):** learning algorithms from
  natural properties / MCSP.
* **Hardness magnification** (Oliveira–Santhanam; McKay–Murray–Williams): a
  barely-superlinear lower bound for MCSP/MKtP variants would amplify to
  `NP ⊄ P/poly`.
* **Locality barrier** (Chen–Hirahara–Oliveira–Pich–Rajgopal–Santhanam, 2020):
  the proven reason the magnification trigger resists current techniques.
* MCSP is not known to be NP-complete (Murray–Williams); partial-MCSP is
  (Hirahara, 2022).

These are facts about the field; they are referenced, not asserted as `Prop`
fields (doing the latter is the vacuity trap).

## 2. What would amplify (the open, barrier-protected target)

`MetacomplexityMagnificationTarget` below records the magnification trigger as an
explicit **open conjecture**.  It is not proved.  By the locality barrier it
resists current techniques, and by the project's own
`nonempty_hardnessMagnificationBreakthrough_iff_MCSPMINKTHardness` (commit
`42d1fd10`) the magnification bridge is itself `P≠NP`-strength.

## 3. What the N-frame contributes (the faithful bridge — proven)

`observerBoundary_iff_metacomplexityObstruction`: the observer boundary IS the
SAT-in-P obstruction, as an **equivalence** (both directions).  This is the
precise, honest contribution — a faithful re-encoding of the metacomplexity
obstruction in observer/`K^t` language.  By the conservation dilemma it gives
**no leverage**: it relocates the difficulty, it does not reduce it.  Its value
is as a precise framework statement and a possible new semantic angle, not as a
step toward the proof.

Caveat held in the open: `MetacomplexityNoPTimeDecider` is the *SAT-in-P face* of
the obstruction; the bridge from there to MCSP/`K^t` hardness proper is the cited
literature above, not a theorem of this file.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine

/-! ## The metacomplexity obstruction (SAT-in-P face) -/

/-- The metacomplexity-side obstruction, SAT-in-P face: for the supplied
polynomial-time class `PT`, no machine in that class decides signed SAT.

Via the metacomplexity dictionary (the cited Liu–Pass / Hirahara results) this is
the face of the MCSP / `K^t` obstruction that the literature connects to one-way
functions and average-case hardness.  It is **not** a formalization of MCSP
itself — that bridge is cited, not proved here. -/
def MetacomplexityNoPTimeDecider
    (enc : SignedFormulaEncoding) (PT : PTimeSATPolynomialTime enc) : Prop :=
  ¬ ∃ M : DTM, PTimeSignedSATDecider enc PT M

/-! ## Core faithful bridge: observer boundary ⟺ metacomplexity obstruction -/

/-- **Faithful bridge (proven).**  At a dimensional channel gap, the N-frame
observer boundary (dimensional force) is *equivalent* to the metacomplexity
obstruction for the supplied P-time class.

This is the precise sense in which the observer boundary IS the metacomplexity /
`K^t` obstruction: an equivalence of two `P≠NP`-strength statements, i.e. a
faithful re-encoding — not a reduction to anything easier. -/
theorem observerBoundary_iff_metacomplexityObstruction
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (O : DimensionalObserver)
    (B : HighDimensionalBoundary)
    (hgap : O.channelCapacity < B.independentDirections) :
    Nonempty (PTimeDeciderDimensionalForce PT O B) ↔
      MetacomplexityNoPTimeDecider enc PT :=
  dimensionalForce_iff_no_pTimeSignedSATDecider_of_gap PT O B hgap

/-- The forward direction in isolation: the observer boundary yields the
metacomplexity obstruction. -/
theorem metacomplexityObstruction_of_observerBoundary
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (O : DimensionalObserver)
    (B : HighDimensionalBoundary)
    (hgap : O.channelCapacity < B.independentDirections)
    (H : Nonempty (PTimeDeciderDimensionalForce PT O B)) :
    MetacomplexityNoPTimeDecider enc PT :=
  (observerBoundary_iff_metacomplexityObstruction PT O B hgap).mp H

/-! ## Amplification target (open, barrier-protected) -/

/-- The hardness-magnification trigger, as an explicit **open conjecture**.

`weakLowerBound` is the barely-superlinear metacomplexity lower bound; `amplifies`
is the magnification implication that it would blow up into the SAT-in-P
obstruction.  Neither field is proved here.  By the locality barrier the trigger
resists current techniques, and by `42d1fd10` the magnification bridge is
`P≠NP`-strength.  This structure exists to *name* the target precisely, not to
discharge it. -/
structure MetacomplexityMagnificationTarget
    (enc : SignedFormulaEncoding) (PT : PTimeSATPolynomialTime enc) : Type where
  weakLowerBound : Prop
  amplifies : weakLowerBound → MetacomplexityNoPTimeDecider enc PT

/-- Conditional chain: if the magnification target holds and its weak lower bound
is established, the observer boundary follows at any channel gap.

Both inputs are open; this records the chain, it does not supply them. -/
theorem observerBoundary_of_magnification
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (O : DimensionalObserver)
    (B : HighDimensionalBoundary)
    (hgap : O.channelCapacity < B.independentDirections)
    (Mag : MetacomplexityMagnificationTarget enc PT)
    (hweak : Mag.weakLowerBound) :
    Nonempty (PTimeDeciderDimensionalForce PT O B) :=
  (observerBoundary_iff_metacomplexityObstruction PT O B hgap).mpr
    (Mag.amplifies hweak)

/-! ## Faithfulness / no-leverage record -/

/-- Honest record that the bridge is an equivalence, hence faithful: the observer
boundary and the metacomplexity obstruction imply each other at a gap.  An
equivalence carries no leverage — both sides are `P≠NP`-strength, so establishing
either is establishing the separation. -/
theorem observerBoundary_faithful_equivalence
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (O : DimensionalObserver)
    (B : HighDimensionalBoundary)
    (hgap : O.channelCapacity < B.independentDirections) :
    (Nonempty (PTimeDeciderDimensionalForce PT O B) →
        MetacomplexityNoPTimeDecider enc PT) ∧
      (MetacomplexityNoPTimeDecider enc PT →
        Nonempty (PTimeDeciderDimensionalForce PT O B)) :=
  ⟨(observerBoundary_iff_metacomplexityObstruction PT O B hgap).mp,
   (observerBoundary_iff_metacomplexityObstruction PT O B hgap).mpr⟩

/-! ## Kernel-only axiom trace (clean = honesty, not progress) -/

#print axioms observerBoundary_iff_metacomplexityObstruction
#print axioms metacomplexityObstruction_of_observerBoundary
#print axioms observerBoundary_of_magnification
#print axioms observerBoundary_faithful_equivalence

end PallLean.Paper93.DeepMath.PathB
