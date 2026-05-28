import PallLean.Paper93.DeepMath.PathB.ComputationalDepthMetacomplexityFrontier

/-!
# Rung 6: the general-model wall

**STATUS: WALL THEOREM / CONSERVATION LAYER, NOT A PROOF OF P ≠ NP.**

Rung 6 is where the ladder stops being a restricted lower-bound program and
becomes the full general polynomial-time lower-bound problem.  This file makes
that endpoint explicit.

The central point is a conservation theorem: any proposed bridge from arbitrary
P-time signed-SAT deciders into a restricted obstruction model is equivalent, at
this level of generality, to the no-decider endpoint itself.  The forward
direction uses the obstruction; the reverse direction is vacuous once no decider
exists.  Therefore a universal bridge is not a shortcut around P vs NP — it is a
repackaging of the separation.

This is useful precisely because it prevents overclaiming.  Rungs 1--5 can add
real restricted kernels and substrates.  Rung 6 records that the unrestricted
lift is the wall.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine

/-! ## General obstruction packages -/

/-- A general obstruction target for P-time signed-SAT deciders.

`Witness` is the restricted object a decider is supposed to yield — a protocol,
realization, circuit, certificate, or observer-visible trace.  `impossible` says
that no such witness can exist. -/
structure GeneralModelObstruction : Type 1 where
  Witness : Type
  impossible : Witness -> False

/-- A bridge from arbitrary P-time signed-SAT deciders into a supplied
obstruction target.  This is the shape every alleged rung-6 lift has to take:
turn any general decider into the restricted object that the lower-bound theorem
forbids. -/
structure PTimeToObstructionBridge
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (Obs : GeneralModelObstruction) : Type where
  realize :
    forall M : DTM, PTimeSignedSATDecider enc PT M -> Obs.Witness

/-- A bridge into an impossible obstruction rules out P-time signed-SAT deciders. -/
theorem no_pTimeSignedSATDecider_of_generalBridge
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (Obs : GeneralModelObstruction)
    (Bridge : PTimeToObstructionBridge PT Obs) :
    MetacomplexityNoPTimeDecider enc PT := by
  rintro ⟨M, H⟩
  exact Obs.impossible (Bridge.realize M H)

/-- Conversely, the bridge is always constructible from the no-decider endpoint,
but only vacuously.  This is the conservation-of-difficulty direction. -/
def generalBridge_of_no_pTimeSignedSATDecider
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (Obs : GeneralModelObstruction)
    (hno : MetacomplexityNoPTimeDecider enc PT) :
    PTimeToObstructionBridge PT Obs where
  realize M H := False.elim (hno ⟨M, H⟩)

/-- Propositional form of the vacuous construction. -/
theorem nonempty_generalBridge_of_no_pTimeSignedSATDecider
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (Obs : GeneralModelObstruction)
    (hno : MetacomplexityNoPTimeDecider enc PT) :
    Nonempty (PTimeToObstructionBridge PT Obs) :=
  ⟨generalBridge_of_no_pTimeSignedSATDecider PT Obs hno⟩

/-- **Rung-6 conservation theorem.**  For any impossible obstruction target, the
existence of a universal bridge from arbitrary P-time signed-SAT deciders into
that target is equivalent to the no-decider endpoint.

So a rung-6 bridge is not an intermediate lemma weaker than P vs NP.  Proving it
unconditionally would already prove the endpoint; obtaining it from the endpoint
is vacuous. -/
theorem generalBridge_iff_no_pTimeSignedSATDecider
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (Obs : GeneralModelObstruction) :
    Nonempty (PTimeToObstructionBridge PT Obs) ↔
      MetacomplexityNoPTimeDecider enc PT := by
  constructor
  · rintro ⟨Bridge⟩
    exact no_pTimeSignedSATDecider_of_generalBridge PT Obs Bridge
  · intro hno
    exact nonempty_generalBridge_of_no_pTimeSignedSATDecider PT Obs hno

/-! ## Observer bridge as a rung-6 wall instance -/

/-- The dimensional observer bridge already present in the project is exactly a
rung-6 wall theorem: at a channel gap, observer force is equivalent to the
no-decider endpoint. -/
theorem observerForce_is_rung6_wall
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (O : DimensionalObserver)
    (B : HighDimensionalBoundary)
    (hgap : O.channelCapacity < B.independentDirections) :
    Nonempty (PTimeDeciderDimensionalForce PT O B) ↔
      MetacomplexityNoPTimeDecider enc PT :=
  observerBoundary_iff_metacomplexityObstruction PT O B hgap

/-- Any proof of a rung-6 observer force at a channel gap gives the no-decider
endpoint.  This is a consequence theorem, not a construction of the force. -/
theorem no_pTimeSignedSATDecider_of_rung6ObserverForce
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (O : DimensionalObserver)
    (B : HighDimensionalBoundary)
    (hgap : O.channelCapacity < B.independentDirections)
    (Force : Nonempty (PTimeDeciderDimensionalForce PT O B)) :
    MetacomplexityNoPTimeDecider enc PT :=
  (observerForce_is_rung6_wall PT O B hgap).mp Force

/-- Conversely, once the no-decider endpoint has been proved, the observer force
exists vacuously.  This records that the bridge has no independent leverage. -/
theorem rung6ObserverForce_of_no_pTimeSignedSATDecider
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (O : DimensionalObserver)
    (B : HighDimensionalBoundary)
    (hgap : O.channelCapacity < B.independentDirections)
    (hno : MetacomplexityNoPTimeDecider enc PT) :
    Nonempty (PTimeDeciderDimensionalForce PT O B) :=
  (observerForce_is_rung6_wall PT O B hgap).mpr hno

/-! ## Rung-6 bundle -/

/-- Rung 6 is complete only as a wall/conservation layer.  It identifies the
unrestricted bridge with the separation endpoint; it does not cross it. -/
structure Rung6WallSubstrate : Prop where
  general_bridge_wall :
    forall {enc : SignedFormulaEncoding}
      (PT : PTimeSATPolynomialTime enc)
      (Obs : GeneralModelObstruction),
      Nonempty (PTimeToObstructionBridge PT Obs) ↔
        MetacomplexityNoPTimeDecider enc PT
  observer_bridge_wall :
    forall {enc : SignedFormulaEncoding}
      (PT : PTimeSATPolynomialTime enc)
      (O : DimensionalObserver)
      (B : HighDimensionalBoundary),
      O.channelCapacity < B.independentDirections ->
      (Nonempty (PTimeDeciderDimensionalForce PT O B) ↔
        MetacomplexityNoPTimeDecider enc PT)

/-- The completed rung-6 wall substrate. -/
theorem rung6_wall_substrate : Rung6WallSubstrate where
  general_bridge_wall := by
    intro enc PT Obs
    exact generalBridge_iff_no_pTimeSignedSATDecider PT Obs
  observer_bridge_wall := by
    intro enc PT O B hgap
    exact observerForce_is_rung6_wall PT O B hgap

/-! ## Kernel-only trace -/

#print axioms no_pTimeSignedSATDecider_of_generalBridge
#print axioms generalBridge_of_no_pTimeSignedSATDecider
#print axioms generalBridge_iff_no_pTimeSignedSATDecider
#print axioms observerForce_is_rung6_wall
#print axioms no_pTimeSignedSATDecider_of_rung6ObserverForce
#print axioms rung6ObserverForce_of_no_pTimeSignedSATDecider
#print axioms rung6_wall_substrate

end PallLean.Paper93.DeepMath.PathB
