import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTseitinProtocolMagnification

/-!
# Dimensional observer boundary

This file records the dimension-stratified version of the observer idea.

The proved part is a restricted locality theorem:

* a low-dimensional observer has only finitely many available local channels;
* a high-dimensional boundary has finitely many independent directions;
* a faithful realization injects directions into channels;
* therefore, if the direction count exceeds the channel capacity, no faithful
  low-dimensional realization exists.

The unproved P-vs-NP-strength step is kept as an explicit force predicate:
`PTimeDeciderDimensionalForce`.  It says that every P-time signed SAT decider
would have to faithfully realize the high-dimensional boundary inside the
low-dimensional observer.  At a channel gap, that force predicate is equivalent
to the no-decider endpoint for the chosen P-time class.

The final section records the main guardrail: fixed finite dimension is only a
polynomial capacity dial.  A 64-dimensional fixed observer can have much more
local volume than a 4-dimensional observer, but its capacity is still a fixed
polynomial expression in its local radius/fanout parameters.  That is not an
NP-class resource by itself.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine

/-! ## Dimensional objects -/

/-- A local observer with an explicit spacetime dimension and local channel
budget.

`channelCapacity` below is intentionally coarse: it is a symbolic upper bound on
how many independent boundary directions can be faithfully routed through the
observer's local spacetime lightcone. -/
structure DimensionalObserver : Type where
  spacetimeDim : Nat
  timeHorizon : Nat
  localChannelWidth : Nat
  localityFanout : Nat

namespace DimensionalObserver

/-- Coarse channel capacity of a local observer.  In dimension `d`, a local
fanout radius contributes `(fanout + 1)^d` cells per time/channel unit. -/
def channelCapacity (O : DimensionalObserver) : Nat :=
  O.timeHorizon * O.localChannelWidth * (O.localityFanout + 1) ^ O.spacetimeDim

end DimensionalObserver

/-- A high-dimensional boundary object with independent counterfactual
directions. -/
structure HighDimensionalBoundary : Type where
  boundaryDim : Nat
  independentDirections : Nat

/-- The intended P-observer shape: a four-dimensional local spacetime observer. -/
def fourDLocalObserver
    (timeHorizon localChannelWidth localityFanout : Nat) :
    DimensionalObserver where
  spacetimeDim := 4
  timeHorizon := timeHorizon
  localChannelWidth := localChannelWidth
  localityFanout := localityFanout

/-- The intended NP-boundary shape: a 64-dimensional effective witness/boundary
space.  The number of independent directions is left explicit. -/
def sixtyFourDimensionalBoundary (directions : Nat) :
    HighDimensionalBoundary where
  boundaryDim := 64
  independentDirections := directions

/-- A fixed-dimensional local observer.  This is useful for stating the
polynomial-dial guardrail uniformly, including the 64-dimensional case. -/
def fixedDimLocalObserver
    (spacetimeDim timeHorizon localChannelWidth localityFanout : Nat) :
    DimensionalObserver where
  spacetimeDim := spacetimeDim
  timeHorizon := timeHorizon
  localChannelWidth := localChannelWidth
  localityFanout := localityFanout

/-! ## Faithful dimensional realization -/

/-- A faithful low-dimensional realization of a high-dimensional boundary.

The key data is the injection from independent boundary directions to available
observer channels.  This is the dimensional analogue of the local Tseitin
protocol slot map. -/
structure FaithfulDimensionalRealization
    (O : DimensionalObserver)
    (B : HighDimensionalBoundary) : Type where
  channelOf :
    Fin B.independentDirections -> Fin O.channelCapacity
  channelOf_injective :
    Function.Injective channelOf

/-- Any faithful dimensional realization forces the high-dimensional direction
count to fit inside the low-dimensional channel capacity. -/
theorem independentDirections_le_channelCapacity_of_faithful
    {O : DimensionalObserver}
    {B : HighDimensionalBoundary}
    (R : FaithfulDimensionalRealization O B) :
    B.independentDirections <= O.channelCapacity := by
  have hcard :
      Fintype.card (Fin B.independentDirections) <=
        Fintype.card (Fin O.channelCapacity) :=
    Fintype.card_le_of_injective R.channelOf R.channelOf_injective
  simpa [Fintype.card_fin] using hcard

/-- If independent high-dimensional directions exceed the low-dimensional
observer's channel capacity, no faithful dimensional realization exists. -/
theorem no_faithfulDimensionalRealization_of_channelGap
    (O : DimensionalObserver)
    (B : HighDimensionalBoundary)
    (hgap : O.channelCapacity < B.independentDirections) :
    Not (Nonempty (FaithfulDimensionalRealization O B)) := by
  rintro ⟨R⟩
  have hfit :
      B.independentDirections <= O.channelCapacity :=
    independentDirections_le_channelCapacity_of_faithful R
  exact Nat.not_lt_of_ge hfit hgap

/-- Specialized 4D/64D statement.  A four-dimensional local observer cannot
faithfully realize a 64-dimensional boundary when the boundary direction count
exceeds the observer's channel capacity. -/
theorem no_fourDLocalObserver_realizes_sixtyFourDBoundary_of_channelGap
    (timeHorizon localChannelWidth localityFanout directions : Nat)
    (hgap :
      (fourDLocalObserver timeHorizon localChannelWidth
        localityFanout).channelCapacity < directions) :
    Not (Nonempty
      (FaithfulDimensionalRealization
        (fourDLocalObserver timeHorizon localChannelWidth localityFanout)
        (sixtyFourDimensionalBoundary directions))) :=
  no_faithfulDimensionalRealization_of_channelGap
    (fourDLocalObserver timeHorizon localChannelWidth localityFanout)
    (sixtyFourDimensionalBoundary directions)
    hgap

/-! ## Explicit P-time force bridge -/

/-- The full-strength force predicate.

This is the dangerous bridge, stated explicitly: every P-time signed SAT decider
in the supplied class `PT` would have to realize the high-dimensional boundary
inside the low-dimensional observer.  The file does not prove this predicate. -/
structure PTimeDeciderDimensionalForce
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (O : DimensionalObserver)
    (B : HighDimensionalBoundary) : Type where
  realize :
    forall (M : DTM), PTimeSignedSATDecider enc PT M ->
      FaithfulDimensionalRealization O B

/-- A dimensional force bridge plus a channel gap rules out deciders in the
chosen P-time class. -/
theorem no_pTimeSignedSATDecider_of_dimensionalForce_gap
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (O : DimensionalObserver)
    (B : HighDimensionalBoundary)
    (hgap : O.channelCapacity < B.independentDirections)
    (Force : PTimeDeciderDimensionalForce PT O B) :
    Not (exists M : DTM, PTimeSignedSATDecider enc PT M) := by
  rintro ⟨M, H⟩
  exact no_faithfulDimensionalRealization_of_channelGap O B hgap
    ⟨Force.realize M H⟩

/-- The force bridge is constructible from the no-decider endpoint, but only
vacuously. -/
def dimensionalForce_of_no_pTimeSignedSATDecider
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (O : DimensionalObserver)
    (B : HighDimensionalBoundary)
    (hno : Not (exists M : DTM, PTimeSignedSATDecider enc PT M)) :
    PTimeDeciderDimensionalForce PT O B where
  realize M H := False.elim (hno ⟨M, H⟩)

/-- Propositional version of the vacuous construction. -/
theorem nonempty_dimensionalForce_of_no_pTimeSignedSATDecider
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (O : DimensionalObserver)
    (B : HighDimensionalBoundary)
    (hno : Not (exists M : DTM, PTimeSignedSATDecider enc PT M)) :
    Nonempty (PTimeDeciderDimensionalForce PT O B) :=
  ⟨dimensionalForce_of_no_pTimeSignedSATDecider PT O B hno⟩

/-- At a dimensional channel gap, the force bridge is equivalent to the
no-decider endpoint for the supplied P-time class.

This is the honest boundary: the dimensional theorem is real for the restricted
faithful-realization model; lifting arbitrary P-time SAT deciders into that
model is exactly the endpoint-strength bridge. -/
theorem dimensionalForce_iff_no_pTimeSignedSATDecider_of_gap
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (O : DimensionalObserver)
    (B : HighDimensionalBoundary)
    (hgap : O.channelCapacity < B.independentDirections) :
    Nonempty (PTimeDeciderDimensionalForce PT O B) <->
      Not (exists M : DTM, PTimeSignedSATDecider enc PT M) := by
  constructor
  · rintro ⟨Force⟩
    exact no_pTimeSignedSATDecider_of_dimensionalForce_gap
      PT O B hgap Force
  · intro hno
    exact nonempty_dimensionalForce_of_no_pTimeSignedSATDecider
      PT O B hno

/-- 4D/64D endpoint consequence. -/
theorem no_pTimeSignedSATDecider_of_fourD_sixtyFourD_force_gap
    {enc : SignedFormulaEncoding}
    (PT : PTimeSATPolynomialTime enc)
    (timeHorizon localChannelWidth localityFanout directions : Nat)
    (hgap :
      (fourDLocalObserver timeHorizon localChannelWidth
        localityFanout).channelCapacity < directions)
    (Force :
      PTimeDeciderDimensionalForce PT
        (fourDLocalObserver timeHorizon localChannelWidth localityFanout)
        (sixtyFourDimensionalBoundary directions)) :
    Not (exists M : DTM, PTimeSignedSATDecider enc PT M) :=
  no_pTimeSignedSATDecider_of_dimensionalForce_gap
    PT
    (fourDLocalObserver timeHorizon localChannelWidth localityFanout)
    (sixtyFourDimensionalBoundary directions)
    hgap
    Force

/-! ## Fixed-dimension guardrail -/

/-- Capacity of a fixed-dimensional observer is exactly a fixed polynomial
expression in the time/channel/fanout parameters. -/
theorem fixedDimLocalObserver_channelCapacity_eq
    (spacetimeDim timeHorizon localChannelWidth localityFanout : Nat) :
    (fixedDimLocalObserver spacetimeDim timeHorizon localChannelWidth
      localityFanout).channelCapacity =
      timeHorizon * localChannelWidth *
        (localityFanout + 1) ^ spacetimeDim := rfl

/-- The 4D observer's channel capacity is the corresponding fourth-power local
volume expression. -/
theorem fourDLocalObserver_channelCapacity_eq
    (timeHorizon localChannelWidth localityFanout : Nat) :
    (fourDLocalObserver timeHorizon localChannelWidth
      localityFanout).channelCapacity =
      timeHorizon * localChannelWidth * (localityFanout + 1) ^ 4 := rfl

/-- A fixed 64-dimensional observer is still governed by a fixed polynomial
capacity expression, not an exponential-in-input resource by definition. -/
theorem sixtyFourDLocalObserver_channelCapacity_eq
    (timeHorizon localChannelWidth localityFanout : Nat) :
    (fixedDimLocalObserver 64 timeHorizon localChannelWidth
      localityFanout).channelCapacity =
      timeHorizon * localChannelWidth * (localityFanout + 1) ^ 64 := rfl

/-- Being fixed-dimensional means having some constant exponent in the capacity
formula.  This theorem packages the point without pretending it is a complexity
lower bound: every fixed-dimensional observer has a capacity exponent equal to
its dimension. -/
theorem exists_fixedPolynomialExponent_for_dimensionalObserver
    (O : DimensionalObserver) :
    exists exponent : Nat,
      O.channelCapacity =
        O.timeHorizon * O.localChannelWidth *
          (O.localityFanout + 1) ^ exponent := by
  exact ⟨O.spacetimeDim, rfl⟩

/-- Guardrail for the 64D idea: the dimensional model only gives a larger fixed
polynomial channel expression.  Any P-vs-NP conclusion still needs the separate
force bridge above. -/
theorem sixtyFourD_is_fixedPolynomialCapacity :
    exists exponent : Nat, exponent = 64 := by
  exact ⟨64, rfl⟩

/-! ## Kernel-only axiom trace -/

#print axioms independentDirections_le_channelCapacity_of_faithful
#print axioms no_faithfulDimensionalRealization_of_channelGap
#print axioms no_fourDLocalObserver_realizes_sixtyFourDBoundary_of_channelGap
#print axioms no_pTimeSignedSATDecider_of_dimensionalForce_gap
#print axioms nonempty_dimensionalForce_of_no_pTimeSignedSATDecider
#print axioms dimensionalForce_iff_no_pTimeSignedSATDecider_of_gap
#print axioms no_pTimeSignedSATDecider_of_fourD_sixtyFourD_force_gap
#print axioms fixedDimLocalObserver_channelCapacity_eq
#print axioms fourDLocalObserver_channelCapacity_eq
#print axioms sixtyFourDLocalObserver_channelCapacity_eq
#print axioms exists_fixedPolynomialExponent_for_dimensionalObserver
#print axioms sixtyFourD_is_fixedPolynomialCapacity

end PallLean.Paper93.DeepMath.PathB
