import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameBooleanObservationBarrier

/-!
# Exact trace-length threshold for separated continuation cells

The Boolean-observation barrier is the one-bit case of a general information
law.  Suppose a continuation-to-cell map factors through a `k`-bit execution
trace.  If a distance-three code satisfies the radius-one four-label law, then
the cell map is injective; factorization then makes the trace injective.  The
`2^m` continuation labels must therefore fit into `2^k` traces, forcing
`m <= k`.

This file proves that threshold, its strict-short-trace obstruction, and the
corresponding correctness calibration for an alleged SAT solver.  It also
shows tightness at `k = m`: retaining the full continuation label as the trace
does satisfy factorization and fourwise compatibility.

Thus moving from the final answer to a transcript only helps if the transcript
retains at least the complete semantic information content of the
continuation label.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameTraceLengthThreshold

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordRadiusBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneDistanceBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalityThreshold
open PallLean.Paper93.DeepMath.PathB.NFrameSeparatedFourwiseInjectivityEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameBooleanObservationBarrier

/-! ## Capacity and length lower bounds -/

/-- An injective cell map factored through a `k`-bit trace requires room for
all `2^m` continuation labels. -/
theorem two_pow_le_two_pow_of_traceFactored_injective_cellMap
    {m k : Nat} {Cell : Type}
    (trace : Assignment m -> Assignment k)
    (cellOf : Assignment m -> Cell)
    (hfactor : CellMapFactorsThrough trace cellOf)
    (hcell : Function.Injective cellOf) :
    2 ^ m <= 2 ^ k := by
  simpa using
    (two_pow_le_observation_card_of_factored_injective_cellMap
      trace cellOf hfactor hcell)

/-- Equivalently, such a trace must contain at least `m` bits. -/
theorem trace_length_ge_of_factored_injective_cellMap
    {m k : Nat} {Cell : Type}
    (trace : Assignment m -> Assignment k)
    (cellOf : Assignment m -> Cell)
    (hfactor : CellMapFactorsThrough trace cellOf)
    (hcell : Function.Injective cellOf) :
    m <= k := by
  have hpow := two_pow_le_two_pow_of_traceFactored_injective_cellMap
    trace cellOf hfactor hcell
  by_contra hnot
  have hkm : k < m := Nat.lt_of_not_ge hnot
  have hstrict : 2 ^ k < 2 ^ m :=
    Nat.pow_lt_pow_right (by norm_num : 1 < (2 : Nat)) hkm
  omega

/-- A trace strictly shorter than the continuation label cannot support an
injective factored cell map. -/
theorem shortTrace_factored_cellMap_not_injective
    {m k : Nat} {Cell : Type}
    (trace : Assignment m -> Assignment k)
    (cellOf : Assignment m -> Cell)
    (hfactor : CellMapFactorsThrough trace cellOf)
    (hshort : k < m) :
    ¬ Function.Injective cellOf := by
  intro hcell
  have hmk := trace_length_ge_of_factored_injective_cellMap
    trace cellOf hfactor hcell
  omega

/-! ## Distance-three fourwise consequence -/

/-- A distance-three four-label law forces every factored trace to have at
least as many bits as the semantic continuation. -/
theorem trace_length_ge_of_fourwise_distanceThree
    {m k N : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (trace : Assignment m -> Assignment k)
    (cellOf : Assignment m -> Cell)
    (hfactor : CellMapFactorsThrough trace cellOf)
    (hfour : CellFourwiseRadiusCompatible C cellOf (R := 1))
    (hsep : MinimumDistanceAtLeastThree C) :
    m <= k := by
  have hcell :=
    (fourwise_iff_cellOf_injective_of_distanceThree C cellOf hsep).mp hfour
  exact trace_length_ge_of_factored_injective_cellMap
    trace cellOf hfactor hcell

/-- Therefore a strictly short trace cannot satisfy the separated four-label
law. -/
theorem shortTrace_not_fourwise_distanceThree
    {m k N : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (trace : Assignment m -> Assignment k)
    (cellOf : Assignment m -> Cell)
    (hfactor : CellMapFactorsThrough trace cellOf)
    (hshort : k < m)
    (hsep : MinimumDistanceAtLeastThree C) :
    ¬ CellFourwiseRadiusCompatible C cellOf (R := 1) := by
  intro hfour
  have hmk := trace_length_ge_of_fourwise_distanceThree
    C trace cellOf hfactor hfour hsep
  omega

/-- For a short factored trace, asserting that solver correctness forces the
four-label law is exactly asserting that the alleged solver is not correct. -/
theorem correctnessForces_shortTrace_fourwise_iff_not_decidesSAT
    {U : MachineModel} (D : DecisionMachine U)
    {m k N : Nat} {Cell : Type} [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (trace : Assignment m -> Assignment k)
    (cellOf : Assignment m -> Cell)
    (hfactor : CellMapFactorsThrough trace cellOf)
    (hshort : k < m)
    (hsep : MinimumDistanceAtLeastThree C) :
    (DecidesSAT U D ->
      CellFourwiseRadiusCompatible C cellOf (R := 1)) ↔
      ¬ DecidesSAT U D := by
  have hnotfour := shortTrace_not_fourwise_distanceThree
    C trace cellOf hfactor hshort hsep
  constructor
  · intro hforce hD
    exact hnotfour (hforce hD)
  · intro hnotD hD
    exact (hnotD hD).elim

/-! ## Tightness at full semantic length -/

/-- The complete continuation label, viewed as its own trace. -/
def fullLabelTrace (m : Nat) : Assignment m -> Assignment m := id

/-- The identity cell map factors through the full-label trace. -/
theorem fullLabelCell_factorsThrough_fullLabelTrace (m : Nat) :
    CellMapFactorsThrough (fullLabelTrace m) (id : Assignment m -> Assignment m) := by
  exact ⟨id, fun _ => rfl⟩

/-- Retaining the complete continuation label makes the induced cell map
injective. -/
theorem fullLabelCell_injective (m : Nat) :
    Function.Injective (id : Assignment m -> Assignment m) :=
  Function.injective_id

/-- At the threshold `k = m`, the full-label cell map satisfies the four-label
law for every code (and hence in particular for distance-three codes). -/
theorem fullLabelCell_fourwise
    {m N : Nat} (C : RedundantContinuationCode m N) :
    CellFourwiseRadiusCompatible C
      (id : Assignment m -> Assignment m) (R := 1) :=
  fourwise_of_cellOf_injective C id Function.injective_id

end PallLean.Paper93.DeepMath.PathB.NFrameTraceLengthThreshold

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTraceLengthThreshold.two_pow_le_two_pow_of_traceFactored_injective_cellMap
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTraceLengthThreshold.trace_length_ge_of_factored_injective_cellMap
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTraceLengthThreshold.shortTrace_factored_cellMap_not_injective
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTraceLengthThreshold.trace_length_ge_of_fourwise_distanceThree
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTraceLengthThreshold.shortTrace_not_fourwise_distanceThree
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTraceLengthThreshold.correctnessForces_shortTrace_fourwise_iff_not_decidesSAT
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameTraceLengthThreshold.fullLabelCell_fourwise
