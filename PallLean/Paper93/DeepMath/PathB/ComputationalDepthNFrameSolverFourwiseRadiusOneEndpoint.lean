import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameRadiusOneFourHellyEndpoint

/-!
# Solver-indexed fourwise radius-one endpoint

The radius-one four-Helly theorem turns the missing global received-word bridge
into a finite semantic law: any four continuation labels assigned to one
solver-induced cell have encoded codewords in a common radius-one ball.

This file wires that law back to the SAT separation endpoints in two forms.

* For an arbitrary injective code, polynomial encoded length gives the `N + 1`
  sphere bound and contradicts polynomially many cells.
* For a code of minimum distance at least three, fourwise compatibility glues to
  a projection which already forces the cell map to be injective; no encoded
  length bound is needed.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameSolverFourwiseRadiusOneEndpoint

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameRedundantExpanderCodeEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameReceivedWordListDecodingBridge
open PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneSphereEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneDistanceBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneLocalityThreshold
open PallLean.Paper93.DeepMath.PathB.NFrameRadiusOneFourHellyEndpoint

/-! ## Exact semantic replacement -/

/-- For a fixed solver cell map, correctness-derived fourwise compatibility is
exactly correctness-derived global received-word projection. -/
theorem decides_fourwise_iff_decides_projection
    {U : MachineModel} {D : DecisionMachine U}
    {m N : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (C : RedundantContinuationCode m N)
    (cellOf : Assignment m -> Cell) :
    (DecidesSAT U D ->
      CellFourwiseRadiusCompatible C cellOf (R := 1)) ↔
    (DecidesSAT U D ->
      Nonempty (CellReceivedWordProjection C cellOf 1)) := by
  constructor
  · intro hfour hD
    exact ⟨radiusOneProjectionOfFourwise C cellOf (hfour hD)⟩
  · intro hproj hD
    obtain ⟨P⟩ := hproj hD
    exact projection_to_fourwise C cellOf P

/-! ## Polynomial-length sphere-capacity cashout -/

/-- Solver-indexed finite four-label law with polynomial cell count and encoded
length. -/
structure SolverFourwiseRadiusOneFor
    (U : MachineModel) (D : DecisionMachine U) where
  m : Nat
  N : Nat
  k : Nat
  d : Nat
  code : RedundantContinuationCode m N
  Cell : Type
  cellFintype : Fintype Cell
  cellDecidableEq : DecidableEq Cell
  cellOf : Assignment m -> Cell
  polyCells : @Fintype.card Cell cellFintype <= m ^ k
  polyEncodedLength : N + 1 <= m ^ d
  fourwise_of_decides : DecidesSAT U D ->
    @CellFourwiseRadiusCompatible m N 1 Cell cellDecidableEq code cellOf
  expGap : m ^ (k + d) < 2 ^ m

namespace SolverFourwiseRadiusOneFor

variable {U : MachineModel} {D : DecisionMachine U}

/-- The finite four-label semantic law constructs the formerly global
received-word projection. -/
noncomputable def projection_of_decides
    (B : SolverFourwiseRadiusOneFor U D) (hD : DecidesSAT U D) :
    @CellReceivedWordProjection B.m B.N B.Cell B.cellDecidableEq
      B.code B.cellOf 1 := by
  letI : Fintype B.Cell := B.cellFintype
  letI : DecidableEq B.Cell := B.cellDecidableEq
  exact radiusOneProjectionOfFourwise B.code B.cellOf
    (B.fourwise_of_decides hD)

/-- Polynomially many cells and polynomial encoded length make the four-label
law incompatible with SAT correctness. -/
theorem not_decidesSAT (B : SolverFourwiseRadiusOneFor U D) :
    ¬ DecidesSAT U D := by
  intro hD
  letI : Fintype B.Cell := B.cellFintype
  letI : DecidableEq B.Cell := B.cellDecidableEq
  exact no_polynomial_cells_with_radiusOneProjection B.code B.cellOf
    (B.projection_of_decides hD) B.polyCells B.polyEncodedLength B.expGap

end SolverFourwiseRadiusOneFor

/-- Four-label radius-one packages for every certified machine rule out
polynomial SAT decision. -/
theorem no_SATDecisionInP_of_solverFourwiseRadiusOne
    {U : MachineModel}
    (H : forall D : DecisionMachine U,
      Nonempty (SolverFourwiseRadiusOneFor U D)) :
    ¬ SATDecisionInP U := by
  rintro ⟨D, hD⟩
  obtain ⟨B⟩ := H D
  exact B.not_decidesSAT hD

/-! ## Distance-three cashout without an encoded-length bound -/

/-- With minimum distance at least three, the same four-label law already
forces complete semantic preservation by the cell map. -/
structure SolverSeparatedFourwiseRadiusOneFor
    (U : MachineModel) (D : DecisionMachine U) where
  m : Nat
  N : Nat
  k : Nat
  code : RedundantContinuationCode m N
  codeDistanceThree : MinimumDistanceAtLeastThree code
  Cell : Type
  cellFintype : Fintype Cell
  cellDecidableEq : DecidableEq Cell
  cellOf : Assignment m -> Cell
  polyCells : @Fintype.card Cell cellFintype <= m ^ k
  fourwise_of_decides : DecidesSAT U D ->
    @CellFourwiseRadiusCompatible m N 1 Cell cellDecidableEq code cellOf
  expGap : m ^ k < 2 ^ m

namespace SolverSeparatedFourwiseRadiusOneFor

variable {U : MachineModel} {D : DecisionMachine U}

/-- A correctness-derived four-label law for a distance-three code refutes the
alleged solver without any block-length estimate. -/
theorem not_decidesSAT (B : SolverSeparatedFourwiseRadiusOneFor U D) :
    ¬ DecidesSAT U D := by
  intro hD
  letI : Fintype B.Cell := B.cellFintype
  letI : DecidableEq B.Cell := B.cellDecidableEq
  let P := radiusOneProjectionOfFourwise B.code B.cellOf
    (B.fourwise_of_decides hD)
  exact no_polynomial_cells_with_radiusOne_and_distanceThree
    B.code B.cellOf P B.codeDistanceThree B.polyCells B.expGap

end SolverSeparatedFourwiseRadiusOneFor

/-- Separated-code four-label packages for every certified machine also rule
out polynomial SAT decision. -/
theorem no_SATDecisionInP_of_solverSeparatedFourwiseRadiusOne
    {U : MachineModel}
    (H : forall D : DecisionMachine U,
      Nonempty (SolverSeparatedFourwiseRadiusOneFor U D)) :
    ¬ SATDecisionInP U := by
  rintro ⟨D, hD⟩
  obtain ⟨B⟩ := H D
  exact B.not_decidesSAT hD

end PallLean.Paper93.DeepMath.PathB.NFrameSolverFourwiseRadiusOneEndpoint

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSolverFourwiseRadiusOneEndpoint.decides_fourwise_iff_decides_projection
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSolverFourwiseRadiusOneEndpoint.SolverFourwiseRadiusOneFor.not_decidesSAT
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSolverFourwiseRadiusOneEndpoint.no_SATDecisionInP_of_solverFourwiseRadiusOne
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSolverFourwiseRadiusOneEndpoint.SolverSeparatedFourwiseRadiusOneFor.not_decidesSAT
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameSolverFourwiseRadiusOneEndpoint.no_SATDecisionInP_of_solverSeparatedFourwiseRadiusOne
