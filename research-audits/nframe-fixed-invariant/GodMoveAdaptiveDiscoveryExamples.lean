import GodMoveAdaptiveDiscovery

/-!
# Executable adaptive-discovery examples with an exhaustive oracle

The concrete oracle in this file enumerates its entire Boolean input cube.
It satisfies the decision-oracle interface, allowing the conditional adaptive
algorithm to run without any missing implementation. The guarded evaluations
check actual samples, selected wire indices, and the search's query counter.

Counting oracle calls does not count the assignments inspected inside those
calls. These examples demonstrate executable correctness, not polynomial-time
sample discovery. The reported counter belongs to `adaptiveSearch`; evaluating
`adaptiveBasisIndices` separately repeats that search in these test snapshots.
-/

namespace GodMoveAdaptiveDiscoveryExamples

open GodMoveBooleanInterpolation GodMoveBooleanWireTable GodMoveCubeWitnessSearch
open GodMoveAdaptiveDiscovery GodMoveSamplingBarrier
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer (CGate)

/-- A complete implementation for examples, with exponential internal search. -/
def exhaustiveOracle : CubeOracle := fun n p => (allAssignments n).any p

theorem exhaustiveOracle_correct : OracleCorrect exhaustiveOracle := by
  intro n p
  simp only [exhaustiveOracle, List.any_eq_true]
  constructor
  · rintro ⟨a, _, ha⟩
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, allAssignments_complete n a, ha⟩

theorem samples_separate {n : ℕ} (c : List (CGate n)) :
    SeparatesWires c (adaptiveSamples exhaustiveOracle c) :=
  adaptiveSamples_separates exhaustiveOracle exhaustiveOracle_correct c

/-- Inspect samples and original wire indices. The final number is the
instrumented counter returned by the displayed `adaptiveSearch` call. -/
def snapshot {n : ℕ} (c : List (CGate n)) :
    List (List Bool) × List ℕ × ℕ :=
  let found := adaptiveSearch exhaustiveOracle c
  (found.samples.map List.ofFn,
    (adaptiveBasisIndices exhaustiveOracle c).map Fin.val, found.queries)

def andCircuit : List (CGate 2) := [.var 0, .var 1, .bin (· && ·) 0 1]

def duplicateCircuit : List (CGate 1) := [.var 0, .var 0]

def contradictionAndConstant : List (CGate 1) :=
  [.var 0, .un (! ·) 0, .bin (· && ·) 0 1, .cst true]

/-- Out-of-range reads contribute `false`; the last two gates reuse a wire. -/
def malformedAndReuse : List (CGate 1) :=
  [.bin (· || ·) 7 9, .un (! ·) 8, .var 0,
    .bin (· && ·) 2 2, .bin (· || ·) 0 3]

/-- info: true -/
#guard_msgs in
#eval decide (snapshot ([] : List (CGate 0)) = ([], [], 1))

/- Three independent rows use three witness searches with three queries
each, followed by a single query certifying that no new row exists. -/
/-- info: true -/
#guard_msgs in
#eval decide (snapshot andCircuit =
  ([[false, true], [true, false], [true, true]], [0, 1, 2], 10))

/-- info: true -/
#guard_msgs in
#eval decide (snapshot duplicateCircuit = ([[true]], [0], 3))

/-- info: true -/
#guard_msgs in
#eval decide (snapshot contradictionAndConstant = ([[false], [true]], [0, 1], 5))

/-- info: true -/
#guard_msgs in
#eval decide (snapshot malformedAndReuse = ([[false], [true]], [1, 2], 5))

/-- info: true -/
#guard_msgs in
#eval decide (snapshot ([.cst true] : List (CGate 0)) = ([[]], [0], 2))

end GodMoveAdaptiveDiscoveryExamples

#print axioms GodMoveAdaptiveDiscoveryExamples.exhaustiveOracle_correct
#print axioms GodMoveAdaptiveDiscoveryExamples.samples_separate
