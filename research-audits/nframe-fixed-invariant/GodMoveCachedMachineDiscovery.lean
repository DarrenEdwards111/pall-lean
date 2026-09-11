import GodMoveMachineDiscovery
import GodMoveCachedDiscoveryBasis
import GodMoveCachedRowFinder

/-!
# Adaptive machine discovery with materialized orthogonal rows

Each round materializes the residual coefficient matrix before performing the
existing encoded-query procedure on its stored rows. Each successful round runs
the supplied circuit once to materialize its Boolean wire row, then performs one
cached orthogonal insertion. The result, including the reported SAT-machine query
count, equals the existing discovery result for the semantic row basis.

The additional operation counter measures rational arithmetic in the residual
matrices and insertions. It excludes rational clearing, query construction, SAT
execution, circuit evaluation, comparisons, allocation, indexing, and integer
bit costs.
-/

namespace GodMoveCachedMachineDiscovery

open GodMoveBooleanInterpolation GodMoveBooleanWireTable
open GodMoveCachedDiscoveryBasis
open GodMoveTrackedOrthogonalization (rowValue)
open GodMoveTrackedOrthogonalizationCost (Counted)
open GodMoveAdaptiveDiscovery (SearchResult)
open GodMoveCachedRowFinder (findRowWithCount findRowWithCount_value)
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer (CGate runFrom)
open ComposableMachine SeparationTarget

/-- Cache the circuit trace before materializing all rational row coordinates. -/
def cachedWireRow {n : ℕ} (c : List (CGate n)) (a : Assignment n) :
    Vector ℚ c.length :=
  let values := runFrom a [] c
  Vector.ofFn (fun i => bit (values.getD i.val false))

@[simp] theorem cachedWireRow_value {n : ℕ} (c : List (CGate n))
    (a : Assignment n) : rowValue (cachedWireRow c a) = wireRow c a := by
  funext i
  simp [rowValue, cachedWireRow, wireRow]

/-- Discovery reuses stored numeric basis rows between successive SAT queries. -/
def discover (M : Machine) (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n)) :
    ℕ → CachedBasis c.length → Counted (SearchResult n)
  | 0, _ => ⟨⟨[], 0⟩, 0⟩
  | fuel + 1, B =>
    let attempt := findRowWithCount M T c B
    match attempt.value.1 with
    | none => ⟨⟨[], attempt.value.2⟩, attempt.operations⟩
    | some a =>
      let next := insert B (cachedWireRow c a)
      let rest := discover M T c fuel next.value
      ⟨⟨a :: rest.value.samples, attempt.value.2 + rest.value.queries⟩,
        attempt.operations + next.operations + rest.operations⟩

/-- Erasing the arithmetic counter gives precisely the original discovery. -/
theorem discover_value (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (fuel : ℕ) (B : CachedBasis c.length) :
    (discover M T c fuel B).value =
      GodMoveMachineDiscovery.discover M T c fuel B.toRowBasis := by
  induction fuel generalizing B with
  | zero => rfl
  | succ fuel ih =>
    cases ha : (GodMoveMachineRowFinder.findRowWithCount M T c B.toRowBasis).1 with
    | none => simp only [discover, findRowWithCount_value, GodMoveMachineDiscovery.discover, ha]
    | some a =>
      simp only [discover, findRowWithCount_value, GodMoveMachineDiscovery.discover, ha, ih,
        insert_value, cachedWireRow_value]

/-- This counts executed residual-matrix and basis-insertion arithmetic. -/
theorem discover_operations_le (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (fuel : ℕ) (B : CachedBasis c.length) :
    (discover M T c fuel B).operations ≤ fuel * 16 * (c.length + 1) ^ 3 := by
  induction fuel generalizing B with
  | zero => simp [discover]
  | succ fuel ih =>
    have hattempt := GodMoveCachedRowFinder.findRowWithCount_operations_le M T c B
    cases ha : (findRowWithCount M T c B).value.1 with
    | none =>
      simp only [discover, ha]
      calc
        _ ≤ 4 * (c.length + 1) ^ 3 := hattempt
        _ ≤ (fuel + 1) * 16 * (c.length + 1) ^ 3 := by nlinarith
    | some a =>
      have hrest := ih (insert B (cachedWireRow c a)).value
      have hnext := insert_operations_le_quadratic B (cachedWireRow c a)
      have hpow : (c.length + 1) ^ 2 ≤ (c.length + 1) ^ 3 := by
        nlinarith [Nat.zero_le (c.length * (c.length + 1) ^ 2)]
      have hround : (findRowWithCount M T c B).operations +
          (insert B (cachedWireRow c a)).operations ≤ 16 * (c.length + 1) ^ 3 := by
        nlinarith
      simp only [discover, ha]
      calc
        _ ≤ 16 * (c.length + 1) ^ 3 + fuel * 16 * (c.length + 1) ^ 3 :=
          Nat.add_le_add hround hrest
        _ = (fuel + 1) * 16 * (c.length + 1) ^ 3 := by ring

/-- The original query bound transports independently of SAT correctness. -/
theorem discover_queries_le (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (fuel : ℕ) (B : CachedBasis c.length) :
    (discover M T c fuel B).value.queries ≤ fuel * (c.length * (n + 1)) := by
  rw [discover_value]
  exact GodMoveMachineDiscovery.discover_query_budget M T c fuel B.toRowBasis

def machineSearch (M : Machine) (T : ℕ → ℕ) {n : ℕ} (c : List (CGate n)) :
    Counted (SearchResult n) :=
  discover M T c (c.length + 1) (empty c.length)

def machineSamples (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) : List (Assignment n) :=
  (machineSearch M T c).value.samples

theorem machineSearch_value (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) :
    (machineSearch M T c).value = GodMoveMachineDiscovery.machineSearch M T c := by
  simp only [machineSearch, discover_value, empty_value, GodMoveMachineDiscovery.machineSearch]

theorem machineSamples_eq (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) :
    machineSamples M T c = GodMoveMachineDiscovery.machineSamples M T c := by
  simp only [machineSamples, machineSearch_value, GodMoveMachineDiscovery.machineSamples]

theorem machineSearch_operations_le_quartic (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) :
    (machineSearch M T c).operations ≤ 16 * (c.length + 1) ^ 4 := by
  calc
    _ ≤ (c.length + 1) * 16 * (c.length + 1) ^ 3 :=
      discover_operations_le M T c (c.length + 1) (empty c.length)
    _ = 16 * (c.length + 1) ^ 4 := by ring

theorem machineSearch_queries_le (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) :
    (machineSearch M T c).value.queries ≤
      (c.length + 1) * (c.length * (n + 1)) := by
  rw [machineSearch_value]
  exact GodMoveMachineDiscovery.machineSearch_queries_le M T c

/-- Exact result transport retains the original successful-refinement proof. -/
theorem machineSamples_separates (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n)) :
    GodMoveSamplingBarrier.SeparatesWires c (machineSamples M T c) := by
  rw [machineSamples_eq]
  exact GodMoveMachineDiscovery.machineSamples_separates M T hD c

end GodMoveCachedMachineDiscovery

#print axioms GodMoveCachedMachineDiscovery.cachedWireRow_value
#print axioms GodMoveCachedMachineDiscovery.discover_value
#print axioms GodMoveCachedMachineDiscovery.discover_operations_le
#print axioms GodMoveCachedMachineDiscovery.discover_queries_le
#print axioms GodMoveCachedMachineDiscovery.machineSearch_value
#print axioms GodMoveCachedMachineDiscovery.machineSamples_eq
#print axioms GodMoveCachedMachineDiscovery.machineSearch_operations_le_quartic
#print axioms GodMoveCachedMachineDiscovery.machineSearch_queries_le
#print axioms GodMoveCachedMachineDiscovery.machineSamples_separates
