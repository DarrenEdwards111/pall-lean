import GodMoveCachedSelection
import GodMoveCachedMachineDiscovery
import GodMoveConstructedProjectionPrecision

/-!
# A stored projection descriptor using cached discovery and column selection

The wrapper retains the search result, selected column list and inverse result
before returning one size-indexed descriptor. Both row-basis scans use cached
rows instead of nested residual closures. Exact erasure preserves the existing
machine-discovered wire projection.

`operations` counts the rational arithmetic in residual-matrix construction,
adaptive basis insertion, column selection and inverse construction. It does
not count coefficient clearing, query-circuit compilation, SAT calls, Boolean
execution, indexing, comparisons or bit-level integer operations. Therefore
the polynomial bound here is not total runtime.
-/

namespace GodMoveCachedProjectionConstruction

open GodMoveBooleanInterpolation GodMoveProjectionSamples GodMoveConstructedProjection
open GodMoveTrackedOrthogonalizationCost (Counted)
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer (CGate)
open ComposableMachine SeparationTarget

/-- The size is stored with the descriptor rather than rediscovered when a
caller asks for its dependent array type. -/
structure Result {n : ℕ} (c : List (CGate n)) where
  size : ℕ
  descriptor : Descriptor c size
  queries : ℕ

private def finish {n : ℕ} (c : List (CGate n)) (samples : List (Assignment n))
    (indices : List (Fin c.length)) (hlen : indices.length = samples.length)
    (queries : ℕ) : Counted (Result c) :=
  let inverse := buildDescriptorWithCost (ofLists c samples indices hlen)
  ⟨⟨samples.length, inverse.value, queries⟩, inverse.operations⟩

def construct (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    {n : ℕ} (c : List (CGate n)) : Counted (Result c) :=
  let search := GodMoveCachedMachineDiscovery.machineSearch M T c
  let samples := search.value.samples
  let chosen := GodMoveCachedSelection.selectedIndices c samples
  have hlen : chosen.value.length = samples.length := by
    dsimp only [chosen, samples, search]
    rw [GodMoveCachedSelection.selectedIndices_value,
      GodMoveCachedMachineDiscovery.machineSearch_value]
    exact machine_sample_basis_length M T hD c
  let result := finish c samples chosen.value hlen search.value.queries
  ⟨result.value, search.operations + chosen.operations + result.operations⟩

theorem construct_value (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    {n : ℕ} (c : List (CGate n)) :
    (construct M T hD c).value =
      ⟨(GodMoveMachineDiscovery.machineSamples M T c).length,
        machineDescriptor M T hD c, (GodMoveMachineDiscovery.machineSearch M T c).queries⟩ := by
  simp only [construct, GodMoveCachedMachineDiscovery.machineSearch_value,
    GodMoveCachedSelection.selectedIndices_value]
  rfl

/-- The executed residual, basis and inverse loops have a common quartic bound.
Query construction and the SAT machine's steps are not part of this counter. -/
theorem construct_basis_operations_le (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n)) :
    (construct M T hD c).operations ≤ 32 * (c.length + 1) ^ 4 := by
  have hs := GodMoveCachedMachineDiscovery.machineSearch_operations_le_quartic M T c
  have hsample := GodMoveConstructedProjectionPrecision.machineSamples_length_le_circuit M T hD c
  have hsel := GodMoveCachedSelection.selectedIndices_operations_le c
    (GodMoveCachedMachineDiscovery.machineSearch M T c).value.samples
  simp only [GodMoveCachedMachineDiscovery.machineSearch_value] at hsel
  change (GodMoveCachedSelection.selectedIndices c
    (GodMoveMachineDiscovery.machineSamples M T c)).operations ≤
      c.length * (8 * ((GodMoveMachineDiscovery.machineSamples M T c).length + 1) ^ 2) at hsel
  have hinv := buildDescriptor_operations_le_cubic (machineSampleData M T hD c)
  have hsel' : (GodMoveCachedSelection.selectedIndices c
      (GodMoveMachineDiscovery.machineSamples M T c)).operations ≤
        8 * (c.length + 1) ^ 3 := by
    apply hsel.trans
    have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hsample 1) 2
    nlinarith [Nat.mul_le_mul_left (8 * c.length) hp]
  have hinv' : (buildDescriptorWithCost (machineSampleData M T hD c)).operations ≤
      8 * (c.length + 1) ^ 3 := by
    apply hinv.trans
    exact Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (by omega) 3)
  have he : (construct M T hD c).operations =
      (GodMoveCachedMachineDiscovery.machineSearch M T c).operations +
        (GodMoveCachedSelection.selectedIndices c (GodMoveMachineDiscovery.machineSamples M T c)).operations +
        (buildDescriptorWithCost (machineSampleData M T hD c)).operations := by
    simp only [construct, GodMoveCachedMachineDiscovery.machineSearch_value,
      GodMoveCachedSelection.selectedIndices_value]
    rfl
  rw [he]
  have hp : (c.length + 1) ^ 3 ≤ (c.length + 1) ^ 4 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem construct_query_count (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n)) :
    (construct M T hD c).value.queries ≤ (c.length + 1) * (c.length * (n + 1)) := by
  rw [construct_value]
  exact GodMoveMachineDiscovery.machineSearch_queries_le M T c

end GodMoveCachedProjectionConstruction

#print axioms GodMoveCachedProjectionConstruction.construct_value
#print axioms GodMoveCachedProjectionConstruction.construct_basis_operations_le
#print axioms GodMoveCachedProjectionConstruction.construct_query_count
