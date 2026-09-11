import GodMoveCachedArithmeticPrecision
import GodMoveCachedProjectionConstruction

/-!
# Rational-stage precision along the cached construction

The predicates below follow the actual branches of cached discovery and the
actual insertion sequence of cached column selection. Every reached residual
matrix and every executed insertion has the proved canonical-rational precision
certificate. Rejected and duplicate Boolean rows are included.

The combined construction theorem also covers the inverse kernel on the exact
sample data stored in the returned descriptor. These are bounds on rational
stages, not on internal integer operations, coefficient clearing, query-circuit
compilation, allocation, or complete machine runtime. No derivative-rank bound
or SAT separation is asserted.
-/

namespace GodMoveCachedConstructionPrecision

open GodMoveBooleanInterpolation GodMoveBooleanWireTable
open GodMoveCachedDiscoveryBasis GodMoveCachedBasisPrecision
open GodMoveCachedArithmeticPrecision
open GodMoveTrackedOrthogonalization (Row rowValue)
open GodMoveTrackedArithmeticPrecision (arithmeticBits InversePrecision)
open GodMoveConstructedProjectionPrecision (descriptorInput)
open GodMoveProjectionSamples (machineSampleData)
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer (CGate)
open ComposableMachine SeparationTarget

private theorem bit_boolean (b : Bool) : bit b = 0 ∨ bit b = 1 := by
  cases b <;> simp [bit]

/-- The cached numeric row is Boolean regardless of how the sample was found. -/
theorem cachedWireRow_boolean {n : ℕ} (c : List (CGate n)) (a : Assignment n) :
    BooleanRow (rowValue (GodMoveCachedMachineDiscovery.cachedWireRow c a)) := by
  rw [GodMoveCachedMachineDiscovery.cachedWireRow_value]
  intro j
  exact bit_boolean _

/-- The matrix is computed even on a final unsuccessful attempt. An insertion
certificate is required only on the successful branch where it is executed. -/
def DiscoveryPrecision (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (b : ℕ) : ℕ → CachedBasis c.length → Prop
  | 0, _ => True
  | fuel + 1, B =>
      MatrixPrecision B b ∧
        match (GodMoveCachedRowFinder.findRowWithCount M T c B).value.1 with
        | none => True
        | some a =>
            InsertPrecision B (GodMoveCachedMachineDiscovery.cachedWireRow c a) b ∧
              DiscoveryPrecision M T c b fuel
                (insert B (GodMoveCachedMachineDiscovery.cachedWireRow c a)).value

/-- Boolean generation and stored-row precision are maintained at every
reachable discovery state. No SAT-correctness premise is needed for this fact. -/
theorem discover_precision (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) (fuel : ℕ) (B : CachedBasis c.length) (hB : Ready B) :
    DiscoveryPrecision M T c (arithmeticBits c.length) fuel B := by
  induction fuel generalizing B with
  | zero => trivial
  | succ fuel ih =>
    refine ⟨matrix_precision B hB, ?_⟩
    cases ha : (GodMoveCachedRowFinder.findRowWithCount M T c B).value.1 with
    | none => trivial
    | some a =>
      exact ⟨insert_precision B hB _ (cachedWireRow_boolean c a),
        ih _ (insert_ready B hB _ (cachedWireRow_boolean c a))⟩

theorem machineSearch_precision (M : Machine) (T : ℕ → ℕ) {n : ℕ}
    (c : List (CGate n)) :
    DiscoveryPrecision M T c (arithmeticBits c.length)
      (c.length + 1) (empty c.length) :=
  discover_precision M T c _ _ (empty_ready _)

/-- The selection loop executes one insertion for each supplied row, including
rows that leave the basis unchanged and are omitted from its output. -/
def ScanPrecision {α : Type*} {s : ℕ} (b : ℕ) (B : CachedBasis s) :
    List (α × Row s) → Prop
  | [] => True
  | x :: xs => InsertPrecision B x.2 b ∧ ScanPrecision b (insert B x.2).value xs

theorem scan_precision {α : Type*} {s : ℕ} (B : CachedBasis s) (hB : Ready B)
    (xs : List (α × Row s)) (hxs : ∀ x ∈ xs, BooleanRow (rowValue x.2)) :
    ScanPrecision (arithmeticBits s) B xs := by
  induction xs generalizing B with
  | nil => trivial
  | cons x xs ih =>
    have hx := hxs x List.mem_cons_self
    exact ⟨insert_precision B hB x.2 hx,
      ih _ (insert_ready B hB x.2 hx)
        (fun y hy => hxs y (List.mem_cons_of_mem x hy))⟩

/-- The final cached basis remains ready after all selection insertions. -/
theorem scan_ready {α : Type*} {s : ℕ} (B : CachedBasis s) (hB : Ready B)
    (xs : List (α × Row s)) (hxs : ∀ x ∈ xs, BooleanRow (rowValue x.2)) :
    Ready (GodMoveCachedSelection.scan B xs).value.1 := by
  induction xs generalizing B with
  | nil => exact hB
  | cons x xs ih =>
    exact ih _ (insert_ready B hB x.2 (hxs x List.mem_cons_self))
      (fun y hy => hxs y (List.mem_cons_of_mem x hy))

/-- Every column actually materialized for selection consists of Boolean
wire values at the supplied samples; the samples need not be independent. -/
theorem columns_boolean {n : ℕ} (c : List (CGate n)) (samples : List (Assignment n)) :
    ∀ x ∈ GodMoveCachedSelection.columns c samples, BooleanRow (rowValue x.2) := by
  intro x hx
  dsimp only [GodMoveCachedSelection.columns] at hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  intro j
  simpa [rowValue, GodMoveCachedSelection.wireRows] using
    bit_boolean ((NFrameBoundaryTransducer.runFrom (samples.get j) [] c).getD i.val false)

theorem selectedIndices_precision {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) :
    ScanPrecision (arithmeticBits samples.length) (empty samples.length)
      (GodMoveCachedSelection.columns c samples) :=
  scan_precision _ (empty_ready _) _ (columns_boolean c samples)

/-- Both scans and the inverse certificate refer to the stages and stored
sample data used by the actual cached construction. -/
def ConstructionPrecision (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n)) : Prop :=
  DiscoveryPrecision M T c (arithmeticBits c.length)
      (c.length + 1) (empty c.length) ∧
    (let samples := (GodMoveCachedMachineDiscovery.machineSearch M T c).value.samples;
      ScanPrecision (arithmeticBits samples.length) (empty samples.length)
        (GodMoveCachedSelection.columns c samples)) ∧
    InversePrecision
      (descriptorInput (GodMoveCachedProjectionConstruction.construct M T hD c).value.descriptor.data)
      (arithmeticBits (GodMoveCachedProjectionConstruction.construct M T hD c).value.size)

/-- SAT correctness discharges the sample-matrix independence needed by the
inverse. Neither scan assumes extra precision or basis-selection certificates. -/
theorem construct_precision (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n)) :
    ConstructionPrecision M T hD c := by
  refine ⟨machineSearch_precision M T c, selectedIndices_precision c _, ?_⟩
  rw [GodMoveCachedProjectionConstruction.construct_value]
  exact GodMoveConstructedProjectionPrecision.machineDescriptor_kernel_precision M T hD c

theorem construct_cost_and_precision (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n)) :
    (GodMoveCachedProjectionConstruction.construct M T hD c).operations ≤
        32 * (c.length + 1) ^ 4 ∧ ConstructionPrecision M T hD c :=
  ⟨GodMoveCachedProjectionConstruction.construct_basis_operations_le M T hD c,
    construct_precision M T hD c⟩

/-- Selection and inversion use the discovered sample dimension. Both of their
precision exponents fit the same circuit-width budget used by discovery. -/
theorem construct_precision_budgets_le_circuit (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n)) :
    arithmeticBits (GodMoveCachedMachineDiscovery.machineSearch M T c).value.samples.length ≤
        arithmeticBits c.length ∧
      arithmeticBits (GodMoveCachedProjectionConstruction.construct M T hD c).value.size ≤
        arithmeticBits c.length := by
  rw [GodMoveCachedMachineDiscovery.machineSearch_value,
    GodMoveCachedProjectionConstruction.construct_value]
  have h := GodMoveConstructedProjectionPrecision.machineDescriptor_precision_budget_le_circuit
    M T hD c
  exact ⟨h, h⟩

end GodMoveCachedConstructionPrecision

#print axioms GodMoveCachedConstructionPrecision.cachedWireRow_boolean
#print axioms GodMoveCachedConstructionPrecision.discover_precision
#print axioms GodMoveCachedConstructionPrecision.machineSearch_precision
#print axioms GodMoveCachedConstructionPrecision.scan_precision
#print axioms GodMoveCachedConstructionPrecision.scan_ready
#print axioms GodMoveCachedConstructionPrecision.columns_boolean
#print axioms GodMoveCachedConstructionPrecision.selectedIndices_precision
#print axioms GodMoveCachedConstructionPrecision.construct_precision
#print axioms GodMoveCachedConstructionPrecision.construct_cost_and_precision
#print axioms GodMoveCachedConstructionPrecision.construct_precision_budgets_le_circuit
