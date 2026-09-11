import GodMoveConstructedProjection
import GodMoveTrackedArithmeticPrecision

/-!
# Complete rational-stage precision for the constructed projection weights

The descriptor's actual numeric wrapper materializes the discovered sample
matrix before running the cached inverse. This input table is proved equal
to the already stored Boolean sample table. The complete inverse precision
theorem therefore applies to exactly the kernel used by the descriptor.

Duality, a cubic rational-operation count, and polynomial bounds for every
listed rational stage hold together. For machine-discovered samples, the
needed independence follows from the existing discovery theorem; the caller
does not supply weights, numeric identities, or precision certificates.

The scope is the weight-building kernel after its sample data are available.
No bound for sample discovery, matrix acquisition, bit-level implementation
of rational primitives, expanded polynomial output, or SAT derivative rank
is inferred here.
-/

namespace GodMoveConstructedProjectionPrecision

open GodMoveBooleanInterpolation GodMoveProjectionSamples GodMoveConstructedProjection
open GodMoveTrackedOrthogonalization GodMoveTrackedArithmeticPrecision
open GodMoveMachineDiscovery
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer (CGate)
open ComposableMachine SeparationTarget
open scoped BigOperators

/-- Exactly the table materialized by the descriptor's inverseWeights wrapper. -/
def descriptorInput {n r : ℕ} {c : List (CGate n)} (d : SampleData c r) : Table r :=
  Vector.ofFn (fun i => Vector.ofFn (sampleMatrix d i))

theorem descriptorInput_tableValue {n r : ℕ} {c : List (CGate n)} (d : SampleData c r) :
    tableValue (descriptorInput d) = sampleMatrix d := by
  ext i j
  simp [descriptorInput, tableValue]

/-- Rematerializing the matrix retains the exact stored sample entries. -/
theorem descriptorInput_eq_sampleTable {n r : ℕ} {c : List (CGate n)} (d : SampleData c r) :
    descriptorInput d = sampleTable d := by
  ext i j
  simp [descriptorInput, sampleMatrix, Vector.get]

theorem sampleTable_tableValue {n r : ℕ} {c : List (CGate n)} (d : SampleData c r) :
    tableValue (sampleTable d) = sampleMatrix d := by
  rw [← descriptorInput_eq_sampleTable d, descriptorInput_tableValue]

theorem descriptorInput_boolean {n r : ℕ} {c : List (CGate n)} (d : SampleData c r) :
    ∀ i j, tableValue (descriptorInput d) i j = 0 ∨
      tableValue (descriptorInput d) i j = 1 := by
  rw [descriptorInput_tableValue]
  exact sampleMatrix_boolean d

theorem descriptorInput_independent {n r : ℕ} {c : List (CGate n)} (d : SampleData c r)
    (hLI : LinearIndependent ℚ (sampleMatrix d)) :
    LinearIndependent ℚ (tableValue (descriptorInput d)) := by
  rw [descriptorInput_tableValue]
  exact hLI

/-- The counted descriptor uses this exact inverse kernel, with no additional
rational arithmetic charged for storing its output matrix. -/
theorem buildDescriptor_operations_eq_kernel {n r : ℕ} {c : List (CGate n)}
    (d : SampleData c r) :
    (buildDescriptorWithCost d).operations =
      (GodMoveTrackedOrthogonalizationCost.inverseTable (descriptorInput d)).operations := rfl

theorem buildDescriptor_weights_eq_kernel {n r : ℕ} {c : List (CGate n)}
    (d : SampleData c r) (i j : Fin r) :
    ((buildDescriptor d).weights.get i).get j =
      tableValue (GodMoveTrackedOrthogonalizationCost.inverseTable (descriptorInput d)).value i j := by
  rw [buildDescriptor_weights_eq_inverse,
    GodMoveTrackedOrthogonalizationCost.inverseTable_value]
  rfl

/-- All scalar stages refer to the same numeric input used by the constructed
descriptor. Boolean entries and independence discharge every precision premise. -/
theorem descriptor_kernel_precision {n r : ℕ} {c : List (CGate n)}
    (d : SampleData c r) (hLI : LinearIndependent ℚ (sampleMatrix d)) :
    InversePrecision (descriptorInput d) (arithmeticBits r) :=
  inverse_precision (descriptorInput d) (descriptorInput_boolean d)
    (descriptorInput_independent d hLI)

theorem descriptor_kernel_correct_cost_precision {n r : ℕ} {c : List (CGate n)}
    (d : SampleData c r) (hLI : LinearIndependent ℚ (sampleMatrix d)) :
    tableValue (GodMoveTrackedOrthogonalizationCost.inverseTable (descriptorInput d)).value *
        sampleMatrix d = 1 ∧
      (buildDescriptorWithCost d).operations ≤ 8 * r ^ 3 ∧
      InversePrecision (descriptorInput d) (arithmeticBits r) := by
  have h := inverse_correct_cost_precision (descriptorInput d) (descriptorInput_boolean d)
    (descriptorInput_independent d hLI)
  simpa only [descriptorInput_tableValue, buildDescriptor_operations_eq_kernel] using h

/-- Actual descriptor duality, actual rational-operation count, and complete
rational-stage precision, for one and the same constructed numeric kernel. -/
theorem buildDescriptor_duality_cost_precision {n r : ℕ} {c : List (CGate n)}
    (d : SampleData c r) (hLI : LinearIndependent ℚ (sampleMatrix d)) :
    (∀ i k : Fin r,
      (∑ j : Fin r, ((buildDescriptor d).weights.get i).get j *
        MvPolynomial.eval (booleanPoint (d.points.get j))
          (GodMoveRowSpanSeparation.wirePolynomial c (d.indices.get k))) =
        if i = k then 1 else 0) ∧
      (buildDescriptorWithCost d).operations ≤ 8 * r ^ 3 ∧
      InversePrecision (descriptorInput d) (arithmeticBits r) := by
  exact ⟨buildDescriptor_duality d hLI,
    (descriptor_kernel_correct_cost_precision d hLI).2⟩

/-- The actual machine-discovered sample data require no extra independence
or precision certificate from the caller. -/
theorem machineDescriptor_kernel_precision (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n)) :
    InversePrecision (descriptorInput (machineSampleData M T hD c))
      (arithmeticBits (machineSamples M T c).length) :=
  descriptor_kernel_precision _ (machineSampleData_rows_linearIndependent M T hD c)

theorem machineDescriptor_duality_cost_precision (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n)) :
    (∀ i k : Fin (machineSamples M T c).length,
      (∑ j : Fin (machineSamples M T c).length,
        ((machineDescriptor M T hD c).weights.get i).get j *
          MvPolynomial.eval (booleanPoint ((machineSampleData M T hD c).points.get j))
            (GodMoveRowSpanSeparation.wirePolynomial c
              ((machineSampleData M T hD c).indices.get k))) =
        if i = k then 1 else 0) ∧
      (buildDescriptorWithCost (machineSampleData M T hD c)).operations ≤
        8 * (machineSamples M T c).length ^ 3 ∧
      InversePrecision (descriptorInput (machineSampleData M T hD c))
        (arithmeticBits (machineSamples M T c).length) :=
  buildDescriptor_duality_cost_precision _
    (machineSampleData_rows_linearIndependent M T hD c)

/-- In particular the same precision certificate applies to the faithful
unrolling of the supplied SAT machine on each original encoded input length. -/
theorem actualSAT_descriptor_kernel_precision (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) (L : ℕ) :
    let c := ComposablePpolyDischarge.circuitFor M L (T L)
    InversePrecision (descriptorInput (machineSampleData M T hD c))
      (arithmeticBits (machineSamples M T c).length) :=
  machineDescriptor_kernel_precision M T hD _

/-- Discovery retains at most one sample per independent computed wire. -/
theorem machineSamples_length_le_circuit (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n)) :
    (machineSamples M T c).length ≤ c.length := by
  rw [machineSamples_length_eq_wireRank M T hD c]
  exact GodMoveComputedWireRank.wireRank_le_length c

theorem machineDescriptor_precision_budget_le_circuit (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n)) :
    arithmeticBits (machineSamples M T c).length ≤ 100 * (c.length + 1) ^ 4 := by
  exact Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left
    (Nat.add_le_add_right (machineSamples_length_le_circuit M T hD c) 1) 4)

/-- This bounds the exponent in the numeric-kernel precision certificate by
the actual unrolling clock. It does not bound discovery time or bit-machine time. -/
theorem actualSAT_descriptor_precision_budget_le_clock (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) (L : ℕ) :
    let c := ComposablePpolyDischarge.circuitFor M L (T L)
    arithmeticBits (machineSamples M T c).length ≤
      100 * (GodMoveCircuitRuntimeCost.circuitConstant M * (L + T L + 1) ^ 4 + 1) ^ 4 := by
  exact (machineDescriptor_precision_budget_le_circuit M T hD _).trans
    (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left
      (Nat.add_le_add_right
        (GodMoveCircuitRuntimeCost.circuitFor_length_le_quartic M L (T L)) 1) 4))

end GodMoveConstructedProjectionPrecision

#print axioms GodMoveConstructedProjectionPrecision.descriptorInput_eq_sampleTable
#print axioms GodMoveConstructedProjectionPrecision.descriptorInput_independent
#print axioms GodMoveConstructedProjectionPrecision.buildDescriptor_operations_eq_kernel
#print axioms GodMoveConstructedProjectionPrecision.buildDescriptor_weights_eq_kernel
#print axioms GodMoveConstructedProjectionPrecision.descriptor_kernel_correct_cost_precision
#print axioms GodMoveConstructedProjectionPrecision.buildDescriptor_duality_cost_precision
#print axioms GodMoveConstructedProjectionPrecision.machineDescriptor_kernel_precision
#print axioms GodMoveConstructedProjectionPrecision.machineDescriptor_duality_cost_precision
#print axioms GodMoveConstructedProjectionPrecision.actualSAT_descriptor_kernel_precision
#print axioms GodMoveConstructedProjectionPrecision.machineSamples_length_le_circuit
#print axioms GodMoveConstructedProjectionPrecision.machineDescriptor_precision_budget_le_circuit
#print axioms GodMoveConstructedProjectionPrecision.actualSAT_descriptor_precision_budget_le_clock
