import GodMoveMachineDiscovery
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# A stored sample matrix for the discovered wire basis

Each sample runs the original Boolean circuit once. The selected wire
values are stored in a rational matrix; no polynomial coefficients or
assignment enumeration are used in this matrix-building step. The actual
SAT-machine discovery produces equally many independent samples and basis
wires, so the resulting square matrix is nonsingular by its proved numeric
column independence. No inverse weights are assumed here.
-/

namespace GodMoveProjectionSamples

open GodMoveBooleanInterpolation GodMoveBooleanWireTable GodMoveSampledWireBasis
open GodMoveMachineDiscovery GodMoveExhaustiveWireBasis
open PallLean.Paper93.DeepMath.PathB
open NFrameBoundaryTransducer (CGate runFrom)
open ComposableMachine SeparationTarget

/-- Stored inputs to the numeric projection builder. -/
structure SampleData {n : ℕ} (c : List (CGate n)) (r : ℕ) where
  points : Vector (Assignment n) r
  indices : Vector (Fin c.length) r

/-- Run once per sample, then read and store all selected wire values. -/
def sampleTable {n r : ℕ} {c : List (CGate n)} (d : SampleData c r) :
    Vector (Vector ℚ r) r :=
  d.points.map (fun a =>
    let values := runFrom a [] c
    d.indices.map (fun j => bit (values.getD j.val false)))

def sampleMatrix {n r : ℕ} {c : List (CGate n)} (d : SampleData c r) :
    Matrix (Fin r) (Fin r) ℚ :=
  let table := sampleTable d
  fun i j => (table.get i).get j

theorem sampleMatrix_apply {n r : ℕ} {c : List (CGate n)} (d : SampleData c r)
    (i j : Fin r) :
    sampleMatrix d i j = wireRow c (d.points.get i) (d.indices.get j) := by
  simp [sampleMatrix, sampleTable, wireRow, Vector.get]

theorem sampleMatrix_eq_polynomial_eval {n r : ℕ} {c : List (CGate n)}
    (d : SampleData c r) (i j : Fin r) :
    sampleMatrix d i j = MvPolynomial.eval (booleanPoint (d.points.get i))
      (GodMoveRowSpanSeparation.wirePolynomial c (d.indices.get j)) := by
  rw [sampleMatrix_apply]
  exact wireRow_eq_normalized_eval c _ _

/-- The equality proof only aligns finite array lengths; it performs no search. -/
def ofLists {n : ℕ} (c : List (CGate n)) (samples : List (Assignment n))
    (indices : List (Fin c.length)) (hlen : indices.length = samples.length) :
    SampleData c samples.length where
  points := Vector.ofFn samples.get
  indices := Vector.ofFn (fun j => indices.get (Fin.cast hlen.symm j))

theorem ofLists_columns_linearIndependent {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (indices : List (Fin c.length))
    (hlen : indices.length = samples.length)
    (hLI : LinearIndependent ℚ
      (fun j : Fin indices.length => wireColumn c samples (indices.get j))) :
    LinearIndependent ℚ (sampleMatrix (ofLists c samples indices hlen)).col := by
  have hinj : Function.Injective (Fin.cast hlen.symm) := by
    exact (finCongr hlen.symm).injective
  have h := hLI.comp (Fin.cast hlen.symm) hinj
  convert h using 1
  funext j i
  simp [Matrix.col, sampleMatrix_apply, ofLists, wireColumn, Vector.get]

theorem ofLists_rows_linearIndependent {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (indices : List (Fin c.length))
    (hlen : indices.length = samples.length)
    (hLI : LinearIndependent ℚ
      (fun j : Fin indices.length => wireColumn c samples (indices.get j))) :
    LinearIndependent ℚ (sampleMatrix (ofLists c samples indices hlen)) := by
  apply Matrix.linearIndependent_rows_iff_isUnit.mpr
  exact Matrix.linearIndependent_cols_iff_isUnit.mp
    (ofLists_columns_linearIndependent c samples indices hlen hLI)

theorem ofLists_basis_range {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (indices : List (Fin c.length))
    (hlen : indices.length = samples.length) :
    Set.range (fun j => GodMoveRowSpanSeparation.wirePolynomial c
      ((ofLists c samples indices hlen).indices.get j)) =
      Set.range (chosenWire c indices) := by
  ext p
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨Fin.cast hlen.symm j, by simp [ofLists, chosenWire, Vector.get]⟩
  · rintro ⟨j, rfl⟩
    exact ⟨Fin.cast hlen j, by simp [ofLists, chosenWire, Vector.get]⟩

theorem machine_sample_basis_length (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n)) :
    (selectedIndices c (machineSamples M T c)).length =
      (machineSamples M T c).length := by
  rw [← machineBasisIndices, machineBasis_length_eq_wireRank M T hD,
    machineSamples_length_eq_wireRank M T hD]

/-- Pass the discovered lists to the stored sample-data builder. The
correctness proof is used only for the equality of array lengths; this
declaration does not assert a whole-wrapper execution-time bound. -/
def machineSampleData (M : Machine) (T : ℕ → ℕ) (hD : Decides M SATLang T)
    {n : ℕ} (c : List (CGate n)) : SampleData c (machineSamples M T c).length :=
  let samples := machineSamples M T c
  let indices := selectedIndices c samples
  ofLists c samples indices (machine_sample_basis_length M T hD c)

theorem machineSampleData_rows_linearIndependent (M : Machine) (T : ℕ → ℕ)
    (hD : Decides M SATLang T) {n : ℕ} (c : List (CGate n)) :
    LinearIndependent ℚ (sampleMatrix (machineSampleData M T hD c)) :=
  ofLists_rows_linearIndependent c _ _ (machine_sample_basis_length M T hD c)
    (selectedColumns_linearIndependent c _)

end GodMoveProjectionSamples

#print axioms GodMoveProjectionSamples.sampleMatrix_apply
#print axioms GodMoveProjectionSamples.sampleMatrix_eq_polynomial_eval
#print axioms GodMoveProjectionSamples.ofLists_columns_linearIndependent
#print axioms GodMoveProjectionSamples.ofLists_rows_linearIndependent
#print axioms GodMoveProjectionSamples.ofLists_basis_range
#print axioms GodMoveProjectionSamples.machine_sample_basis_length
#print axioms GodMoveProjectionSamples.machineSampleData_rows_linearIndependent
