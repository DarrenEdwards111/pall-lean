import GodMoveExhaustiveDiscovery
import GodMoveSampledWireBasis

/-!
# Executable discovery of an exact computed-wire basis

After discovering separating samples, transpose their numeric wire table and
apply the same rational row selector to its columns. The selected labels are
actual wire indices. Numeric spanning and independence lift to the normalized
polynomials, so the returned wires form an exact basis of `wireSpace`.

This constructs the sample and basis lists without semantic oracles. The first
stage still scans all Boolean assignments. No efficient general discovery,
rational inverse-weight construction, or SAT lower bound is asserted here.
-/

namespace GodMoveExhaustiveWireBasis

open GodMoveBooleanInterpolation GodMoveComputedWireRank GodMoveExhaustiveDiscovery
open GodMoveSampledWireBasis GodMoveRationalRowBasis
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer (CGate)

def columnTable {n : ℕ} (c : List (CGate n)) (samples : List (Assignment n)) :
    List (Fin c.length × (Fin samples.length → ℚ)) :=
  List.ofFn (fun i => (i, wireColumn c samples i))

theorem columnTable_contains {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (i : Fin c.length) :
    (i, wireColumn c samples i) ∈ columnTable c samples := by
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

def selectedColumns {n : ℕ} (c : List (CGate n)) (samples : List (Assignment n)) :=
  selectRows (columnTable c samples)

def selectedIndices {n : ℕ} (c : List (CGate n)) (samples : List (Assignment n)) :
    List (Fin c.length) := (selectedColumns c samples).map Prod.fst

theorem selectedColumns_consistent {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (x : Fin c.length × (Fin samples.length → ℚ))
    (hx : x ∈ selectedColumns c samples) : x.2 = wireColumn c samples x.1 := by
  have hx' := selectRows_subset (columnTable c samples) x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx'
  rfl

theorem selectedColumnSpace_eq {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) :
    chosenColumnSpace c samples (selectedIndices c samples) =
      rowListSpan (selectedColumns c samples) := by
  unfold chosenColumnSpace rowListSpan
  congr 1
  ext v
  constructor
  · rintro ⟨j, rfl⟩
    have hj : (selectedIndices c samples).get j ∈ selectedIndices c samples :=
      List.getElem_mem j.isLt
    obtain ⟨x, hx, heq⟩ := List.mem_map.mp hj
    exact ⟨x, hx, (selectedColumns_consistent c samples x hx).trans
      (congrArg (wireColumn c samples) heq)⟩
  · rintro ⟨x, hx, rfl⟩
    have hi : x.1 ∈ selectedIndices c samples := List.mem_map.mpr ⟨x, hx, rfl⟩
    obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hi
    refine ⟨⟨j, hj⟩, ?_⟩
    change wireColumn c samples ((selectedIndices c samples)[j]'hj) = x.2
    rw [heq, selectedColumns_consistent c samples x hx]

theorem every_column_mem {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) (i : Fin c.length) :
    wireColumn c samples i ∈ chosenColumnSpace c samples (selectedIndices c samples) := by
  rw [selectedColumnSpace_eq, selectedColumns, selectRows_span]
  exact Submodule.subset_span ⟨(i, wireColumn c samples i), columnTable_contains c samples i,
    rfl⟩

theorem selectedColumns_linearIndependent {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) :
    LinearIndependent ℚ (fun j : Fin (selectedIndices c samples).length =>
      wireColumn c samples ((selectedIndices c samples).get j)) := by
  unfold selectedIndices
  simp only [List.get_eq_getElem, List.getElem_map]
  have heq : (fun j : Fin (selectedColumns c samples).length =>
      wireColumn c samples ((selectedColumns c samples).get j).1) =
      (fun j : Fin (selectedColumns c samples).length =>
        ((selectedColumns c samples).get j).2) := by
    funext j
    exact (selectedColumns_consistent c samples _ (List.getElem_mem j.isLt)).symm
  have hlin := selectRows_linearIndependent (columnTable c samples)
  change LinearIndependent ℚ (fun j : Fin (selectedColumns c samples).length =>
    ((selectedColumns c samples).get j).2) at hlin
  rw [← heq] at hlin
  let e : Fin ((selectedColumns c samples).map Prod.fst).length →
      Fin (selectedColumns c samples).length :=
    fun j => ⟨j.val, by simpa only [List.length_map] using j.isLt⟩
  apply hlin.comp e
  intro j k h
  apply Fin.ext
  exact congrArg (fun z : Fin (selectedColumns c samples).length => z.val) h

def discoverBasisIndices {n : ℕ} (c : List (CGate n)) : List (Fin c.length) :=
  selectedIndices c (discoverSamples c)

/-- The executable selected wires span the entire actual computed-wire space. -/
theorem discoverBasis_spans {n : ℕ} (c : List (CGate n)) :
    chosenWireSpace c (discoverBasisIndices c) = wireSpace c :=
  chosenWireSpace_eq_of_columns c (discoverSamples c) (discoverBasisIndices c)
    (discoverSamples_separates c) (every_column_mem c (discoverSamples c))

/-- The selected objects are a basis, rather than a redundant spanning list. -/
theorem discoverBasis_linearIndependent {n : ℕ} (c : List (CGate n)) :
    LinearIndependent ℚ (chosenWire c (discoverBasisIndices c)) :=
  chosenWire_linearIndependent c (discoverSamples c) (discoverBasisIndices c)
    (selectedColumns_linearIndependent c (discoverSamples c))

theorem discoverBasis_length_eq_wireRank {n : ℕ} (c : List (CGate n)) :
    (discoverBasisIndices c).length = wireRank c :=
  chosenWire_length_eq_rank c (discoverBasisIndices c)
    (discoverBasis_spans c) (discoverBasis_linearIndependent c)

theorem discoverBasis_length_le_samples {n : ℕ} (c : List (CGate n)) :
    (discoverBasisIndices c).length ≤ (discoverSamples c).length := by
  simpa only [discoverBasisIndices, selectedIndices, List.length_map] using
    selectRows_length_le (columnTable c (discoverSamples c))

theorem discoverBasis_length_le_gates {n : ℕ} (c : List (CGate n)) :
    (discoverBasisIndices c).length ≤ c.length :=
  (discoverBasis_length_le_samples c).trans (discoverSamples_length_le c)

/-- An executable exact rank calculation. Exhaustive discovery remains inside
this definition; the equality theorem gives no polynomial runtime bound. -/
def discoveredRank {n : ℕ} (c : List (CGate n)) : ℕ := (discoverBasisIndices c).length

theorem discoveredRank_eq_wireRank {n : ℕ} (c : List (CGate n)) :
    discoveredRank c = wireRank c := discoverBasis_length_eq_wireRank c

namespace Examples

/-- info: true -/
#guard_msgs in
#eval decide ((discoverBasisIndices GodMoveExhaustiveDiscovery.Examples.duplicateCircuit).map
  Fin.val = [0])

/-- info: true -/
#guard_msgs in
#eval decide ((discoverBasisIndices GodMoveExhaustiveDiscovery.Examples.andCircuit).map
  Fin.val = [0, 1, 2])

/-- info: true -/
#guard_msgs in
#eval decide (discoveredRank ([.cst false] : List (CGate 0)) = 0)

/-- info: true -/
#guard_msgs in
#eval decide (discoveredRank ([.cst true] : List (CGate 0)) = 1)

end Examples

end GodMoveExhaustiveWireBasis

#print axioms GodMoveExhaustiveWireBasis.every_column_mem
#print axioms GodMoveExhaustiveWireBasis.selectedColumns_linearIndependent
#print axioms GodMoveExhaustiveWireBasis.discoverBasis_spans
#print axioms GodMoveExhaustiveWireBasis.discoverBasis_linearIndependent
#print axioms GodMoveExhaustiveWireBasis.discoveredRank_eq_wireRank
#print axioms GodMoveExhaustiveWireBasis.discoverBasis_length_le_samples
#print axioms GodMoveExhaustiveWireBasis.discoverBasis_length_le_gates
