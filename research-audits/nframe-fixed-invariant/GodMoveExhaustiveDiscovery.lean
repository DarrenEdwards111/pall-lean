import GodMoveBooleanWireTable
import GodMoveRationalRowBasis
import GodMoveRowSpanSeparation
import GodMoveSampledSAT

/-!
# Executable exhaustive discovery of separating wire samples

The input rows come from executing the Boolean circuit on all `2^n`
assignments. Exact rational row selection retains at most one assignment per
wire and supplies a numeric span proof. That proof implies separation of the
actual normalized computed-wire space, so the resulting SAT test no longer
takes semantic separation as a hypothesis.

The returned sample list is small; discovering it here is exhaustive.
No polynomial runtime or rational bit-complexity bound is asserted.
-/

namespace GodMoveExhaustiveDiscovery

open GodMoveBooleanInterpolation GodMoveBooleanWireTable
open GodMoveSamplingBarrier GodMoveSampledSAT
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer (CGate)
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction (Formula Satisfiable)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec (encodeFormula')

/-- Labels retain their original circuit-value rows. -/
theorem rowSpan_labels_eq {n : ℕ} (c : List (CGate n))
    (rows : List (Assignment n × (Fin c.length → ℚ)))
    (hrows : ∀ x ∈ rows, x.2 = wireRow c x.1) :
    GodMoveRowSpanSeparation.rowSpan c (rows.map Prod.fst) =
      Submodule.span ℚ (↑(rows.map Prod.snd).toFinset : Set (Fin c.length → ℚ)) := by
  unfold GodMoveRowSpanSeparation.rowSpan
  congr 2
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro x hx
  exact (hrows x hx).symm

def discoverRows {n : ℕ} (c : List (CGate n)) :
    List (Assignment n × (Fin c.length → ℚ)) :=
  GodMoveRationalRowBasis.selectRows (wireTable c)

/-- The actual assignments retained by exact row-space scanning. -/
def discoverSamples {n : ℕ} (c : List (CGate n)) : List (Assignment n) :=
  (discoverRows c).map Prod.fst

theorem discoverRows_consistent {n : ℕ} (c : List (CGate n))
    (x : Assignment n × (Fin c.length → ℚ)) (hx : x ∈ discoverRows c) :
    x.2 = wireRow c x.1 := by
  have hx' := GodMoveRationalRowBasis.selectRows_subset (wireTable c) x hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx'
  rfl

theorem discoverSamples_rowSpan {n : ℕ} (c : List (CGate n)) :
    GodMoveRowSpanSeparation.rowSpan c (discoverSamples c) =
      GodMoveRationalRowBasis.rowListSpan (wireTable c) := by
  rw [discoverSamples, rowSpan_labels_eq c (discoverRows c) (discoverRows_consistent c)]
  have heq :
      Submodule.span ℚ (↑((discoverRows c).map Prod.snd).toFinset :
        Set (Fin c.length → ℚ)) = GodMoveRationalRowBasis.rowListSpan (discoverRows c) := by
    unfold GodMoveRationalRowBasis.rowListSpan
    congr 1
    ext v
    simp
  rw [heq]
  exact GodMoveRationalRowBasis.selectRows_span (wireTable c)

/-- Global polynomial separation is derived from the actual finite scan. -/
theorem discoverSamples_separates {n : ℕ} (c : List (CGate n)) :
    SeparatesWires c (discoverSamples c) := by
  apply GodMoveRowSpanSeparation.separates_of_all_rows_mem
  intro a
  rw [discoverSamples_rowSpan]
  apply Submodule.subset_span
  exact ⟨(a, wireRow c a), wireTable_contains c a, rfl⟩

theorem discoverSamples_length_le {n : ℕ} (c : List (CGate n)) :
    (discoverSamples c).length ≤ c.length := by
  simpa only [discoverSamples, List.length_map] using
    GodMoveRationalRowBasis.selectRows_length_le (wireTable c)

/-- The search input is exponential even though its selected output is small. -/
theorem discovery_table_length {n : ℕ} (c : List (CGate n)) :
    (wireTable c).length = 2 ^ n := wireTable_length c

def exhaustiveSelector : SampleSelector := fun _ c => discoverSamples c

def exhaustiveSAT := sampledSAT exhaustiveSelector

theorem exhaustiveSAT_correct
    (φ : Formula) :
    exhaustiveSAT φ = true ↔ Satisfiable φ :=
  sampledSAT_correct exhaustiveSelector (fun _ c => discoverSamples_separates c) φ

/-- This is an executable decider using exhaustive discovery, with no sample
selector or separation assumption supplied by its caller. -/
def exhaustiveSATWord := sampledSATWord exhaustiveSelector

theorem exhaustiveSATWord_eq_SATLang (x : List Bool) :
    exhaustiveSATWord x = PallLean.Paper93.DeepMath.PathB.SeparationTarget.SATLang x :=
  sampledSATWord_eq_SATLang exhaustiveSelector (fun _ c => discoverSamples_separates c) x

theorem selectedSamples_length_le_encoded
    (φ : Formula) :
    (selectedSamples exhaustiveSelector φ).length ≤
      (encodeFormula' φ).length :=
  (discoverSamples_length_le (sampledCircuit φ)).trans (sampledCircuit_length_le φ)

/-- A storage bound for the retained Boolean assignments, after the exhaustive
search has finished. This does not bound the search table or its computation. -/
theorem storedSamples_length_le_encoded
    (φ : Formula) :
    (storedSamples exhaustiveSelector φ).length ≤
      3 * (encodeFormula' φ).length *
        ((encodeFormula' φ).length + 1) ^ 2 := by
  rw [storedSamples_length]
  calc
    _ ≤ (encodeFormula' φ).length *
        (3 * ((encodeFormula' φ).length + 1) ^ 2) :=
      Nat.mul_le_mul (selectedSamples_length_le_encoded φ) (witnessArity_le_quadratic φ)
    _ = _ := by ring

namespace Examples

def andCircuit : List (CGate 2) := [.var 0, .var 1, .bin (· && ·) 0 1]

def duplicateCircuit : List (CGate 1) := [.var 0, .var 0]

theorem empty_samples :
    ((discoverSamples ([] : List (CGate 0))).map List.ofFn) = [] := by decide

/-- info: true -/
#guard_msgs in
#eval decide ((discoverSamples andCircuit).map List.ofFn =
  [[false, true], [true, false], [true, true]])

/-- info: true -/
#guard_msgs in
#eval decide ((discoverSamples duplicateCircuit).map List.ofFn = [[true]])

end Examples

end GodMoveExhaustiveDiscovery

#print axioms GodMoveExhaustiveDiscovery.discoverSamples_rowSpan
#print axioms GodMoveExhaustiveDiscovery.discoverSamples_separates
#print axioms GodMoveExhaustiveDiscovery.discoverSamples_length_le
#print axioms GodMoveExhaustiveDiscovery.exhaustiveSAT_correct
#print axioms GodMoveExhaustiveDiscovery.exhaustiveSATWord_eq_SATLang
#print axioms GodMoveExhaustiveDiscovery.selectedSamples_length_le_encoded
#print axioms GodMoveExhaustiveDiscovery.storedSamples_length_le_encoded
#print axioms GodMoveExhaustiveDiscovery.Examples.empty_samples
