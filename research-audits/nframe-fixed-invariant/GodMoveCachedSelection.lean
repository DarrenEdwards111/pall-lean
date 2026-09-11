import GodMoveCachedDiscoveryBasis
import GodMoveExhaustiveWireBasis

/-!
# Cached selection of the original independent wire columns

The scan accepts the same original labelled columns as the existing exact
row-basis scan. Each update retains materialized rows and cached norms, and
the count increase supplies its acceptance decision without recalculating
the residual. All input rows and all wire columns are stored before scanning.

The count below concerns rational arithmetic in the selection scan. Building
the Boolean wire table, indexing, comparisons, and integer work inside a
rational primitive are separate from this arithmetic-operation count.
-/

namespace GodMoveCachedSelection

open GodMoveCachedDiscoveryBasis
open GodMoveTrackedOrthogonalization (rowValue)
open GodMoveTrackedOrthogonalizationCost (Counted)
open GodMoveBooleanInterpolation GodMoveBooleanWireTable GodMoveSampledWireBasis
open PallLean.Paper93.DeepMath.PathB.NFrameBoundaryTransducer (CGate runFrom)

def eraseRows {α : Type*} {s : ℕ} (xs : List (α × Vector ℚ s)) :
    List (α × GodMoveRationalRowBasis.Vec s) :=
  xs.map (fun x => (x.1, rowValue x.2))

/-- Each insertion is evaluated once. Its stored output count decides whether
to retain the supplied labelled row. -/
def scan {α : Type*} {s : ℕ} (B : CachedBasis s) :
    List (α × Vector ℚ s) → Counted (CachedBasis s × List (α × Vector ℚ s))
  | [] => ⟨(B, []), 0⟩
  | x :: xs =>
      let next := insert B x.2
      let rest := scan next.value xs
      let selected := if next.value.count = B.count then rest.value.2 else x :: rest.value.2
      ⟨(rest.value.1, selected), next.operations + rest.operations⟩

theorem scan_value {α : Type*} {s : ℕ} (B : CachedBasis s)
    (xs : List (α × Vector ℚ s)) :
    ((scan B xs).value.1.toRowBasis, eraseRows (scan B xs).value.2) =
      GodMoveRationalRowBasis.scan B.toRowBasis (eraseRows xs) := by
  induction xs generalizing B with
  | nil => simp [scan, eraseRows, GodMoveRationalRowBasis.scan]
  | cons x xs ih =>
      have ht := ih (insert B x.2).value
      rw [insert_value] at ht
      have hcount := insert_count B x.2
      cases ha : GodMoveRationalRowBasis.accepts B.toRowBasis (rowValue x.2) <;>
        simpa [scan, eraseRows, GodMoveRationalRowBasis.scan, ha, hcount,
          Prod.ext_iff] using ht

theorem scan_operations_le {α : Type*} {s : ℕ} (B : CachedBasis s)
    (xs : List (α × Vector ℚ s)) :
    (scan B xs).operations ≤ xs.length * (8 * (s + 1) ^ 2) := by
  induction xs generalizing B with
  | nil => simp [scan]
  | cons x xs ih =>
      have hi := insert_operations_le_quadratic B x.2
      have hr := ih (insert B x.2).value
      simp only [scan, List.length_cons]
      nlinarith

def select {α : Type*} {s : ℕ} (xs : List (α × Vector ℚ s)) :
    Counted (List (α × Vector ℚ s)) :=
  let result := scan (empty s) xs
  ⟨result.value.2, result.operations⟩

theorem select_value {α : Type*} {s : ℕ} (xs : List (α × Vector ℚ s)) :
    eraseRows (select xs).value = GodMoveRationalRowBasis.selectRows (eraseRows xs) := by
  simpa [select, GodMoveRationalRowBasis.selectRows] using
    congrArg Prod.snd (scan_value (empty s) xs)

theorem select_operations_le {α : Type*} {s : ℕ} (xs : List (α × Vector ℚ s)) :
    (select xs).operations ≤ xs.length * (8 * (s + 1) ^ 2) :=
  scan_operations_le (empty s) xs

/-- Run the original circuit once for each supplied sample and store every
wire value. No enumeration of unsupplied assignments occurs. -/
def wireRows {n : ℕ} (c : List (CGate n)) (samples : List (Assignment n)) :
    Vector (Vector ℚ c.length) samples.length :=
  Vector.ofFn (fun j =>
    let vals := runFrom (samples.get j) [] c
    Vector.ofFn (fun i => bit (vals.getD i.val false)))

def columns {n : ℕ} (c : List (CGate n)) (samples : List (Assignment n)) :
    List (Fin c.length × Vector ℚ samples.length) :=
  let rows := wireRows c samples
  List.ofFn (fun i => (i, Vector.ofFn (fun j => rows[j][i])))

theorem erase_columns {n : ℕ} (c : List (CGate n)) (samples : List (Assignment n)) :
    eraseRows (columns c samples) = GodMoveExhaustiveWireBasis.columnTable c samples := by
  simp only [eraseRows, columns, GodMoveExhaustiveWireBasis.columnTable, List.map_ofFn]
  congr 1
  funext i
  apply Prod.ext
  · rfl
  funext j
  simp [wireRows, rowValue, wireColumn, wireRow]

def selectedIndices {n : ℕ} (c : List (CGate n)) (samples : List (Assignment n)) :
    Counted (List (Fin c.length)) :=
  let result := select (columns c samples)
  ⟨result.value.map Prod.fst, result.operations⟩

theorem selectedIndices_value {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) :
    (selectedIndices c samples).value =
      GodMoveExhaustiveWireBasis.selectedIndices c samples := by
  have h := congrArg (List.map Prod.fst) (select_value (columns c samples))
  rw [erase_columns] at h
  simpa [selectedIndices, eraseRows, List.map_map,
    GodMoveExhaustiveWireBasis.selectedIndices,
    GodMoveExhaustiveWireBasis.selectedColumns] using h

theorem selectedIndices_operations_le {n : ℕ} (c : List (CGate n))
    (samples : List (Assignment n)) :
    (selectedIndices c samples).operations ≤ c.length * (8 * (samples.length + 1) ^ 2) := by
  simpa [selectedIndices, columns] using select_operations_le (columns c samples)

end GodMoveCachedSelection

#print axioms GodMoveCachedSelection.scan_value
#print axioms GodMoveCachedSelection.scan_operations_le
#print axioms GodMoveCachedSelection.select_value
#print axioms GodMoveCachedSelection.erase_columns
#print axioms GodMoveCachedSelection.selectedIndices_value
#print axioms GodMoveCachedSelection.selectedIndices_operations_le
