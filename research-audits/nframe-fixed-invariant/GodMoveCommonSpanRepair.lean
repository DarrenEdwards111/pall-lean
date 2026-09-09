import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic

/-!
# A constructed common-span projection and its exact rank cost

The paper's Lemmas 27/31 need one common linear map, not only a different
coordinate permutation for each row.  For a concrete family of coordinate
rows we construct such a map: sum the coordinates and place the result in
one fixed coordinate.  Every coordinate row then maps to the same vector,
so their images really do have one common one-dimensional span.

This is a working repair of the common-span inference for this example.
Its cost is explicit: the original coordinate rows span dimension `N`,
whereas their images span dimension `1`.  A nonzero difference of two rows
lies in the kernel, so this particular map does not preserve their identity
minor when `N >= 2`.

No claim is made that this is a valid SAT separation gauge, or that another
SAT-dependent map cannot supply both collapse and the required preservation.
-/

namespace GodMoveCommonSpanRepair

open scoped BigOperators

abbrev RowSpace (N : ℕ) := Fin N → ℚ

def coordinateRow {N : ℕ} (i : Fin N) : RowSpace N := Pi.single i 1

/-- The scalar part of the common factorization. -/
def coordinateTotal (N : ℕ) : RowSpace N →ₗ[ℚ] ℚ where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

/-- A single linear map used for every row, with a fixed output coordinate. -/
def coordinateCollapse {N : ℕ} (anchor : Fin N) : RowSpace N →ₗ[ℚ] RowSpace N :=
  (coordinateTotal N).smulRight (coordinateRow anchor)

@[simp] theorem coordinateTotal_coordinateRow {N : ℕ} (i : Fin N) :
    coordinateTotal N (coordinateRow i) = 1 := by
  simp [coordinateTotal, coordinateRow]

theorem coordinateCollapse_apply {N : ℕ} (anchor : Fin N) (x : RowSpace N) :
    coordinateCollapse anchor x = coordinateTotal N x • coordinateRow anchor := rfl

@[simp] theorem coordinateCollapse_coordinateRow {N : ℕ} (anchor i : Fin N) :
    coordinateCollapse anchor (coordinateRow i) = coordinateRow anchor := by
  simp [coordinateCollapse_apply]

/-- The map is genuinely a projection, so applying it again changes nothing. -/
theorem coordinateCollapse_idempotent {N : ℕ} (anchor : Fin N) (x : RowSpace N) :
    coordinateCollapse anchor (coordinateCollapse anchor x) = coordinateCollapse anchor x := by
  rw [coordinateCollapse_apply anchor x, map_smul, coordinateCollapse_coordinateRow]

theorem coordinateRow_ne_zero {N : ℕ} (i : Fin N) : coordinateRow i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [coordinateRow] at this

/-- Every image lies in the same explicitly specified line. -/
theorem coordinateCollapse_mem_common_span {N : ℕ} (anchor : Fin N) (x : RowSpace N) :
    coordinateCollapse anchor x ∈
      Submodule.span ℚ ({coordinateRow anchor} : Set (RowSpace N)) := by
  rw [coordinateCollapse_apply]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-- The image is exactly that line, not merely contained in a proposed span. -/
theorem coordinateCollapse_range_eq_common_span {N : ℕ} (anchor : Fin N) :
    LinearMap.range (coordinateCollapse anchor) =
      Submodule.span ℚ ({coordinateRow anchor} : Set (RowSpace N)) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    exact coordinateCollapse_mem_common_span anchor x
  · apply Submodule.span_le.mpr
    intro y hy
    have hy' : y = coordinateRow anchor := by simpa using hy
    subst y
    exact ⟨coordinateRow anchor, coordinateCollapse_coordinateRow anchor anchor⟩

theorem coordinateCollapse_range_finrank {N : ℕ} (anchor : Fin N) :
    Module.finrank ℚ (LinearMap.range (coordinateCollapse anchor)) = 1 := by
  rw [coordinateCollapse_range_eq_common_span]
  exact finrank_span_singleton (coordinateRow_ne_zero anchor)

/-- The unprojected coordinate rows are an actual independent family. -/
theorem coordinateRows_linearIndependent (N : ℕ) :
    LinearIndependent ℚ (fun i : Fin N => coordinateRow i) :=
  Pi.linearIndependent_single_one (Fin N) ℚ

theorem coordinateRows_span_finrank (N : ℕ) :
    Module.finrank ℚ (Submodule.span ℚ (Set.range (fun i : Fin N => coordinateRow i))) = N := by
  simpa using finrank_span_eq_card (coordinateRows_linearIndependent N)

/-- The entire projected family, including all interface placements, spans one line. -/
theorem collapsedCoordinateRows_span_finrank {N : ℕ} (anchor : Fin N) :
    Module.finrank ℚ (Submodule.span ℚ
      (Set.range (fun i : Fin N => coordinateCollapse anchor (coordinateRow i)))) = 1 := by
  have hrange :
      Set.range (fun i : Fin N => coordinateCollapse anchor (coordinateRow i)) =
        ({coordinateRow anchor} : Set (RowSpace N)) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      simp
    · intro hy
      have hy' : y = coordinateRow anchor := by simpa using hy
      exact ⟨anchor, by simp [hy']⟩
  rw [hrange]
  exact finrank_span_singleton (coordinateRow_ne_zero anchor)

/-- Distinct coordinate rows have a nonzero difference. -/
theorem coordinateRow_sub_ne_zero {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    coordinateRow i - coordinateRow j ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [coordinateRow, hij] at hi

/-- Every linear map that identifies all coordinate rows has this same
coordinate-total factorization, with an arbitrary output vector. -/
theorem any_coordinate_identification_factors_through_total
    {V : Type*} [AddCommGroup V] [Module ℚ V] {N : ℕ}
    (T : RowSpace N →ₗ[ℚ] V) (v : V)
    (hidentify : ∀ i : Fin N, T (coordinateRow i) = v) :
    T = (coordinateTotal N).smulRight v := by
  apply (Pi.basisFun ℚ (Fin N)).ext
  intro i
  simpa [coordinateRow, coordinateTotal] using hidentify i

/-- Identifying even two distinct coordinate rows necessarily kills their
difference, for any linear map and any output module. -/
theorem any_two_coordinate_identification_kills_difference
    {V : Type*} [AddCommGroup V] [Module ℚ V] {N : ℕ}
    (T : RowSpace N →ₗ[ℚ] V) (i j : Fin N)
    (hidentify : T (coordinateRow i) = T (coordinateRow j)) :
    T (coordinateRow i - coordinateRow j) = 0 := by
  rw [map_sub, hidentify, sub_self]

/-- Therefore exact identification of two distinct coordinate rows cannot
be injective on their original coordinate-row span.  This concerns maps
that forget those positions; it does not exclude maps retaining more data. -/
theorem any_two_coordinate_identification_not_injOn_span
    {V : Type*} [AddCommGroup V] [Module ℚ V] {N : ℕ}
    (T : RowSpace N →ₗ[ℚ] V) (i j : Fin N) (hij : i ≠ j)
    (hidentify : T (coordinateRow i) = T (coordinateRow j)) :
    ¬ Set.InjOn T
      (Submodule.span ℚ (Set.range (fun k : Fin N => coordinateRow k)) :
        Set (RowSpace N)) := by
  intro hinj
  have hi : coordinateRow i ∈
      Submodule.span ℚ (Set.range (fun k : Fin N => coordinateRow k)) :=
    Submodule.subset_span ⟨i, rfl⟩
  have hj : coordinateRow j ∈
      Submodule.span ℚ (Set.range (fun k : Fin N => coordinateRow k)) :=
    Submodule.subset_span ⟨j, rfl⟩
  exact coordinateRow_sub_ne_zero i j hij (sub_eq_zero.mpr (hinj hi hj hidentify))

/-- The common-span projection kills that nonzero difference. -/
theorem coordinateRow_sub_mem_kernel {N : ℕ} (anchor i j : Fin N) :
    coordinateRow i - coordinateRow j ∈ LinearMap.ker (coordinateCollapse anchor) := by
  simp [LinearMap.mem_ker]

/-- Consequently this particular projection cannot preserve a two-row independent minor. -/
theorem coordinateCollapse_not_injective {N : ℕ} (anchor i j : Fin N) (hij : i ≠ j) :
    ¬ Function.Injective (coordinateCollapse anchor) := by
  intro hinj
  have hsame : coordinateRow i = coordinateRow j := hinj (by simp)
  exact coordinateRow_sub_ne_zero i j hij (sub_eq_zero.mpr hsame)

/-- The exact rank loss in the example, at arbitrary dimension greater than one. -/
theorem common_span_repair_strictly_lowers_row_rank {N : ℕ} (anchor : Fin N) (hN : 1 < N) :
    Module.finrank ℚ (Submodule.span ℚ
      (Set.range (fun i : Fin N => coordinateCollapse anchor (coordinateRow i)))) <
    Module.finrank ℚ (Submodule.span ℚ (Set.range (fun i : Fin N => coordinateRow i))) := by
  rw [collapsedCoordinateRows_span_finrank, coordinateRows_span_finrank]
  exact hN

/-- An alternative common span retains every placement in the original
coordinates.  Its generators are the union of the local generating families. -/
def positionRetainingSpan {V : Type*} [AddCommGroup V] [Module ℚ V]
    {placementCount localDimension : ℕ}
    (generators : Fin placementCount → Fin localDimension → V) : Submodule ℚ V :=
  Submodule.span ℚ
    (Set.range (fun ij : Fin placementCount × Fin localDimension => generators ij.1 ij.2))

/-- Every per-placement span is contained in this one common, unquotiented span. -/
theorem perPlacement_span_le_positionRetainingSpan
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    {placementCount localDimension : ℕ}
    (generators : Fin placementCount → Fin localDimension → V) (i : Fin placementCount) :
    Submodule.span ℚ (Set.range (generators i)) ≤ positionRetainingSpan generators := by
  apply Submodule.span_le.mpr
  rintro y ⟨j, rfl⟩
  exact Submodule.subset_span ⟨(i, j), rfl⟩

/-- Retaining positions has the valid bound `placementCount * localDimension`.
A polynomial bound on the number of placements is a separate obligation. -/
theorem positionRetainingSpan_finrank_le
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    {placementCount localDimension : ℕ}
    (generators : Fin placementCount → Fin localDimension → V) :
    Module.finrank ℚ (positionRetainingSpan generators) ≤ placementCount * localDimension := by
  simpa [positionRetainingSpan, Set.finrank] using
    (finrank_range_le_card (R := ℚ)
      (fun ij : Fin placementCount × Fin localDimension => generators ij.1 ij.2))

end GodMoveCommonSpanRepair

#print axioms GodMoveCommonSpanRepair.coordinateCollapse_idempotent
#print axioms GodMoveCommonSpanRepair.coordinateCollapse_range_finrank
#print axioms GodMoveCommonSpanRepair.coordinateRows_span_finrank
#print axioms GodMoveCommonSpanRepair.collapsedCoordinateRows_span_finrank
#print axioms GodMoveCommonSpanRepair.coordinateRow_sub_ne_zero
#print axioms GodMoveCommonSpanRepair.any_coordinate_identification_factors_through_total
#print axioms GodMoveCommonSpanRepair.any_two_coordinate_identification_kills_difference
#print axioms GodMoveCommonSpanRepair.any_two_coordinate_identification_not_injOn_span
#print axioms GodMoveCommonSpanRepair.coordinateRow_sub_mem_kernel
#print axioms GodMoveCommonSpanRepair.coordinateCollapse_not_injective
#print axioms GodMoveCommonSpanRepair.common_span_repair_strictly_lowers_row_rank
#print axioms GodMoveCommonSpanRepair.perPlacement_span_le_positionRetainingSpan
#print axioms GodMoveCommonSpanRepair.positionRetainingSpan_finrank_le
