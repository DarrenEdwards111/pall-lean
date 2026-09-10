import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# A positive external matrix and its one-dimensional positive-cone map

The external matrix has rows on the rational moment curve. Its ordered maximal
minors are strictly positive, not an assumed predicate. Its row-vector map is
the affine-cone version of the k = 1 amplituhedron map: a nonzero nonnegative
row maps to a vector with positive first coordinate. This module does not
construct higher Grassmannian cells or assert SPDP monotonicity for this map.

Any r distinct rows remain independent when r ≤ q. Conversely, a boundary with
q coordinates cannot linearly encode and decode an r-dimensional identity
minor for r > q. Thus positive geometry preserves a selected minor only with
the stated dimension cost; it supplies no unproved compression theorem.
-/

namespace GodMovePositiveBoundaryMap

open Matrix

/-- Positive, distinct rational nodes attached to finite labels. -/
def node {N : ℕ} (i : Fin N) : ℚ := (i.val : ℚ) + 1

theorem node_strictMono (N : ℕ) : StrictMono (@node N) := by
  intro i j hij
  dsimp [node]
  have hv : i.val < j.val := hij
  have hcast : (i.val : ℚ) < (j.val : ℚ) := by exact_mod_cast hv
  linarith

theorem node_injective (N : ℕ) : Function.Injective (@node N) :=
  (node_strictMono N).injective

/-- Rectangular moment-curve external matrix, with q boundary coordinates. -/
def boundaryMatrix (N q : ℕ) : Matrix (Fin N) (Fin q) ℚ :=
  fun i j => node i ^ j.val

/-- Every ordered maximal minor is a positive Vandermonde determinant. -/
theorem ordered_maximal_minor_pos {N q : ℕ} (f : Fin q → Fin N)
    (hf : StrictMono f) :
    0 < ((boundaryMatrix N q).submatrix f id).det := by
  change 0 < (Matrix.vandermonde (fun i => node (f i))).det
  rw [Matrix.det_vandermonde]
  apply Finset.prod_pos
  intro i hi
  apply Finset.prod_pos
  intro j hj
  exact sub_pos.mpr (node_strictMono N (hf (Finset.mem_Ioi.mp hj)))

/-- An arbitrary selection of distinct rows has nonzero maximal minor;
the determinant's sign depends on their order. -/
theorem maximal_minor_ne_zero {N q : ℕ} (f : Fin q → Fin N)
    (hf : Function.Injective f) :
    ((boundaryMatrix N q).submatrix f id).det ≠ 0 := by
  change (Matrix.vandermonde (fun i => node (f i))).det ≠ 0
  exact Matrix.det_vandermonde_ne_zero_iff.mpr ((node_injective N).comp hf)

/-- The first r powers give a nonsingular minor of any r distinct rows. -/
theorem first_columns_minor_ne_zero {N q r : ℕ} (f : Fin r → Fin N)
    (hf : Function.Injective f) (hrq : r ≤ q) :
    ((boundaryMatrix N q).submatrix f (Fin.castLE hrq)).det ≠ 0 := by
  change (Matrix.vandermonde (fun i => node (f i))).det ≠ 0
  exact Matrix.det_vandermonde_ne_zero_iff.mpr ((node_injective N).comp hf)

/-- Restrict boundary vectors to their first r coordinates. -/
def firstCoordinates {q r : ℕ} (hrq : r ≤ q) :
    (Fin q → ℚ) →ₗ[ℚ] (Fin r → ℚ) where
  toFun x i := x (Fin.castLE hrq i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Distinct external rows preserve any selected r-dimensional row space,
provided at least r boundary coordinates are retained. -/
theorem selected_rows_linearIndependent {N q r : ℕ} (f : Fin r → Fin N)
    (hf : Function.Injective f) (hrq : r ≤ q) :
    LinearIndependent ℚ (fun i => boundaryMatrix N q (f i)) := by
  apply LinearIndependent.of_comp (firstCoordinates hrq)
  change LinearIndependent ℚ
    (((boundaryMatrix N q).submatrix f (Fin.castLE hrq)).row)
  apply Matrix.linearIndependent_rows_iff_isUnit.mpr
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  exact isUnit_iff_ne_zero.mpr (first_columns_minor_ne_zero f hf hrq)

/-- Matrix selecting the first r coordinates of a q-coordinate boundary. -/
def firstCoordinateSelector {q r : ℕ} (hrq : r ≤ q) :
    Matrix (Fin q) (Fin r) ℚ :=
  fun i j => if i = Fin.castLE hrq j then 1 else 0

theorem mul_firstCoordinateSelector {r q : ℕ} (hrq : r ≤ q)
    (E : Matrix (Fin r) (Fin q) ℚ) :
    E * firstCoordinateSelector hrq = E.submatrix id (Fin.castLE hrq) := by
  ext i j
  simp [Matrix.mul_apply, firstCoordinateSelector]

/-- Explicit decoder: select the first r coordinates and invert their
nonsingular Vandermonde minor. No extension to an ambient basis is used. -/
noncomputable def selectedDecoder {N q r : ℕ} (f : Fin r → Fin N)
    (hrq : r ≤ q) : Matrix (Fin q) (Fin r) ℚ :=
  firstCoordinateSelector hrq *
    ((boundaryMatrix N q).submatrix f (Fin.castLE hrq))⁻¹

/-- The selected moment-curve encoder followed by its explicit decoder
reconstructs every coordinate of the retained r-dimensional family. -/
theorem selected_encoder_mul_decoder {N q r : ℕ} (f : Fin r → Fin N)
    (hf : Function.Injective f) (hrq : r ≤ q) :
    (boundaryMatrix N q).submatrix f id * selectedDecoder f hrq = 1 := by
  rw [selectedDecoder, ← Matrix.mul_assoc, mul_firstCoordinateSelector]
  change ((boundaryMatrix N q).submatrix f (Fin.castLE hrq)) *
    ((boundaryMatrix N q).submatrix f (Fin.castLE hrq))⁻¹ = 1
  exact Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (first_columns_minor_ne_zero f hf hrq))

/-- Decoding recovers arbitrary signed row coordinates, not just cone data. -/
theorem selected_decode_encode {N q r : ℕ} (f : Fin r → Fin N)
    (hf : Function.Injective f) (hrq : r ≤ q) (c : Fin r → ℚ) :
    (c ᵥ* (boundaryMatrix N q).submatrix f id) ᵥ* selectedDecoder f hrq = c := by
  rw [Matrix.vecMul_vecMul, selected_encoder_mul_decoder f hf hrq, Matrix.vecMul_one]

/-- Decode and re-encode the boundary. This square matrix, unlike the
rectangular encoder itself, is an actual idempotent when the rows are distinct. -/
noncomputable def selectedBoundaryProjection {N q r : ℕ} (f : Fin r → Fin N)
    (hrq : r ≤ q) : Matrix (Fin q) (Fin q) ℚ :=
  selectedDecoder f hrq * (boundaryMatrix N q).submatrix f id

theorem selectedBoundaryProjection_idempotent {N q r : ℕ} (f : Fin r → Fin N)
    (hf : Function.Injective f) (hrq : r ≤ q) :
    selectedBoundaryProjection f hrq * selectedBoundaryProjection f hrq =
      selectedBoundaryProjection f hrq := by
  unfold selectedBoundaryProjection
  calc
    _ = selectedDecoder f hrq *
        ((boundaryMatrix N q).submatrix f id * selectedDecoder f hrq) *
          (boundaryMatrix N q).submatrix f id := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [selected_encoder_mul_decoder f hf hrq, Matrix.mul_one]

/-- The square boundary projection fixes every retained external row. -/
theorem selected_encoder_mul_projection {N q r : ℕ} (f : Fin r → Fin N)
    (hf : Function.Injective f) (hrq : r ≤ q) :
    (boundaryMatrix N q).submatrix f id * selectedBoundaryProjection f hrq =
      (boundaryMatrix N q).submatrix f id := by
  rw [selectedBoundaryProjection, ← Matrix.mul_assoc,
    selected_encoder_mul_decoder f hf hrq, Matrix.one_mul]

/-- The actual projection retains exactly r dimensions; it does not reduce
the dimension of the independent family being reconstructed. -/
theorem selectedBoundaryProjection_rank {N q r : ℕ} (f : Fin r → Fin N)
    (hf : Function.Injective f) (hrq : r ≤ q) :
    (selectedBoundaryProjection f hrq).rank = r := by
  apply Nat.le_antisymm
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width (selectedDecoder f hrq))
  · have hr : r ≤ ((boundaryMatrix N q).submatrix f id).rank := by
      have h := Matrix.rank_mul_le_left ((boundaryMatrix N q).submatrix f id)
        (selectedDecoder f hrq)
      simpa only [selected_encoder_mul_decoder f hf hrq, Matrix.rank_one,
        Fintype.card_fin] using h
    have h := Matrix.rank_mul_le_right ((boundaryMatrix N q).submatrix f id)
      (selectedBoundaryProjection f hrq)
    rw [selected_encoder_mul_projection f hf hrq] at h
    exact hr.trans h

/-- Rational positive-cone moment map c ↦ c Z. -/
noncomputable def positiveBoundaryMap (N q : ℕ) :
    (Fin N → ℚ) →ₗ[ℚ] (Fin q → ℚ) :=
  (boundaryMatrix N q).vecMulLinear

theorem positiveBoundaryMap_first {N q : ℕ} (hq : 0 < q) (c : Fin N → ℚ) :
    positiveBoundaryMap N q c ⟨0, hq⟩ = ∑ i, c i := by
  simp [positiveBoundaryMap, Matrix.vecMul, dotProduct, boundaryMatrix]

/-- Nonzero nonnegative cone data have positive first image coordinate. -/
theorem positiveBoundaryMap_first_pos {N q : ℕ} (hq : 0 < q)
    (c : Fin N → ℚ) (hc : ∀ i, 0 ≤ c i) (hne : c ≠ 0) :
    0 < positiveBoundaryMap N q c ⟨0, hq⟩ := by
  rw [positiveBoundaryMap_first hq c]
  apply Finset.sum_pos' (fun i _ => hc i)
  have hex : ∃ i, c i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, Finset.mem_univ i, lt_of_le_of_ne (hc i) (Ne.symm hi)⟩

theorem positiveBoundaryMap_ne_zero {N q : ℕ} (hq : 0 < q)
    (c : Fin N → ℚ) (hc : ∀ i, 0 ≤ c i) (hne : c ≠ 0) :
    positiveBoundaryMap N q c ≠ 0 := by
  intro h
  have := positiveBoundaryMap_first_pos hq c hc hne
  simp [h] at this

/-- The linear boundary has at most q dimensions. -/
theorem boundaryMatrix_rank_le (N q : ℕ) :
    (boundaryMatrix N q).rank ≤ q := Matrix.rank_le_width _

/-- Any linear encoder and decoder preserving an identity minor must retain
at least its dimension, regardless of positivity or graph structure. -/
theorem identity_minor_requires_boundary_dimension {r q : ℕ}
    (E : Matrix (Fin r) (Fin q) ℚ) (D : Matrix (Fin q) (Fin r) ℚ)
    (hED : E * D = 1) : r ≤ q := by
  have h := (Matrix.rank_mul_le_left E D).trans (Matrix.rank_le_width E)
  simpa [hED] using h

theorem no_identity_minor_through_smaller_boundary {r q : ℕ} (hqr : q < r)
    (E : Matrix (Fin r) (Fin q) ℚ) (D : Matrix (Fin q) (Fin r) ℚ) :
    E * D ≠ 1 := by
  intro h
  exact (Nat.not_le_of_lt hqr) (identity_minor_requires_boundary_dimension E D h)

end GodMovePositiveBoundaryMap

#print axioms GodMovePositiveBoundaryMap.ordered_maximal_minor_pos
#print axioms GodMovePositiveBoundaryMap.maximal_minor_ne_zero
#print axioms GodMovePositiveBoundaryMap.first_columns_minor_ne_zero
#print axioms GodMovePositiveBoundaryMap.selected_rows_linearIndependent
#print axioms GodMovePositiveBoundaryMap.selected_encoder_mul_decoder
#print axioms GodMovePositiveBoundaryMap.selected_decode_encode
#print axioms GodMovePositiveBoundaryMap.selectedBoundaryProjection_idempotent
#print axioms GodMovePositiveBoundaryMap.selected_encoder_mul_projection
#print axioms GodMovePositiveBoundaryMap.selectedBoundaryProjection_rank
#print axioms GodMovePositiveBoundaryMap.positiveBoundaryMap_first_pos
#print axioms GodMovePositiveBoundaryMap.positiveBoundaryMap_ne_zero
#print axioms GodMovePositiveBoundaryMap.boundaryMatrix_rank_le
#print axioms GodMovePositiveBoundaryMap.identity_minor_requires_boundary_dimension
#print axioms GodMovePositiveBoundaryMap.no_identity_minor_through_smaller_boundary
