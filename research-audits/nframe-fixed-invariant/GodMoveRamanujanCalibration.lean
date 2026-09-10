import PallLean.Paper93.DeepMath.PathB.ComputationalDepthExpanderTseitinInstance

/-!
# A concrete Ramanujan spectral calibration

The matrix below is the actual adjacency matrix of the existing six-edge
Tseitin graph `K4`.  The endpoint relation, degree three, and action on every
mean-zero vector are proved, rather than supplied as spectral data.  Its
nonconstant adjacency eigenvalue is exactly `-1`, so it satisfies the squared
Ramanujan estimate `‖A x‖² ≤ 4 (3 - 1) ‖x‖²` on the mean-zero subspace.

This is one graph on four vertices.  It does not construct an asymptotic
fixed-degree family, establish a SAT runtime bound, or assert that graph
mixing preserves polynomial projected-partial-derivative rank.
-/

namespace GodMoveRamanujanCalibration

open Finset
open PallLean.Paper93.DeepMath.PathB
open scoped BigOperators

/-- Adjacency of the simple complete graph on four vertices. -/
def adjacency : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => if i = j then 0 else 1

/-- The matrix's off-diagonal edges are exactly the production graph's edges. -/
theorem endpoints_iff (i j : Fin 4) :
    (∃ e : Fin 6, K4.endpoints e = {i, j}) ↔ i ≠ j := by
  fin_cases i <;> fin_cases j <;> decide

/-- An adjacency entry is determined by the actual six endpoint sets. -/
theorem adjacency_eq_endpoint_indicator (i j : Fin 4) :
    adjacency i j = if ∃ e : Fin 6, K4.endpoints e = {i, j} then 1 else 0 := by
  simp only [endpoints_iff]
  by_cases h : i = j <;> simp [adjacency, h]

theorem adjacency_symmetric : adjacency.IsSymm := by
  ext i j
  simp only [adjacency, Matrix.transpose_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- Every vertex has degree three in this same endpoint graph. -/
theorem endpoint_degree_three (i : Fin 4) :
    (univ.filter fun e : Fin 6 => i ∈ K4.endpoints e).card = 3 := by
  fin_cases i <;> decide

/-- On every vector, adjacency is the all-ones matrix minus the identity. -/
theorem adjacency_mulVec (x : Fin 4 → ℝ) :
    adjacency.mulVec x = fun i => (∑ j, x j) - x i := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, adjacency, Fin.sum_univ_succ] <;> ring

theorem adjacency_row_sum (i : Fin 4) :
    ∑ j, adjacency i j = 3 := by
  have h := congrFun (adjacency_mulVec (fun _ => 1)) i
  norm_num [Matrix.mulVec, dotProduct] at h
  exact h

/-- This computes the actual nonconstant spectrum, without a scalar gap field. -/
theorem adjacency_mulVec_of_sum_zero (x : Fin 4 → ℝ)
    (hx : ∑ i, x i = 0) : adjacency.mulVec x = -x := by
  rw [adjacency_mulVec]
  ext i
  simp [hx]

/-- Euclidean squared norm, written directly as a finite sum of squares. -/
def normSquared (x : Fin 4 → ℝ) : ℝ := ∑ i, (x i) ^ 2

theorem normSquared_nonneg (x : Fin 4 → ℝ) : 0 ≤ normSquared x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem adjacency_normSquared_of_sum_zero (x : Fin 4 → ℝ)
    (hx : ∑ i, x i = 0) : normSquared (adjacency.mulVec x) = normSquared x := by
  rw [adjacency_mulVec_of_sum_zero x hx]
  simp [normSquared]

/-- A concrete squared Ramanujan operator bound for the actual K4 adjacency. -/
theorem K4_ramanujan_squared (x : Fin 4 → ℝ)
    (hx : ∑ i, x i = 0) :
    normSquared (adjacency.mulVec x) ≤ 4 * ((3 : ℝ) - 1) * normSquared x := by
  rw [adjacency_normSquared_of_sum_zero x hx]
  have hn := normSquared_nonneg x
  nlinarith

/-- Spectral and combinatorial expansion are certified for the same graph. -/
theorem K4_spectral_and_expansion :
    K4.HasExpansion 2 ∧
      ∀ x : Fin 4 → ℝ, (∑ i, x i) = 0 →
        normSquared (adjacency.mulVec x) ≤ 8 * normSquared x := by
  refine ⟨K4_hasExpansion, ?_⟩
  intro x hx
  convert K4_ramanujan_squared x hx using 1
  norm_num

#print axioms endpoints_iff
#print axioms adjacency_eq_endpoint_indicator
#print axioms adjacency_symmetric
#print axioms endpoint_degree_three
#print axioms adjacency_row_sum
#print axioms adjacency_mulVec_of_sum_zero
#print axioms adjacency_normSquared_of_sum_zero
#print axioms K4_ramanujan_squared
#print axioms K4_spectral_and_expansion

end GodMoveRamanujanCalibration
