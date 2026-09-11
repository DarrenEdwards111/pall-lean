import GodMoveCachedDiscoveryBasis
import GodMoveResidualQueries

/-!
# Materialized residual-query coefficient matrix

The builder first stores every scaled orthogonal row, then executes one cached
dot product and subtraction per matrix entry. The resulting table is exactly
the existing residual-coefficient family. Its count is rational arithmetic only;
query encoding, comparisons, allocation, and rational primitive internals are
outside this module's arithmetic model.
-/

namespace GodMoveCachedResidualMatrix

open GodMoveCachedDiscoveryBasis
open GodMoveTrackedOrthogonalization (Row rowValue)
open GodMoveTrackedOrthogonalizationCost (Counted tabulate qdiv qsub sumProducts)
open scoped BigOperators

def scaledRows {s : ℕ} (B : CachedBasis s) : Counted (Vector (Row s) B.count) :=
  tabulate fun h => tabulate fun i => qdiv B.rows[h][i] B.norms[h]

theorem scaledRows_value {s : ℕ} (B : CachedBasis s) :
    (scaledRows B).value =
      Vector.ofFn (fun h => Vector.ofFn (fun i => B.rows[h][i] / B.norms[h])) := by
  simp [scaledRows, qdiv]

theorem scaledRows_operations {s : ℕ} (B : CachedBasis s) :
    (scaledRows B).operations = B.count * s := by
  simp [scaledRows, qdiv]

def residualMatrix {s : ℕ} (B : CachedBasis s) : Counted (Vector (Row s) s) :=
  let scaled := scaledRows B
  let result := tabulate fun j => tabulate fun i =>
    let projected := sumProducts (fun h => scaled.value[h][i]) (fun h => B.rows[h][j])
    let coefficient := qsub (if j = i then 1 else 0) projected.value
    ⟨coefficient.value, projected.operations + coefficient.operations⟩
  ⟨result.value, scaled.operations + result.operations⟩

theorem residualMatrix_value {s : ℕ} (B : CachedBasis s) (j i : Fin s) :
    (residualMatrix B).value[j][i] =
      GodMoveResidualQueries.residualCoefficients B.toRowBasis j i := by
  simp [residualMatrix, scaledRows_value, qsub,
    GodMoveResidualQueries.residualCoefficients, GodMoveRationalRowBasis.residual,
    GodMoveRationalRowBasis.projected, GodMoveRationalRowBasis.component,
    B.norms_correct, CachedBasis.toRowBasis, GodMoveRationalRowBasis.dot,
    rowValue, dotProduct, Finset.sum_apply, Pi.single_apply, ite_mul, eq_comm]

theorem residualMatrix_row {s : ℕ} (B : CachedBasis s) (j : Fin s) :
    rowValue (residualMatrix B).value[j] =
      GodMoveResidualQueries.residualCoefficients B.toRowBasis j := by
  funext i
  exact residualMatrix_value B j i

theorem residualMatrix_operations {s : ℕ} (B : CachedBasis s) :
    (residualMatrix B).operations = B.count * s + s ^ 2 * (2 * B.count + 1) := by
  simp [residualMatrix, scaledRows_operations, qsub]
  ring

theorem residualMatrix_operations_le_cubic {s : ℕ} (B : CachedBasis s) :
    (residualMatrix B).operations ≤ 4 * (s + 1) ^ 3 := by
  rw [residualMatrix_operations]
  have h := count_le_width B
  have h₁ := Nat.mul_le_mul_right s h
  have h₂ := Nat.mul_le_mul_right (s ^ 2) h
  nlinarith

end GodMoveCachedResidualMatrix

#print axioms GodMoveCachedResidualMatrix.scaledRows_value
#print axioms GodMoveCachedResidualMatrix.residualMatrix_value
#print axioms GodMoveCachedResidualMatrix.residualMatrix_row
#print axioms GodMoveCachedResidualMatrix.residualMatrix_operations
#print axioms GodMoveCachedResidualMatrix.residualMatrix_operations_le_cubic
