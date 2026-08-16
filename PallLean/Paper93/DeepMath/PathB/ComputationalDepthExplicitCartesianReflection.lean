import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCartesianHankelWitness
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthGodelTowerVerify

/-!
# Explicit Cartesian reflection and its succinctness obstruction

The literal Kronecker-square reflection is constructible and automatically
has the Cartesian witness required by the rank-amplification theorem.  It also
squares the explicit row set, column set, and matrix cell count.  Thus this
construction proves product capture only by materialising the product; it is
not the missing uniformly succinct solver-relative Gödel construction.

The existing Gödel verification step is additive (`n ↦ n+1`).  No theorem in
the current development turns that additive logical extension into the
independently variable Cartesian product built here.
-/

namespace PallLean.Paper93.DeepMath.PathB.ExplicitCartesianReflection

open PallLean.Paper93.DeepMath.PathB.CartesianHankelWitness

/-- The direct semantic product construction. -/
def cartesianReflect {R Rows Cols : Type*} [Mul R]
    (old : Matrix Rows Cols R) : Matrix (Rows × Rows) (Cols × Cols) R :=
  old.kronecker old

/-- The direct product carries the required Cartesian witness by identity
row and column maps. -/
def cartesianReflectWitness {R Rows Cols : Type*} [Field R]
    [Fintype Rows] [Fintype Cols]
    (old : Matrix Rows Cols R) :
    CartesianWitness old (cartesianReflect old) where
  rowMap := id
  colMap := id
  product_submatrix := by
    ext row col
    rfl

/-- Consequently the explicit reflection squares semantic rank exactly. -/
theorem cartesianReflect_rank {R Rows Cols : Type*} [Field R]
    [Fintype Rows] [Fintype Cols] [DecidableEq Rows] [DecidableEq Cols]
    (old : Matrix Rows Cols R) :
    (cartesianReflect old).rank = old.rank * old.rank := by
  exact rank_kronecker_eq old old

/-- The explicit reflection squares the number of row indices. -/
theorem cartesianReflect_row_count {Rows : Type*} [Fintype Rows] :
    Fintype.card (Rows × Rows) = Fintype.card Rows * Fintype.card Rows := by
  simp

/-- The explicit reflection squares the number of column indices. -/
theorem cartesianReflect_col_count {Cols : Type*} [Fintype Cols] :
    Fintype.card (Cols × Cols) = Fintype.card Cols * Fintype.card Cols := by
  simp

/-- Materialising all entries squares the old matrix's explicit cell count. -/
theorem cartesianReflect_cell_count {Rows Cols : Type*}
    [Fintype Rows] [Fintype Cols] :
    Fintype.card (Rows × Rows) * Fintype.card (Cols × Cols) =
      (Fintype.card Rows * Fintype.card Cols) ^ 2 := by
  simp [pow_two]
  ring

/-- At any nontrivial dimension, the explicit row product is strictly larger
than the old row set. -/
theorem cartesianReflect_rows_strictly_grow {Rows : Type*} [Fintype Rows]
    (hrows : 2 ≤ Fintype.card Rows) :
    Fintype.card Rows < Fintype.card (Rows × Rows) := by
  rw [cartesianReflect_row_count]
  nlinarith

end PallLean.Paper93.DeepMath.PathB.ExplicitCartesianReflection

#print axioms PallLean.Paper93.DeepMath.PathB.ExplicitCartesianReflection.cartesianReflectWitness
#print axioms PallLean.Paper93.DeepMath.PathB.ExplicitCartesianReflection.cartesianReflect_rank
#print axioms PallLean.Paper93.DeepMath.PathB.ExplicitCartesianReflection.cartesianReflect_cell_count
#print axioms PallLean.Paper93.DeepMath.PathB.ExplicitCartesianReflection.cartesianReflect_rows_strictly_grow
