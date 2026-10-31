import Mathlib
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHankelProductCapture

/-!
# Cartesian witnesses force Hankel rank squaring

This is the strongest non-circular theorem surviving the solver-capture audit.
If the next reflection matrix contains, under explicit row and column maps, a
submatrix equal to the Kronecker square of the previous matrix, then the next
rank is at least the square of the previous rank.

The Cartesian witness is concrete data.  This file does not claim arbitrary
SAT correctness or Gödel reflection produces such a witness; establishing that
for the intended succinct tower remains the open construction theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB.CartesianHankelWitness

/-- Exact rank multiplicativity of finite matrices under Kronecker product. -/
theorem rank_kronecker_eq {R : Type*} [Field R]
    {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (A : Matrix l m R) (B : Matrix n p R) :
    (A.kronecker B).rank = A.rank * B.rank := by
  classical
  let bl : Module.Basis l R (l → R) := Pi.basisFun R l
  let bm : Module.Basis m R (m → R) := Pi.basisFun R m
  let bn : Module.Basis n R (n → R) := Pi.basisFun R n
  let bp : Module.Basis p R (p → R) := Pi.basisFun R p
  let f : (m → R) →ₗ[R] (l → R) := Matrix.toLin bm bl A
  let g : (p → R) →ₗ[R] (n → R) := Matrix.toLin bp bn B
  have hA : A.rank = Module.finrank R (LinearMap.range f) := by
    simpa [f, bl, bm] using Matrix.rank_eq_finrank_range_toLin A bl bm
  have hB : B.rank = Module.finrank R (LinearMap.range g) := by
    simpa [g, bn, bp] using Matrix.rank_eq_finrank_range_toLin B bn bp
  have hAB :
      Matrix.toLin (bm.tensorProduct bp) (bl.tensorProduct bn) (A.kronecker B) =
        TensorProduct.map f g := by
    exact Matrix.toLin_kronecker (bM := bm) (bN := bp) (bM' := bl) (bN' := bn) A B
  rw [Matrix.rank_eq_finrank_range_toLin (A.kronecker B)
    (bl.tensorProduct bn) (bm.tensorProduct bp), hAB]
  have hRange :
      LinearMap.range (TensorProduct.map f g) =
        LinearMap.range
          (TensorProduct.mapIncl (LinearMap.range f) (LinearMap.range g)) := by
    exact (TensorProduct.range_map f g).trans
      (TensorProduct.range_mapIncl (LinearMap.range f) (LinearMap.range g)).symm
  rw [hRange]
  rw [LinearMap.finrank_range_of_inj
    (Module.Flat.tensorProduct_mapIncl_injective_of_left
      (LinearMap.range f) (LinearMap.range g))]
  rw [Module.finrank_tensorProduct, ← hA, ← hB]

/-- Restricting arbitrary finite rows and columns cannot increase rank. -/
theorem rank_submatrix_maps_le {R : Type*} [Field R]
    {rows cols subRows subCols : Type*}
    [Fintype rows] [Fintype cols] [Fintype subRows] [Fintype subCols]
    (A : Matrix rows cols R) (rowMap : subRows → rows)
    (colMap : subCols → cols) :
    (A.submatrix rowMap colMap).rank ≤ A.rank := by
  classical
  have hcols :
      (A.submatrix (Equiv.refl rows) colMap).rank ≤ A.rank := by
    have htranspose :
        (A.submatrix (Equiv.refl rows) colMap).transpose.rank ≤
          A.transpose.rank := by
      simpa [Matrix.transpose_submatrix] using
        Matrix.rank_submatrix_le (f := colMap) (e := Equiv.refl rows)
          (A := A.transpose)
    calc
      (A.submatrix (Equiv.refl rows) colMap).rank
          = (A.submatrix (Equiv.refl rows) colMap).transpose.rank := by
              symm
              exact Matrix.rank_transpose _
      _ ≤ A.transpose.rank := htranspose
      _ = A.rank := Matrix.rank_transpose _
  have hrows :
      ((A.submatrix (Equiv.refl rows) colMap).submatrix rowMap
        (Equiv.refl subCols)).rank ≤
        (A.submatrix (Equiv.refl rows) colMap).rank := by
    exact Matrix.rank_submatrix_le (f := rowMap) (e := Equiv.refl subCols)
      (A := A.submatrix (Equiv.refl rows) colMap)
  have hcompose :
      (A.submatrix (Equiv.refl rows) colMap).submatrix rowMap
          (Equiv.refl subCols) = A.submatrix rowMap colMap := by
    simpa [Matrix.submatrix_submatrix, Function.comp_def]
  rw [hcompose] at hrows
  exact le_trans hrows hcols

/-- Explicit Cartesian product witness inside a next-stage matrix. -/
structure CartesianWitness {R : Type*} [Field R]
    {oldRows oldCols nextRows nextCols : Type*}
    [Fintype oldRows] [Fintype oldCols]
    (old : Matrix oldRows oldCols R)
    (next : Matrix nextRows nextCols R) where
  rowMap : oldRows × oldRows → nextRows
  colMap : oldCols × oldCols → nextCols
  product_submatrix : next.submatrix rowMap colMap = old.kronecker old

/-- A Cartesian witness forces rank-square growth at one reflection step. -/
theorem rank_sq_le_next {R : Type*} [Field R]
    {oldRows oldCols nextRows nextCols : Type*}
    [Fintype oldRows] [Fintype oldCols]
    [Fintype nextRows] [Fintype nextCols]
    [DecidableEq oldRows] [DecidableEq oldCols]
    (old : Matrix oldRows oldCols R)
    (next : Matrix nextRows nextCols R)
    (witness : CartesianWitness old next) :
    old.rank * old.rank ≤ next.rank := by
  calc
    old.rank * old.rank = (old.kronecker old).rank :=
      (rank_kronecker_eq old old).symm
    _ = (next.submatrix witness.rowMap witness.colMap).rank := by
      rw [witness.product_submatrix]
    _ ≤ next.rank := rank_submatrix_maps_le next witness.rowMap witness.colMap

end PallLean.Paper93.DeepMath.PathB.CartesianHankelWitness

#print axioms PallLean.Paper93.DeepMath.PathB.CartesianHankelWitness.rank_kronecker_eq
#print axioms PallLean.Paper93.DeepMath.PathB.CartesianHankelWitness.rank_submatrix_maps_le
#print axioms PallLean.Paper93.DeepMath.PathB.CartesianHankelWitness.rank_sq_le_next
