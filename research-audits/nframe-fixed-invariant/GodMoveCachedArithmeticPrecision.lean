import GodMoveCachedBasisPrecision
import GodMoveCachedResidualMatrix
import GodMoveTrackedArithmeticPrecision

/-!
# Rational precision in cached discovery and selection arithmetic

The readiness invariant derives the stored-row bounds from actual Boolean-row
insertions. This file uses those bounds to cover every rational operand,
product, quotient, subtraction and dot-product accumulator in the cached
insertion and residual-matrix programs. Rejected rows are covered too.

These are canonical rational precision bounds. They do not count the integer
operations inside rational primitives or the host work compiling SAT queries.
-/

namespace GodMoveCachedArithmeticPrecision

open GodMoveCachedDiscoveryBasis GodMoveCachedBasisPrecision
open GodMoveTrackedOrthogonalization (Row rowValue)
open GodMoveTrackedArithmeticPrecision (arithmeticBits)
open GodMoveRationalPrecisionArithmetic GodMoveDotLoopPrecision
open scoped BigOperators

def scalarBits (s : ℕ) : ℕ := 2 * GodMoveCachedBasisPrecision.normBits s

private theorem boolean_bitBound (q : ℚ) (hq : q = 0 ∨ q = 1) : BitBound q 0 := by
  rcases hq with rfl | rfl <;> norm_num [BitBound, Bound]

private theorem row_le_scalar (s : ℕ) : rowBits s ≤ scalarBits s := by
  unfold scalarBits GodMoveCachedBasisPrecision.normBits
  nlinarith

private theorem norm_le_scalar (s : ℕ) : GodMoveCachedBasisPrecision.normBits s ≤ scalarBits s := by
  unfold scalarBits
  omega

private theorem scaled_le_scalar (s : ℕ) :
    rowBits s + GodMoveCachedBasisPrecision.normBits s ≤ scalarBits s := by
  unfold scalarBits GodMoveCachedBasisPrecision.normBits
  nlinarith

private theorem scalar_le_arithmetic (s : ℕ) : scalarBits s ≤ arithmeticBits s := by
  unfold scalarBits GodMoveCachedBasisPrecision.normBits rowBits arithmeticBits
  ring_nf
  omega

private theorem uniform_dot {s m : ℕ} (hm : m ≤ s) (v w : Fin m → ℚ)
    (hv : ∀ i, BitBound (v i) (scalarBits s))
    (hw : ∀ i, BitBound (w i) (scalarBits s)) :
    DotPrecision v w (arithmeticBits s) := by
  apply dotPrecision_of_bounds v w (scalarBits s) (scalarBits s) (arithmeticBits s) hv hw
  · exact scalar_le_arithmetic s
  · exact scalar_le_arithmetic s
  · unfold scalarBits GodMoveCachedBasisPrecision.normBits rowBits arithmeticBits
    ring_nf
    omega
  · have h := Nat.mul_le_mul_left (scalarBits s + scalarBits s + 1) hm
    unfold scalarBits GodMoveCachedBasisPrecision.normBits rowBits arithmeticBits at *
    nlinarith

theorem components_bitBound {s : ℕ} (B : CachedBasis s) (hB : Ready B)
    (v : Row s) (hv : BooleanRow (rowValue v)) (i : Fin B.count) :
    BitBound (GodMoveTrackedOrthogonalizationCost.components v B.rows B.norms).value[i]
      (scalarBits s) := by
  have hdot := dot_bitBound Finset.univ (fun j : Fin s => v[j])
    (fun j => B.rows[i][j]) 0 (rowBits s)
    (fun j _ => boolean_bitBound _ (hv j)) (fun j _ => hB.rows i j)
  have hn : BitBound (∑ j : Fin s, v[j] * B.rows[i][j])
      (GodMoveCachedBasisPrecision.normBits s) := by
    apply hdot.mono
    simp only [Finset.card_univ, Fintype.card_fin]
    unfold GodMoveCachedBasisPrecision.normBits
    nlinarith
  have h := hn.div (norms_bitBound B hB i)
  simpa [GodMoveTrackedOrthogonalizationCost.components_value, scalarBits, two_mul] using h

/-- Includes operands and all intermediate dot-product accumulator values. -/
structure MatrixPrecision {s : ℕ} (B : CachedBasis s) (b : ℕ) : Prop where
  rows : ∀ (i : Fin B.count) (j : Fin s), BitBound B.rows[i][j] b
  norms : ∀ i : Fin B.count, BitBound B.norms[i] b
  scaled : ∀ (i : Fin B.count) (j : Fin s),
    BitBound (GodMoveCachedResidualMatrix.scaledRows B).value[i][j] b
  dots : ∀ j i : Fin s,
    DotPrecision (fun h : Fin B.count => (GodMoveCachedResidualMatrix.scaledRows B).value[h][i])
      (fun h => B.rows[h][j]) b
  entries : ∀ j i : Fin s, BitBound (GodMoveCachedResidualMatrix.residualMatrix B).value[j][i] b

structure InsertPrecision {s : ℕ} (B : CachedBasis s) (v : Row s) (b : ℕ) : Prop where
  input : ∀ j : Fin s, BitBound v[j] b
  rows : ∀ (i : Fin B.count) (j : Fin s), BitBound B.rows[i][j] b
  norms : ∀ i : Fin B.count, BitBound B.norms[i] b
  componentDots : ∀ i : Fin B.count,
    DotPrecision (fun j : Fin s => v[j]) (fun j => B.rows[i][j]) b
  components : ∀ i : Fin B.count,
    BitBound (GodMoveTrackedOrthogonalizationCost.components v B.rows B.norms).value[i] b
  residualDots : ∀ j : Fin s,
    DotPrecision
      (fun i : Fin B.count =>
        (GodMoveTrackedOrthogonalizationCost.components v B.rows B.norms).value[i])
      (fun i => B.rows[i][j]) b
  residualEntries : ∀ j : Fin s, BitBound (GodMoveCachedDiscoveryBasis.residual B v).value[j] b
  normDot : DotPrecision
    (fun j : Fin s => (GodMoveCachedDiscoveryBasis.residual B v).value[j])
    (fun j => (GodMoveCachedDiscoveryBasis.residual B v).value[j]) b

theorem matrix_precision {s : ℕ} (B : CachedBasis s) (hB : Ready B) :
    MatrixPrecision B (arithmeticBits s) := by
  have hr : ∀ (i : Fin B.count) (j : Fin s), BitBound B.rows[i][j] (scalarBits s) :=
    fun i j => (hB.rows i j).mono (row_le_scalar s)
  have hs : ∀ (i : Fin B.count) (j : Fin s),
      BitBound (GodMoveCachedResidualMatrix.scaledRows B).value[i][j]
      (scalarBits s) := by
    intro i j
    have h := ((hB.rows i j).div (norms_bitBound B hB i)).mono (scaled_le_scalar s)
    simpa [GodMoveCachedResidualMatrix.scaledRows_value] using h
  refine {
    rows := fun i j => (hr i j).mono (scalar_le_arithmetic s)
    norms := fun i => (norms_bitBound B hB i).mono
      ((norm_le_scalar s).trans (scalar_le_arithmetic s))
    scaled := fun i j => (hs i j).mono (scalar_le_arithmetic s)
    dots := fun j i => uniform_dot (count_le_width B) _ _
      (fun h => hs h i) (fun h => hr h j)
    entries := ?_
  }
  intro j i
  have hd := dot_bitBound Finset.univ
    (fun h : Fin B.count => (GodMoveCachedResidualMatrix.scaledRows B).value[h][i])
    (fun h => B.rows[h][j]) (scalarBits s) (scalarBits s)
    (fun h _ => hs h i) (fun h _ => hr h j)
  have hzero : BitBound (if j = i then (1 : ℚ) else 0) 0 := by
    split <;> norm_num [BitBound, Bound]
  have he := hzero.sub hd
  have hb : 0 + ((scalarBits s + scalarBits s + 1) *
      (Finset.univ : Finset (Fin B.count)).card) + 1 ≤
      arithmeticBits s := by
    simp only [Finset.card_univ, Fintype.card_fin]
    have h := Nat.mul_le_mul_left (scalarBits s + scalarBits s + 1) (count_le_width B)
    unfold scalarBits GodMoveCachedBasisPrecision.normBits rowBits arithmeticBits at *
    nlinarith
  have h := he.mono hb
  simpa [GodMoveCachedResidualMatrix.residualMatrix,
    GodMoveTrackedOrthogonalizationCost.tabulate_value,
    GodMoveTrackedOrthogonalizationCost.sumProducts_value,
    GodMoveTrackedOrthogonalizationCost.qsub] using h

/-- Every rational stage of an actual Boolean-row insertion, regardless of
whether the row is accepted or rejected by the final zero comparison. -/
theorem insert_precision {s : ℕ} (B : CachedBasis s) (hB : Ready B)
    (v : Row s) (hv : BooleanRow (rowValue v)) : InsertPrecision B v (arithmeticBits s) := by
  have hr : ∀ (i : Fin B.count) (j : Fin s), BitBound B.rows[i][j] (scalarBits s) :=
    fun i j => (hB.rows i j).mono (row_le_scalar s)
  have hu : ∀ j : Fin s,
      BitBound (GodMoveCachedDiscoveryBasis.residual B v).value[j] (scalarBits s) :=
    fun j => (residual_bitBound B hB v hv j).mono (row_le_scalar s)
  exact {
    input := fun j => (boolean_bitBound _ (hv j)).mono (Nat.zero_le _)
    rows := fun i j => (hr i j).mono (scalar_le_arithmetic s)
    norms := fun i => (norms_bitBound B hB i).mono
      ((norm_le_scalar s).trans (scalar_le_arithmetic s))
    componentDots := fun i => uniform_dot le_rfl _ _
      (fun j => (boolean_bitBound _ (hv j)).mono (Nat.zero_le _)) (fun j => hr i j)
    components := fun i => (components_bitBound B hB v hv i).mono (scalar_le_arithmetic s)
    residualDots := fun j => uniform_dot (count_le_width B) _ _
      (fun i => components_bitBound B hB v hv i) (fun i => hr i j)
    residualEntries := fun j => (hu j).mono (scalar_le_arithmetic s)
    normDot := uniform_dot le_rfl _ _ hu hu
  }

end GodMoveCachedArithmeticPrecision

#print axioms GodMoveCachedArithmeticPrecision.components_bitBound
#print axioms GodMoveCachedArithmeticPrecision.matrix_precision
#print axioms GodMoveCachedArithmeticPrecision.insert_precision
