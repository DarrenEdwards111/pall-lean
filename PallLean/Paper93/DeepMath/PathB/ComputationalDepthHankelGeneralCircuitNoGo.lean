import PallLean.Paper93.DeepMath.PathB.ComputationalDepthEqualityUpperBounds
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHankelProductCapture

/-!
# Raw semantic Hankel rank does not bound unrestricted circuit size

Equality is the decisive obstruction.  Across the natural left/right split,
its communication/Hankel matrix is the identity matrix on `2^n` rows and has
rank `2^n`.  Nevertheless the repository already constructs an equality
formula of size at most `10*n+1`.

Consequently, a large partition rank alone cannot upper-bound even formula
size, hence cannot upper-bound unrestricted circuit size.  Any successful
Gödel-tower capture theorem needs an additional solver-specific extraction
property; the raw semantic rank proposed in the previous conditional bridge
is insufficient.
-/

namespace PallLean.Paper93.DeepMath.PathB.HankelGeneralCircuitNoGo

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.PathB.SplitFormula

/-- Equality's semantic matrix after enumerating all `n`-bit rows and columns.
It is definitionally the identity matrix of dimension `2^n`. -/
def equalityHankel (n : Nat) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℚ := 1

/-- Equality has exponential rational Hankel rank under the natural split. -/
theorem equalityHankel_rank (n : Nat) :
    (equalityHankel n).rank = 2 ^ n := by
  rw [equalityHankel, Matrix.rank_one]
  simp

/-- Whenever the elementary exponential exceeds the certified linear formula
bound, equality's semantic rank is strictly larger than the size of an actual
formula computing equality. -/
theorem equality_rank_exceeds_formula_size {n : Nat}
    (hscale : 10 * n + 1 < 2 ^ n) :
    (equalityFormula n).size < (equalityHankel n).rank := by
  rw [equalityHankel_rank]
  exact lt_of_le_of_lt (equalityFormula_size_le n) hscale

/-- Concrete kernel-checked counterexample: at ten bits the equality Hankel
rank is `1024`, while the explicit equality formula has size at most `101`. -/
theorem equality_rank_exceeds_formula_size_at_ten :
    (equalityFormula 10).size < (equalityHankel 10).rank := by
  apply equality_rank_exceeds_formula_size
  norm_num

/-- Refutes the raw universal bridge `semantic rank ≤ formula size`.  Since
formulas are a restricted form of circuits, raw rank cannot be used as a
general-circuit size measure either. -/
theorem not_all_equality_rank_le_formula_size :
    ¬ ∀ n : Nat, (equalityHankel n).rank ≤ (equalityFormula n).size := by
  intro claimed
  exact (Nat.not_lt_of_ge (claimed 10)) equality_rank_exceeds_formula_size_at_ten

end PallLean.Paper93.DeepMath.PathB.HankelGeneralCircuitNoGo

#print axioms PallLean.Paper93.DeepMath.PathB.HankelGeneralCircuitNoGo.equalityHankel_rank
#print axioms PallLean.Paper93.DeepMath.PathB.HankelGeneralCircuitNoGo.equality_rank_exceeds_formula_size
#print axioms PallLean.Paper93.DeepMath.PathB.HankelGeneralCircuitNoGo.equality_rank_exceeds_formula_size_at_ten
#print axioms PallLean.Paper93.DeepMath.PathB.HankelGeneralCircuitNoGo.not_all_equality_rank_le_formula_size
