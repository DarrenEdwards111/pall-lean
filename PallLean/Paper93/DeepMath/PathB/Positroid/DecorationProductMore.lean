import PallLean.Paper93.DeepMath.PathB.Positroid.DecorationProduct
import PallLean.Paper93.DeepMath.PathB.Positroid.DecoratedPermutation

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- For n=1, signProduct of negated identity is -1. -/
theorem neg_id_signProduct_n1 :
    (DecoratedPermutation.neg_id 1).signProduct = -1 := by
  rw [DecoratedPermutation.neg_id_signProduct]; norm_num

/-- For n=2, signProduct of negated identity is 1 (= (-1)²). -/
theorem neg_id_signProduct_n2 :
    (DecoratedPermutation.neg_id 2).signProduct = 1 := by
  rw [DecoratedPermutation.neg_id_signProduct]; norm_num

/-- For n=3, signProduct of negated identity is -1 (= (-1)³). -/
theorem neg_id_signProduct_n3 :
    (DecoratedPermutation.neg_id 3).signProduct = -1 := by
  rw [DecoratedPermutation.neg_id_signProduct]; norm_num

/-- For n=4, signProduct of negated identity is 1 (= (-1)⁴). -/
theorem neg_id_signProduct_n4 :
    (DecoratedPermutation.neg_id 4).signProduct = 1 := by
  rw [DecoratedPermutation.neg_id_signProduct]; norm_num

/-- For any even n, signProduct of negated identity is 1. -/
theorem neg_id_signProduct_even (k : ℕ) :
    (DecoratedPermutation.neg_id (2 * k)).signProduct = 1 := by
  rw [DecoratedPermutation.neg_id_signProduct]
  rw [show (2 * k) = 2 * k from rfl]
  rw [pow_mul]; norm_num

end PallLean.Paper93.DeepMath.PathB.Positroid
