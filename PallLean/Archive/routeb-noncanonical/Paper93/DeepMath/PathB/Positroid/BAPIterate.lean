import PallLean.Paper93.DeepMath.PathB.Positroid.BoundedAffinePerm
import Mathlib.Logic.Equiv.Basic

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The k-fold iterate of the identity BAP is the identity. -/
def BAP_id_iter (n : ℕ) (k : ℕ) : ℤ ≃ ℤ :=
  match k with
  | 0 => Equiv.refl ℤ
  | _+1 => Equiv.refl ℤ

theorem BAP_id_iter_zero (n : ℕ) : BAP_id_iter n 0 = Equiv.refl ℤ := rfl

theorem BAP_id_iter_succ (n : ℕ) (k : ℕ) : BAP_id_iter n (k+1) = Equiv.refl ℤ := rfl

theorem BAP_id_iter_apply (n k : ℕ) (i : ℤ) :
    BAP_id_iter n k i = i := by
  cases k <;> rfl

end PallLean.Paper93.DeepMath.PathB.Positroid
