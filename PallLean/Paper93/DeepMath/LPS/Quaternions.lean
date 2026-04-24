import Mathlib.Tactic.Positivity

namespace PallLean.Paper93.DeepMath.LPS

structure IntQuaternion where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ

def IntQuaternion.norm (q : IntQuaternion) : ℤ := q.a^2 + q.b^2 + q.c^2 + q.d^2

theorem IntQuaternion.norm_nonneg (q : IntQuaternion) : 0 ≤ q.norm := by
  unfold IntQuaternion.norm; positivity

end PallLean.Paper93.DeepMath.LPS
