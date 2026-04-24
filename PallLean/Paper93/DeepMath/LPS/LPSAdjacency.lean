import Mathlib.Data.Nat.Basic

namespace PallLean.Paper93.DeepMath.LPS

def lpsDegree (p : ℕ) : ℕ := p + 1

theorem lpsDegree_formula (p : ℕ) : lpsDegree p = p + 1 := rfl

theorem lpsDegree_pos (p : ℕ) (hp : 0 < p) : 0 < lpsDegree p := by
  unfold lpsDegree; omega

end PallLean.Paper93.DeepMath.LPS
