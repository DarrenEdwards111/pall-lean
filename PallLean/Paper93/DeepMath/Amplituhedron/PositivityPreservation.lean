import Mathlib.Analysis.Matrix.PosDef

namespace PallLean.Paper93.DeepMath.Amplituhedron

theorem identity_preserves_posSemidef {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.PosSemidef) :
    (1 * A * 1).PosSemidef := by
  simp [Matrix.one_mul, Matrix.mul_one]; exact hA

end PallLean.Paper93.DeepMath.Amplituhedron
