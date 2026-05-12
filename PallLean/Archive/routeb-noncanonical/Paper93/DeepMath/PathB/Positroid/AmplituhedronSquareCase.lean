import PallLean.Paper93.DeepMath.PathB.Positroid.AmplituhedronToyMap

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- For the square k=n case (m=0), amplituhedron map is just C * Z. -/
theorem amplituhedronMap_square_eq_mul {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (Z : Matrix (Fin n) (Fin (n + 0)) ℝ) :
    amplituhedronMap C Z = C * Z := rfl

/-- At k=n, m=0, the amplituhedron map at C=1 returns Z. -/
theorem amplituhedronMap_square_id (n : ℕ) (Z : Matrix (Fin n) (Fin (n + 0)) ℝ) :
    amplituhedronMap (1 : Matrix (Fin n) (Fin n) ℝ) Z = Z := by
  rw [amplituhedronMap_square_eq_mul]
  exact Matrix.one_mul Z

/-- At k=n, m=0, the amplituhedron map at C=0 returns 0. -/
theorem amplituhedronMap_square_zero (n : ℕ) (Z : Matrix (Fin n) (Fin (n + 0)) ℝ) :
    amplituhedronMap (0 : Matrix (Fin n) (Fin n) ℝ) Z = 0 := by
  rw [amplituhedronMap_square_eq_mul]
  exact Matrix.zero_mul Z

end PallLean.Paper93.DeepMath.PathB.Positroid
