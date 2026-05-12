import PallLean.Paper93.DeepMath.PathB.Positroid.AmplituhedronToyMap
import PallLean.Paper93.DeepMath.PathB.Positroid.AmplituhedronEmptyImage

namespace PallLean.Paper93.DeepMath.PathB.Positroid

theorem amplituhedron_linearity_full {k n m : ℕ} (α β : ℝ)
    (C₁ C₂ : Matrix (Fin k) (Fin n) ℝ) (Z : Matrix (Fin n) (Fin (k + m)) ℝ) :
    amplituhedronMap (α • C₁ + β • C₂) Z =
      α • amplituhedronMap C₁ Z + β • amplituhedronMap C₂ Z := by
  unfold amplituhedronMap
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul]

theorem amplituhedron_zero_in_zero_out {k n m : ℕ} (Z : Matrix (Fin n) (Fin (k + m)) ℝ) :
    amplituhedronMap (0 : Matrix (Fin k) (Fin n) ℝ) Z = 0 :=
  amplituhedronMap_zero Z

theorem amplituhedron_z_zero_out_zero {k n m : ℕ} (C : Matrix (Fin k) (Fin n) ℝ) :
    amplituhedronMap C (0 : Matrix (Fin n) (Fin (k + m)) ℝ) = 0 :=
  amplituhedronMap_zero_Z C

theorem amplituhedron_distributive_over_C {k n m : ℕ}
    (C₁ C₂ : Matrix (Fin k) (Fin n) ℝ) (Z : Matrix (Fin n) (Fin (k + m)) ℝ) :
    amplituhedronMap (C₁ + C₂) Z = amplituhedronMap C₁ Z + amplituhedronMap C₂ Z :=
  amplituhedronMap_add C₁ C₂ Z

theorem amplituhedron_distributive_over_Z {k n m : ℕ}
    (C : Matrix (Fin k) (Fin n) ℝ) (Z₁ Z₂ : Matrix (Fin n) (Fin (k + m)) ℝ) :
    amplituhedronMap C (Z₁ + Z₂) = amplituhedronMap C Z₁ + amplituhedronMap C Z₂ :=
  amplituhedronMap_add_Z C Z₁ Z₂

end PallLean.Paper93.DeepMath.PathB.Positroid
