import PallLean.Paper93.DeepMath.PathB.Positroid.AmplituhedronToyMap

/-!
# Amplituhedron map: empty / trivial input properties

This file collects elementary structural properties of the toy
amplituhedron map at empty or trivial inputs, complementing the
linearity-in-`C` lemmas of `AmplituhedronToyMap`. We record the
following:

* the value at the zero `C` matrix is zero;
* the value at the zero `Z` matrix is zero;
* the map is linear in `Z` (scalar multiplication and addition);
* a combined bilinearity statement in `C` (with `Z` fixed).

All proofs reduce to standard `Matrix` algebraic identities and are
kernel-only (no `sorry`, no custom `axiom`, no `True` placeholder).
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The amplituhedron map at zero matrix gives zero. -/
theorem amplituhedronMap_zero_input {k n m : ℕ} (Z : Matrix (Fin n) (Fin (k + m)) ℝ) :
    amplituhedronMap (0 : Matrix (Fin k) (Fin n) ℝ) Z = 0 :=
  amplituhedronMap_zero Z

/-- The amplituhedron map at zero Z matrix gives zero. -/
theorem amplituhedronMap_zero_Z {k n m : ℕ} (C : Matrix (Fin k) (Fin n) ℝ) :
    amplituhedronMap C (0 : Matrix (Fin n) (Fin (k + m)) ℝ) = 0 := by
  unfold amplituhedronMap
  exact Matrix.mul_zero C

/-- The amplituhedron map distributes over scalar multiplication of Z. -/
theorem amplituhedronMap_smul_Z {k n m : ℕ} (α : ℝ)
    (C : Matrix (Fin k) (Fin n) ℝ) (Z : Matrix (Fin n) (Fin (k + m)) ℝ) :
    amplituhedronMap C (α • Z) = α • (amplituhedronMap C Z) := by
  unfold amplituhedronMap
  exact Matrix.mul_smul C α Z

/-- The amplituhedron map distributes over addition of Z. -/
theorem amplituhedronMap_add_Z {k n m : ℕ}
    (C : Matrix (Fin k) (Fin n) ℝ) (Z₁ Z₂ : Matrix (Fin n) (Fin (k + m)) ℝ) :
    amplituhedronMap C (Z₁ + Z₂) = amplituhedronMap C Z₁ + amplituhedronMap C Z₂ := by
  unfold amplituhedronMap
  exact Matrix.mul_add C Z₁ Z₂

/-- The amplituhedron map is bilinear: linearity in both C and Z. -/
theorem amplituhedronMap_bilinear {k n m : ℕ} (α : ℝ)
    (C₁ C₂ : Matrix (Fin k) (Fin n) ℝ) (Z₁ Z₂ : Matrix (Fin n) (Fin (k + m)) ℝ) :
    amplituhedronMap (α • C₁ + C₂) Z₁
      = α • amplituhedronMap C₁ Z₁ + amplituhedronMap C₂ Z₁ := by
  unfold amplituhedronMap
  rw [Matrix.add_mul, Matrix.smul_mul]

end PallLean.Paper93.DeepMath.PathB.Positroid
