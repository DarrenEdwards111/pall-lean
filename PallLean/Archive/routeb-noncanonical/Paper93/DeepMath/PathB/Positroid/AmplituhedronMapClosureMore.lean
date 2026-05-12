import PallLean.Paper93.DeepMath.PathB.Positroid.AmplituhedronToyMap
import PallLean.Paper93.DeepMath.PathB.Positroid.AmplituhedronImageDef
import PallLean.Paper93.DeepMath.PathB.Positroid.AmplituhedronEmptyImage

/-!
# Further closure properties of the toy amplituhedron map

This file complements `AmplituhedronMapMore.lean` (closure under
addition and scalar multiplication) with additional structural
properties of the toy amplituhedron map and its image set:

* the map is compatible with negation (in `C` and in `Z`);
* the map is compatible with subtraction (in `C` and in `Z`);
* the image set is closed under negation and subtraction;
* full bilinear combination closure of the image set.

All proofs reduce to standard `Matrix` algebraic identities
(`Matrix.neg_mul`, `Matrix.sub_mul`, `Matrix.mul_neg`, `Matrix.mul_sub`,
`Matrix.add_mul`, `Matrix.smul_mul`) and are kernel-only: they rely
solely on `propext`, `Classical.choice`, and `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The amplituhedron map sends `-C` to the negation of `amplituhedronMap C Z`. -/
theorem amplituhedronMap_neg {k n m : ℕ}
    (C : Matrix (Fin k) (Fin n) ℝ) (Z : Matrix (Fin n) (Fin (k + m)) ℝ) :
    amplituhedronMap (-C) Z = -(amplituhedronMap C Z) := by
  unfold amplituhedronMap
  exact Matrix.neg_mul C Z

/-- The amplituhedron map sends `C` paired with `-Z` to the negation of `amplituhedronMap C Z`. -/
theorem amplituhedronMap_neg_Z {k n m : ℕ}
    (C : Matrix (Fin k) (Fin n) ℝ) (Z : Matrix (Fin n) (Fin (k + m)) ℝ) :
    amplituhedronMap C (-Z) = -(amplituhedronMap C Z) := by
  unfold amplituhedronMap
  exact Matrix.mul_neg C Z

/-- The amplituhedron map distributes over subtraction in `C`. -/
theorem amplituhedronMap_sub {k n m : ℕ}
    (C₁ C₂ : Matrix (Fin k) (Fin n) ℝ) (Z : Matrix (Fin n) (Fin (k + m)) ℝ) :
    amplituhedronMap (C₁ - C₂) Z = amplituhedronMap C₁ Z - amplituhedronMap C₂ Z := by
  unfold amplituhedronMap
  exact Matrix.sub_mul C₁ C₂ Z

/-- The amplituhedron map distributes over subtraction in `Z`. -/
theorem amplituhedronMap_sub_Z {k n m : ℕ}
    (C : Matrix (Fin k) (Fin n) ℝ) (Z₁ Z₂ : Matrix (Fin n) (Fin (k + m)) ℝ) :
    amplituhedronMap C (Z₁ - Z₂) = amplituhedronMap C Z₁ - amplituhedronMap C Z₂ := by
  unfold amplituhedronMap
  exact Matrix.mul_sub C Z₁ Z₂

/-- The amplituhedron image is closed under negation. -/
theorem amplituhedronImage_neg_closed {k n m : ℕ} (Z : Matrix (Fin n) (Fin (k + m)) ℝ)
    (A : Matrix (Fin k) (Fin (k + m)) ℝ) (hA : A ∈ amplituhedronImage Z) :
    -A ∈ amplituhedronImage Z := by
  obtain ⟨C, hC⟩ := hA
  refine ⟨-C, ?_⟩
  rw [amplituhedronMap_neg]
  rw [hC]

/-- The amplituhedron image is closed under subtraction. -/
theorem amplituhedronImage_sub_closed {k n m : ℕ} (Z : Matrix (Fin n) (Fin (k + m)) ℝ)
    (A B : Matrix (Fin k) (Fin (k + m)) ℝ)
    (hA : A ∈ amplituhedronImage Z) (hB : B ∈ amplituhedronImage Z) :
    A - B ∈ amplituhedronImage Z := by
  obtain ⟨CA, hCA⟩ := hA
  obtain ⟨CB, hCB⟩ := hB
  refine ⟨CA - CB, ?_⟩
  rw [amplituhedronMap_sub]
  rw [hCA, hCB]

/-- The amplituhedron image is closed under linear combinations
`α • A + β • B`: it remains in the image when `A` and `B` are. -/
theorem amplituhedronImage_linearCombo_closed {k n m : ℕ}
    (Z : Matrix (Fin n) (Fin (k + m)) ℝ) (α β : ℝ)
    (A B : Matrix (Fin k) (Fin (k + m)) ℝ)
    (hA : A ∈ amplituhedronImage Z) (hB : B ∈ amplituhedronImage Z) :
    α • A + β • B ∈ amplituhedronImage Z := by
  obtain ⟨CA, hCA⟩ := hA
  obtain ⟨CB, hCB⟩ := hB
  refine ⟨α • CA + β • CB, ?_⟩
  rw [amplituhedronMap_add, amplituhedronMap_smul, amplituhedronMap_smul]
  rw [hCA, hCB]

/-- Combined identity: the amplituhedron map sends `α • C₁ - β • C₂` to
`α • amplituhedronMap C₁ Z - β • amplituhedronMap C₂ Z`. -/
theorem amplituhedronMap_smul_sub {k n m : ℕ} (α β : ℝ)
    (C₁ C₂ : Matrix (Fin k) (Fin n) ℝ) (Z : Matrix (Fin n) (Fin (k + m)) ℝ) :
    amplituhedronMap (α • C₁ - β • C₂) Z =
      α • amplituhedronMap C₁ Z - β • amplituhedronMap C₂ Z := by
  rw [amplituhedronMap_sub, amplituhedronMap_smul, amplituhedronMap_smul]

end PallLean.Paper93.DeepMath.PathB.Positroid
