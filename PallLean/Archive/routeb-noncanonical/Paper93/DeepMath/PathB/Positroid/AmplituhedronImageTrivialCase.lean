import PallLean.Paper93.DeepMath.PathB.Positroid.AmplituhedronToyMap
import PallLean.Paper93.DeepMath.PathB.Positroid.AmplituhedronImageDef

/-!
# Amplituhedron image: trivial-case characterizations

This file collects elementary trivial-case characterizations of the
amplituhedron image set defined in `AmplituhedronImageDef.lean`:

* the image at the zero `Z` matrix is the singleton `{0}`;
* the zero matrix is always in the image (any `Z`);
* the image is non-empty for any `Z`.

All proofs reduce to the linearity facts already established for
`amplituhedronMap` in `AmplituhedronToyMap.lean` and the membership
lemma in `AmplituhedronImageDef.lean`. The development is kernel-only,
relying solely on `propext`, `Classical.choice`, and `Quot.sound`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The amplituhedron image at the zero Z matrix is `{0}`. -/
theorem amplituhedronImage_at_zero_Z {k n m : ℕ} :
    amplituhedronImage (0 : Matrix (Fin n) (Fin (k + m)) ℝ) = {(0 : Matrix (Fin k) (Fin (k + m)) ℝ)} := by
  unfold amplituhedronImage
  ext Y
  constructor
  · rintro ⟨C, hC⟩
    have : amplituhedronMap C (0 : Matrix (Fin n) (Fin (k + m)) ℝ) = 0 := by
      unfold amplituhedronMap
      exact Matrix.mul_zero C
    rw [this] at hC
    rw [Set.mem_singleton_iff]
    exact hC.symm
  · intro h
    rw [Set.mem_singleton_iff] at h
    refine ⟨0, ?_⟩
    rw [amplituhedronMap_zero, h]

/-- Zero is in the amplituhedron image of any Z. -/
theorem zero_in_amplituhedronImage {k n m : ℕ}
    (Z : Matrix (Fin n) (Fin (k + m)) ℝ) :
    (0 : Matrix (Fin k) (Fin (k + m)) ℝ) ∈ amplituhedronImage Z :=
  zero_mem_amplituhedronImage Z

/-- The amplituhedron image is non-empty. -/
theorem amplituhedronImage_nonempty {k n m : ℕ}
    (Z : Matrix (Fin n) (Fin (k + m)) ℝ) :
    (amplituhedronImage Z).Nonempty :=
  ⟨0, zero_in_amplituhedronImage Z⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
