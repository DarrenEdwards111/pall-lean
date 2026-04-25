import PallLean.Paper93.DeepMath.PathB.Positroid.AmplituhedronToyMap
import PallLean.Paper93.DeepMath.PathB.Positroid.AmplituhedronImageDef

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- The amplituhedron image is closed under (linear) addition: A + B is in the image when both are. -/
theorem amplituhedronImage_add_closed {k n m : ℕ} (Z : Matrix (Fin n) (Fin (k + m)) ℝ)
    (A B : Matrix (Fin k) (Fin (k + m)) ℝ)
    (hA : A ∈ amplituhedronImage Z) (hB : B ∈ amplituhedronImage Z) :
    A + B ∈ amplituhedronImage Z := by
  obtain ⟨CA, hCA⟩ := hA
  obtain ⟨CB, hCB⟩ := hB
  refine ⟨CA + CB, ?_⟩
  rw [amplituhedronMap_add]
  rw [hCA, hCB]

/-- Scalar multiples of amplituhedron images are amplituhedron images. -/
theorem amplituhedronImage_smul_closed {k n m : ℕ} (Z : Matrix (Fin n) (Fin (k + m)) ℝ)
    (α : ℝ) (A : Matrix (Fin k) (Fin (k + m)) ℝ) (hA : A ∈ amplituhedronImage Z) :
    α • A ∈ amplituhedronImage Z := by
  obtain ⟨C, hC⟩ := hA
  refine ⟨α • C, ?_⟩
  rw [amplituhedronMap_smul]
  rw [hC]

end PallLean.Paper93.DeepMath.PathB.Positroid
