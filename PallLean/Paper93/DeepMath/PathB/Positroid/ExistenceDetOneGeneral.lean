import PallLean.Paper93.DeepMath.PathB.Positroid.IVTGeneralN
import PallLean.Paper93.DeepMath.PathB.Positroid.N3IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N4IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N5IVTExistence

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- Bundle: ∃ α with the n-specific equation, for each n=3,4,5. -/
theorem exists_alpha_each_n_3_4_5 :
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 3)^2 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 4)^3 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 5)^4 = 1) :=
  ⟨exists_alpha_n3_det_one, exists_alpha_n4_det_one, exists_alpha_n5_det_one⟩

/-- General-n IVT existence (n ≥ 2). -/
theorem exists_alpha_general_n_ge_2 (n : ℕ) (hn : 2 ≤ n) :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ α * (α + n)^(n-1) = 1 :=
  exists_alpha_general_n_det_one n hn

end PallLean.Paper93.DeepMath.PathB.Positroid
