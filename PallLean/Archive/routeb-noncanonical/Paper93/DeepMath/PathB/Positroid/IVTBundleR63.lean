import PallLean.Paper93.DeepMath.PathB.Positroid.N3IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N4IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N5IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N6IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N7IVTExistence

namespace PallLean.Paper93.DeepMath.PathB.Positroid

theorem ivt_bundle_r63 :
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 3)^2 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 4)^3 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 5)^4 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 6)^5 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 7)^6 = 1) :=
  ⟨exists_alpha_n3_det_one, exists_alpha_n4_det_one, exists_alpha_n5_det_one,
   exists_alpha_n6_det_one, exists_alpha_n7_det_one⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
