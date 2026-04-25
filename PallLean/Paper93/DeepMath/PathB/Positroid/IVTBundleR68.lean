import PallLean.Paper93.DeepMath.PathB.Positroid.N3IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N4IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N5IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N6IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N7IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N8IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N9IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N10IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N11IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N12IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N13IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N14IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N15IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N16IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N17IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N18IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N19IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N20IVTExistence

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- IVT bundle for n=3..20.

Note: For n=3..18 we use the strict-bound versions (`α < 1`), matching the
exports of `N3IVTExistence` ... `N18IVTExistence`.  For n=19, 20 the
underlying existence files only export weak-bound versions (`α ≤ 1`), so we
use those as published. -/
theorem ivt_bundle_r68_n3_to_n20 :
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 3)^2 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 4)^3 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 5)^4 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 6)^5 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 7)^6 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 8)^7 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 9)^8 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 10)^9 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 11)^10 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 12)^11 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 13)^12 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 14)^13 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 15)^14 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 16)^15 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 17)^16 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 18)^17 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ α * (α + 19)^18 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ α * (α + 20)^19 = 1) :=
  ⟨exists_alpha_n3_det_one, exists_alpha_n4_det_one, exists_alpha_n5_det_one,
   exists_alpha_n6_det_one, exists_alpha_n7_det_one, exists_alpha_n8_det_one,
   exists_alpha_n9_det_one, exists_alpha_n10_det_one, exists_alpha_n11_det_one,
   exists_alpha_n12_det_one, exists_alpha_n13_det_one, exists_alpha_n14_det_one,
   exists_alpha_n15_det_one, exists_alpha_n16_det_one, exists_alpha_n17_det_one,
   exists_alpha_n18_det_one, exists_alpha_n19_det_one_le,
   exists_alpha_n20_det_one_le⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
