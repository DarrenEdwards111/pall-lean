import PallLean.Paper93.DeepMath.PathB.Positroid.N15IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N16IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N17IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N18IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N19IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N20IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N21IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N22IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N23N24IVTExistence

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- Round-69 IVT existence bundle for n=15..24.

This bundle assembles the IVT-based existence statements
`α ∈ (0, 1)` (or `α ∈ (0, 1]`) with `α * (α + n)^(n-1) = 1`
established in `N15IVTExistence` ... `N23N24IVTExistence`.

For n = 15..18 the underlying existence files export the strict-bound
versions (`α < 1`); for n = 19..22 only the weak-bound versions
(`α ≤ 1`) are exported, so we use those as published; for n = 23, 24
the files export the open-interval `Set.Ioo` form, which we include
verbatim. -/
theorem ivt_bundle_r69 :
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 15)^14 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 16)^15 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 17)^16 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 18)^17 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ α * (α + 19)^18 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ α * (α + 20)^19 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ α * (α + 21)^20 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ α * (α + 22)^21 = 1) ∧
    (∃ α ∈ Set.Ioo (0:ℝ) 1, α * (α + 23)^22 = 1) ∧
    (∃ α ∈ Set.Ioo (0:ℝ) 1, α * (α + 24)^23 = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact exists_alpha_n15_det_one
  · exact exists_alpha_n16_det_one
  · exact exists_alpha_n17_det_one
  · exact exists_alpha_n18_det_one
  · exact exists_alpha_n19_det_one_le
  · exact exists_alpha_n20_det_one_le
  · exact exists_alpha_n21_det_one_le
  · exact exists_alpha_n22_det_one_le
  · exact n23_ivt_existence
  · exact n24_ivt_existence

end PallLean.Paper93.DeepMath.PathB.Positroid
