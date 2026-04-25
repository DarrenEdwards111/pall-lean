import PallLean.Paper93.DeepMath.PathB.Positroid.N3IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N4IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N5IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N6IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N7IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N8IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N9IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N10IVTExistence

/-!
# Round 64 IVT existence bundle for `n = 3, …, 10`

This file bundles the eight IVT-based existence theorems for the
§28.3 gauge condition at `n = 3, 4, 5, 6, 7, 8, 9, 10` into a single
conjunction, yielding a kernel-only existence statement covering all
eight cases.

The constituent theorems are:

* `exists_alpha_n3_det_one`: `∃ α ∈ (0, 1), α (α + 3)² = 1`.
* `exists_alpha_n4_det_one`: `∃ α ∈ (0, 1), α (α + 4)³ = 1`.
* `exists_alpha_n5_det_one`: `∃ α ∈ (0, 1), α (α + 5)⁴ = 1`.
* `exists_alpha_n6_det_one`: `∃ α ∈ (0, 1), α (α + 6)⁵ = 1`.
* `exists_alpha_n7_det_one`: `∃ α ∈ (0, 1), α (α + 7)⁶ = 1`.
* `exists_alpha_n8_det_one`: `∃ α ∈ (0, 1), α (α + 8)⁷ = 1`.
* `exists_alpha_n9_det_one`: `∃ α ∈ (0, 1), α (α + 9)⁸ = 1`.
* `exists_alpha_n10_det_one`: `∃ α ∈ (0, 1), α (α + 10)⁹ = 1`.

The bundled statement `ivt_bundle_r64_n3_to_n10` pairs these eight
existence results via the anonymous constructor, producing a
kernel-only conjunction whose proof reduces to the eight component
theorems.

All results are kernel-only (axioms: `propext`, `Classical.choice`,
`Quot.sound`).

Namespace: `PallLean.Paper93.DeepMath.PathB.Positroid`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- **Round 64 IVT existence bundle for `n = 3, …, 10`**: there exist
positive reals `α₃, α₄, α₅, α₆, α₇, α₈, α₉, α₁₀ ∈ (0, 1)` solving the
§28.3 gauge condition at the corresponding `n`, namely

* `α₃ (α₃ + 3)² = 1`,
* `α₄ (α₄ + 4)³ = 1`,
* `α₅ (α₅ + 5)⁴ = 1`,
* `α₆ (α₆ + 6)⁵ = 1`,
* `α₇ (α₇ + 7)⁶ = 1`,
* `α₈ (α₈ + 8)⁷ = 1`,
* `α₉ (α₉ + 9)⁸ = 1`,
* `α₁₀ (α₁₀ + 10)⁹ = 1`.

The proof is the anonymous constructor applied to the eight
component existence theorems. -/
theorem ivt_bundle_r64_n3_to_n10 :
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 3)^2 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 4)^3 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 5)^4 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 6)^5 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 7)^6 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 8)^7 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 9)^8 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 10)^9 = 1) :=
  ⟨exists_alpha_n3_det_one, exists_alpha_n4_det_one, exists_alpha_n5_det_one,
   exists_alpha_n6_det_one, exists_alpha_n7_det_one, exists_alpha_n8_det_one,
   exists_alpha_n9_det_one, exists_alpha_n10_det_one⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
