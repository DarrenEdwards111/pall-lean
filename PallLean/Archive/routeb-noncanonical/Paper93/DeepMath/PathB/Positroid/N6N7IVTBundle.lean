import PallLean.Paper93.DeepMath.PathB.Positroid.N6IVTExistence
import PallLean.Paper93.DeepMath.PathB.Positroid.N7IVTExistence

/-!
# Bundle of `n = 6` and `n = 7` IVT existence results

This file bundles the two IVT-based existence theorems for the
§28.3 gauge condition at `n = 6` and `n = 7` into a single
conjunction:

* `exists_alpha_n6_det_one`: existence of `α ∈ (0, 1)` with
  `α (α + 6)⁵ = 1`.
* `exists_alpha_n7_det_one`: existence of `α ∈ (0, 1)` with
  `α (α + 7)⁶ = 1`.

The bundled statement `exists_alpha_n6_and_n7` simply pairs these
two existence results, yielding a kernel-only conjunction whose
proof is the explicit anonymous constructor applied to the two
underlying theorems.

All results are kernel-only (axioms: `propext`, `Classical.choice`,
`Quot.sound`).

Namespace: `PallLean.Paper93.DeepMath.PathB.Positroid`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- **Bundled `n = 6` and `n = 7` IVT existence**: there exist
positive reals `α₆, α₇ ∈ (0, 1)` solving the §28.3 gauge condition
at `n = 6` and `n = 7`, namely

* `α₆ (α₆ + 6)⁵ = 1`,
* `α₇ (α₇ + 7)⁶ = 1`.

The proof is the anonymous constructor applied to
`exists_alpha_n6_det_one` and `exists_alpha_n7_det_one`. -/
theorem exists_alpha_n6_and_n7 :
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 6)^5 = 1) ∧
    (∃ α : ℝ, 0 < α ∧ α < 1 ∧ α * (α + 7)^6 = 1) :=
  ⟨exists_alpha_n6_det_one, exists_alpha_n7_det_one⟩

end PallLean.Paper93.DeepMath.PathB.Positroid
