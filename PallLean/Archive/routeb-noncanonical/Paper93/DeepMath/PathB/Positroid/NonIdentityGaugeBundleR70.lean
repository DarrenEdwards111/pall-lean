import PallLean.Paper93.DeepMath.PathB.CompiledGadgetN2SatGauge
import PallLean.Paper93.DeepMath.PathB.Positroid.NonIdentityGaugeN6
import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.PathB.SatFamilyDefinition
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Round-70 bundle: non-identity amplituhedron gauge witnesses

This kernel-only file bundles the currently provable non-identity
amplituhedron gauge existence statements for the truncated SAT family
into a single round-70 theorem. At present the bundle covers the cases
`n = 2` and `n = 6` — the two `n` values for which the Path B
infrastructure has produced a kernel-only certified non-identity
witness via the §28.3 compiled gadget at an explicit / IVT-supplied
positive coupling.

Concretely, `nonIdentity_gauge_bundle_r70` packages:

* **`n = 2`** (`compiledGadget (√2 − 1) 2`):
  * `IsAmplituhedronGauge A (satFamily 2)` from
    `compiledGadget_n2_isGauge_satFamily`.
  * `A ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)` because the off-diagonal
    `(0,1)` entry is `−1` (independent of `α`), repackaged from
    `nontrivial_gauge_exists_n2`.

* **`n = 6`** (`compiledGadget α 6` at the IVT-supplied root of
  `α(α + 6)^5 = 1`):
  * `IsAmplituhedronGauge A (satFamily 6)` and
    `A ≠ (1 : Matrix (Fin 6) (Fin 6) ℝ)` from `nonIdentity_gauge_n6`.

The `n = 5` conjunct is **omitted** here: the supporting
`NonIdentityGaugeN5.lean` file is present on disk but has not yet been
committed at the time of this bundle. Once committed, an extension of
this bundle (or a successor round-71 bundle) will fold it in alongside
`n = 2` and `n = 6`.

Kernel-only: only `propext`, `Classical.choice`, `Quot.sound` are
introduced.

Namespace: `PallLean.Paper93.DeepMath.PathB.Positroid`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank

/-- **Round-70 bundle of non-identity amplituhedron gauge witnesses.**

Combines the kernel-only Path B non-identity gauge existence theorems
for `satFamily n` at the cases `n = 2` and `n = 6` into a single
conjunction:

  * `n = 2`: there exists a `2 × 2` real matrix `A` which is an
    amplituhedron gauge for `satFamily 2` and is not the identity.
    The witness is `compiledGadget (√2 − 1) 2`, certified by
    `nontrivial_gauge_exists_n2` (combining
    `compiledGadget_n2_isGauge_satFamily` with the off-diagonal
    `(0,1)` entry computation).

  * `n = 6`: there exists a `6 × 6` real matrix `A` which is an
    amplituhedron gauge for `satFamily 6` and is not the identity.
    The witness is `compiledGadget α 6` at the IVT-supplied root
    `α ∈ (0, 1)` of `α (α + 6)^5 = 1`, certified by
    `nonIdentity_gauge_n6`.

This is the round-70 packaging of the §7.1 non-identity gauge
existence question at the truncated level: at both `n = 2` and `n = 6`
the §28.3 compiled gadget furnishes a non-trivial gauge for the SAT
family, refuting any reading of the §7.1 axiom that would force the
witness to be the identity matrix.

The `n = 5` slot is presently omitted; see the file docstring. -/
theorem nonIdentity_gauge_bundle_r70 :
    (∃ A : Matrix (Fin 2) (Fin 2) ℝ,
        IsAmplituhedronGauge A (satFamily 2) ∧
          A ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (∃ A : Matrix (Fin 6) (Fin 6) ℝ,
        IsAmplituhedronGauge A (satFamily 6) ∧
          A ≠ (1 : Matrix (Fin 6) (Fin 6) ℝ)) := by
  refine ⟨?_, ?_⟩
  · -- n = 2 conjunct: extract from `nontrivial_gauge_exists_n2`.
    obtain ⟨α, _hα_pos, hGauge, hNeI⟩ := nontrivial_gauge_exists_n2
    exact ⟨compiledGadget α 2, hGauge, hNeI⟩
  · -- n = 6 conjunct: this is exactly `nonIdentity_gauge_n6`.
    exact nonIdentity_gauge_n6

end PallLean.Paper93.DeepMath.PathB.Positroid
