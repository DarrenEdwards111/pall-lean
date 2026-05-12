import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.StarOrdered

/-!
# Gauge normalization under scaling

This file proves how the amplituhedron gauge property
(`IsAmplituhedronGauge`) interacts with scalar multiplication.

## Main results

* `isAmplituhedronGauge_empty_family_iff`: for the empty family `(∅)`, the
  gauge property reduces to positive definiteness.
* `PosDef.smul_pos`: positive scaling preserves positive definiteness.
* `smul_isAmplituhedronGauge_empty`: for any PosDef `A` and `c > 0`,
  `c • A` is a gauge for the empty family.
* `cI_isAmplituhedronGauge_empty`: in particular, `c • (1 : Matrix _ _ ℝ)`
  is a gauge for the empty family for every `c > 0`.

## Mathematical content

For `c > 0` and a gauge `A` (PosDef + unit principal minors at `𝒥`), the
matrix `c • A` is positive definite, but its principal minors at `J ∈ 𝒥`
are scaled by `c ^ (J.card)`. So `c • A` is a gauge for `𝒥` only when
`c = 1`, *or* for trivial families like `{∅}` (which we capture here via
the empty family).

Diagonal scalings `D • A • D` with `D` positive-diagonal can preserve the
gauge property for the empty family by the same argument: PosDef is
preserved and the family imposes no minor constraints.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB

/-- The empty family `(∅ : Finset (Finset (Fin n)))` admits any PosDef matrix as gauge. -/
theorem isAmplituhedronGauge_empty_family_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    IsAmplituhedronGauge A (∅ : Finset (Finset (Fin n))) ↔ A.PosDef := by
  unfold IsAmplituhedronGauge
  constructor
  · intro ⟨h, _⟩; exact h
  · intro h
    refine ⟨h, ?_⟩
    intro J hJ
    exact absurd hJ (Finset.notMem_empty J)

/-- For `c > 0`, scaling preserves positive definiteness. -/
theorem PosDef.smul_pos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {c : ℝ} (hc : 0 < c) :
    (c • A).PosDef := by
  exact hA.smul hc

/-- For any PosDef matrix `A` and `c > 0`, `c • A` is a gauge for the empty family. -/
theorem smul_isAmplituhedronGauge_empty {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {c : ℝ} (hc : 0 < c) :
    IsAmplituhedronGauge (c • A) (∅ : Finset (Finset (Fin n))) := by
  rw [isAmplituhedronGauge_empty_family_iff]
  exact PosDef.smul_pos hA hc

/-- For any positive `c`, `c • (1 : Matrix _ _ ℝ) = c • I` is a gauge for the
    empty family. -/
theorem cI_isAmplituhedronGauge_empty {n : ℕ} (c : ℝ) (hc : 0 < c) :
    IsAmplituhedronGauge (c • (1 : Matrix (Fin n) (Fin n) ℝ)) ∅ := by
  apply smul_isAmplituhedronGauge_empty
  · exact Matrix.PosDef.one
  · exact hc

end PallLean.Paper93.DeepMath.PathB.Positroid
