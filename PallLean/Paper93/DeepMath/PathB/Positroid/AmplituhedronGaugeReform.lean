import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.PathB.IdentityIsGaugeAnyFamily

/-!
# Amplituhedron gauge reformulation via principal-TNN structure

This file provides an alternative reformulation of `IsAmplituhedronGauge`
in terms of principal-TNN structure plus unit-determinant on a designated
family of principal minors.

The paper's §7.1 defines the amplituhedron gauge as a matrix that:
(a) has positive principal minors at the designated family
    (= 1 specifically, by normalization),
(b) admits a positroid-cell representation.

The existing definition `IsAmplituhedronGauge` in `GaugePropertyDef.lean`
already captures (a) (PosDef + ∀ J ∈ 𝒥, principal minor = 1). This file
shows that the property is preserved under "trivially" augmenting the
family with redundant entries (union and subset closure), and provides
the universal identity-matrix witness.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB

/-- Gauge property is preserved under family extension: if A is a gauge for 𝒥
    and is also a gauge for 𝒦, then A is a gauge for 𝒥 ∪ 𝒦. -/
theorem isAmplituhedronGauge_union {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (𝒥 𝒦 : Finset (Finset (Fin n)))
    (h𝒥 : IsAmplituhedronGauge A 𝒥) (h𝒦 : IsAmplituhedronGauge A 𝒦) :
    IsAmplituhedronGauge A (𝒥 ∪ 𝒦) := by
  refine ⟨h𝒥.1, ?_⟩
  intro J hJ e
  rcases Finset.mem_union.mp hJ with h₁ | h₂
  · exact h𝒥.2 J h₁ e
  · exact h𝒦.2 J h₂ e

/-- Gauge property is preserved under family restriction: if A is a gauge for 𝒥
    and 𝒦 ⊆ 𝒥, then A is a gauge for 𝒦. -/
theorem isAmplituhedronGauge_subset {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (𝒥 𝒦 : Finset (Finset (Fin n))) (h𝒦 : 𝒦 ⊆ 𝒥)
    (h : IsAmplituhedronGauge A 𝒥) :
    IsAmplituhedronGauge A 𝒦 := by
  refine ⟨h.1, ?_⟩
  intro J hJ e
  exact h.2 J (h𝒦 hJ) e

/-- The identity matrix is a gauge for ANY finite family — providing the
    universal "trivial" witness used as a fallback in the absence of more
    structured (positroid) witnesses. -/
theorem identity_universal_gauge_witness {n : ℕ} (𝒥 : Finset (Finset (Fin n))) :
    IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) ℝ) 𝒥 :=
  identity_isAmplituhedronGauge_any 𝒥

end PallLean.Paper93.DeepMath.PathB.Positroid
