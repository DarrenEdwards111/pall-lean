import PallLean.Paper93.NFrame.NontrivialIdentityMinorObstruction
import PallLean.Paper93.Substantive.NonTrivialRange

/-!
# Unit-preserving admissible gauges

The basic `AdmissibleGauge` predicate in the N-frame skeleton is too weak: the
zero projection is admissible and therefore wins the rank-only Lagrangian.  This
file records a concrete strengthening that is still inhabited by existing
kernel-only content.

The strengthened predicate requires the projection to fix the constant SPDP row
`1`.  This excludes the zero projection and gives a minimal identity-minor-style
nonvanishing condition without asserting the full paper God-Move gauge.
-/

namespace PallLean
namespace Paper93
namespace NFrame

open MvPolynomial

/-- A strengthened admissibility predicate: the gauge is admissible and fixes
the constant polynomial row. -/
def UnitPreservingAdmissibleGauge {N : ℕ} (gauge : CandidateGauge N) : Prop :=
  AdmissibleGauge gauge ∧
    gauge.projection (1 : MvPolynomial (Fin N) ℚ) = 1

/-- Unit-preserving admissibility rules out the zero linear map. -/
theorem unitPreserving_projection_ne_zero
    {N : ℕ} {gauge : CandidateGauge N}
    (h : UnitPreservingAdmissibleGauge gauge) :
    gauge.projection ≠ 0 := by
  intro hzero
  have hfix := h.2
  rw [hzero] at hfix
  exact (one_ne_zero (α := MvPolynomial (Fin N) ℚ)) hfix.symm

/-- Unit-preserving admissibility rules out zero range. -/
theorem unitPreserving_range_ne_bot
    {N : ℕ} {gauge : CandidateGauge N}
    (h : UnitPreservingAdmissibleGauge gauge) :
    LinearMap.range gauge.projection ≠ ⊥ := by
  intro hrange
  have hzero :
      gauge.projection (1 : MvPolynomial (Fin N) ℚ) = 0 :=
    projection_eq_zero_of_range_bot gauge hrange 1
  rw [h.2] at hzero
  exact (one_ne_zero (α := MvPolynomial (Fin N) ℚ)) hzero

/-- Unit-preserving admissible gauges have positive N-frame rank value. -/
theorem unitPreserving_lagrangianNat_pos
    {N : ℕ} {gauge : CandidateGauge N}
    (h : UnitPreservingAdmissibleGauge gauge) :
    0 < lagrangianNat gauge := by
  by_contra hnot
  have hfin : Module.finrank ℚ (LinearMap.range gauge.projection) = 0 := by
    exact Nat.eq_zero_of_not_pos hnot
  have _finiteRange : Module.Finite ℚ (LinearMap.range gauge.projection) :=
    gauge.rank_finite
  have hrange : LinearMap.range gauge.projection = ⊥ :=
    Submodule.finrank_eq_zero.mp hfin
  exact unitPreserving_range_ne_bot h hrange

/-- Unit-preserving admissibility gives identity-minor preservation for the
constant-one family. -/
theorem unitPreserving_identityMinor_constantOne
    {N : ℕ} {gauge : CandidateGauge N}
    (h : UnitPreservingAdmissibleGauge gauge) :
    IdentityMinorPreservationHypothesis gauge
      (fun _ : ℕ => (1 : MvPolynomial (Fin N) ℚ)) := by
  intro _k _hk
  rw [h.2]
  exact one_ne_zero

/-- The existing projection to constants is unit-preserving admissible. -/
theorem nonTrivialGauge_unitPreserving (N : ℕ) :
    UnitPreservingAdmissibleGauge
      (PallLean.Paper93.Substantive.nonTrivialGauge N) := by
  refine ⟨?_, ?_⟩
  · exact ⟨0, by simp⟩
  · change PallLean.Paper93.Substantive.toConstantsProjection N
        (1 : MvPolynomial (Fin N) ℚ) = 1
    simpa only [one_smul] using
      PallLean.Paper93.Substantive.toConstantsProjection_smul_one N 1

/-- The strengthened admissible set is inhabited by the existing projection to
the constants. -/
theorem unitPreservingAdmissible_nonempty (N : ℕ) :
    ∃ gauge : CandidateGauge N, UnitPreservingAdmissibleGauge gauge :=
  ⟨PallLean.Paper93.Substantive.nonTrivialGauge N,
    nonTrivialGauge_unitPreserving N⟩

/-- The concrete constants projection is not the zero projection. -/
theorem nonTrivialGauge_projection_ne_zero (N : ℕ) :
    (PallLean.Paper93.Substantive.nonTrivialGauge N).projection ≠ 0 :=
  unitPreserving_projection_ne_zero (nonTrivialGauge_unitPreserving N)

#print axioms unitPreserving_projection_ne_zero
#print axioms unitPreserving_range_ne_bot
#print axioms unitPreserving_lagrangianNat_pos
#print axioms unitPreserving_identityMinor_constantOne
#print axioms nonTrivialGauge_unitPreserving
#print axioms unitPreservingAdmissible_nonempty

end NFrame
end Paper93
end PallLean
