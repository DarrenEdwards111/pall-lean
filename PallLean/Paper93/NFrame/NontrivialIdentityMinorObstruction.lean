import PallLean.Paper93.NFrame.DischargeS2

/-!
# Nontrivial identity-minor obstruction for zero-range gauges

The current N-frame skeleton can minimize the Lagrangian at a projection with
zero range.  Such a projection gives the P-side collapse for free, but it cannot
preserve a nonzero identity-minor family.

This file packages that obstruction as reusable Lean theorems.  It does not
close the God-Move gauge construction; it rules out the degenerate minimizer as
soon as the NP-side family contains a nonzero element.
-/

namespace PallLean
namespace Paper93
namespace NFrame

open MvPolynomial

/-- A zero-range gauge maps every polynomial to zero. -/
theorem projection_eq_zero_of_range_bot
    {N : ℕ} (Pi : CandidateGauge N)
    (hrange : LinearMap.range Pi.projection = ⊥)
    (p : MvPolynomial (Fin N) ℚ) :
    Pi.projection p = 0 := by
  have hmem : Pi.projection p ∈ LinearMap.range Pi.projection :=
    LinearMap.mem_range_self _ p
  rw [hrange] at hmem
  exact (Submodule.mem_bot ℚ).mp hmem

/-- A zero-range gauge cannot preserve identity-minor nonvanishing for any
family containing a nonzero member. -/
theorem not_identityMinorPreservationHypothesis_of_range_bot_of_nonzero_family
    {N : ℕ} (Pi : CandidateGauge N)
    (family : ℕ → MvPolynomial (Fin N) ℚ)
    (hrange : LinearMap.range Pi.projection = ⊥)
    (hfamily : ∃ k : ℕ, family k ≠ 0) :
    ¬ IdentityMinorPreservationHypothesis Pi family := by
  intro hpres
  obtain ⟨k, hk⟩ := hfamily
  exact hpres k hk (projection_eq_zero_of_range_bot Pi hrange (family k))

/-- The trivial gauge cannot preserve identity-minor nonvanishing for a
nonzero family. -/
theorem not_identityMinorPreservationHypothesis_trivialGauge_of_nonzero_family
    {N : ℕ} (family : ℕ → MvPolynomial (Fin N) ℚ)
    (hfamily : ∃ k : ℕ, family k ≠ 0) :
    ¬ IdentityMinorPreservationHypothesis (trivialGauge N) family := by
  apply not_identityMinorPreservationHypothesis_of_range_bot_of_nonzero_family
  · ext p
    simp [trivialGauge]
  · exact hfamily

/-- If a zero-range minimizer satisfies identity-minor preservation, then the
family must be identically zero. -/
theorem family_eq_zero_of_range_bot_identityMinorPreservation
    {N : ℕ} (Pi : CandidateGauge N)
    (family : ℕ → MvPolynomial (Fin N) ℚ)
    (hrange : LinearMap.range Pi.projection = ⊥)
    (hpres : IdentityMinorPreservationHypothesis Pi family)
    (k : ℕ) :
    family k = 0 := by
  by_contra hk
  exact hpres k hk (projection_eq_zero_of_range_bot Pi hrange (family k))

#print axioms projection_eq_zero_of_range_bot
#print axioms not_identityMinorPreservationHypothesis_of_range_bot_of_nonzero_family
#print axioms not_identityMinorPreservationHypothesis_trivialGauge_of_nonzero_family
#print axioms family_eq_zero_of_range_bot_identityMinorPreservation

end NFrame
end Paper93
end PallLean
