import PallLean.Paper93.NFrame.PiStarExistence
import PallLean.Paper93.Substantive.NonTrivialRange
import PallLean.Paper93.Substantive.PiStarRankMonotone
import PallLean.Paper93.Substantive.RankUnderPiStar
import PallLean.MultilinearSPDP

/-!
# N-frame hypotheses for the constants projection

This file packages the substantive constants projection
`Substantive.nonTrivialGauge` against the N-frame hypothesis predicates from
`PiStarExistence`.

The statements are deliberately narrow:

* rank monotonicity is proved for the concrete multilinear SPDP rank functional;
* identity-minor preservation is proved only for the constant-one family;
* P-side collapse is proved with the same concrete rank functional and the
  explicit zero bound when the derivative order satisfies `1 ≤ κ`.
-/

namespace PallLean
namespace Paper93
namespace NFrame

open MvPolynomial

/-- The concrete rank functional used for the constants-projection packaging. -/
noncomputable def spdpRankFunctional {N : ℕ}
    (B : SPDP.BlockPartition N) (κ ℓ : ℕ) :
    MvPolynomial (Fin N) ℚ → ℕ :=
  fun p => MultilinearSPDP.mlBlockedSpdpRank B κ ℓ p

/-- The constant-one family used for the identity-minor preservation instance. -/
noncomputable def constantOneFamily (N : ℕ) : ℕ → MvPolynomial (Fin N) ℚ :=
  fun _ => 1

/-- `Substantive.nonTrivialGauge` is the same linear map as the existing
`Substantive.piStarConcrete` constants projection. -/
theorem nonTrivialGauge_projection_eq_piStarConcrete (N : ℕ) :
    (PallLean.Paper93.Substantive.nonTrivialGauge N).projection =
      PallLean.Paper93.Substantive.piStarConcrete N := by
  apply LinearMap.ext
  intro p
  change PallLean.Paper93.Substantive.toConstantsProjection N p =
    PallLean.Paper93.Substantive.piStarConcrete N p
  rw [PallLean.Paper93.Substantive.toConstantsProjection_apply]
  change MvPolynomial.coeff (0 : Fin N →₀ ℕ) p •
      (1 : MvPolynomial (Fin N) ℚ) =
    MvPolynomial.constantCoeff p • (1 : MvPolynomial (Fin N) ℚ)
  rw [MvPolynomial.constantCoeff_eq]

/-- The constants projection is admissible for the current N-frame skeleton. -/
theorem nonTrivialGauge_admissible (N : ℕ) :
    AdmissibleGauge (PallLean.Paper93.Substantive.nonTrivialGauge N) := by
  unfold AdmissibleGauge
  exact ⟨0, by simp⟩

/-- The constants projection fixes the constant polynomial `1`. -/
theorem nonTrivialGauge_projection_one (N : ℕ) :
    (PallLean.Paper93.Substantive.nonTrivialGauge N).projection
        (1 : MvPolynomial (Fin N) ℚ) =
      1 := by
  change PallLean.Paper93.Substantive.toConstantsProjection N
      (1 : MvPolynomial (Fin N) ℚ) = 1
  convert PallLean.Paper93.Substantive.toConstantsProjection_smul_one N 1 <;> simp

/-- Rank monotonicity for `Substantive.nonTrivialGauge` at the concrete
multilinear SPDP rank functional. -/
theorem nonTrivialGauge_rankMonotone_spdpRank
    {N : ℕ} (B : SPDP.BlockPartition N) (κ ℓ : ℕ) :
    RankMonotoneHypothesis (PallLean.Paper93.Substantive.nonTrivialGauge N)
      (spdpRankFunctional B κ ℓ) := by
  intro p
  unfold spdpRankFunctional
  rw [nonTrivialGauge_projection_eq_piStarConcrete N]
  exact PallLean.Paper93.Substantive.piStar_rank_monotone
    (N := N) (B := B) (κ := κ) (ℓ := ℓ) p

/-- Identity-minor preservation for the constant-one family. This is the
largest honest family-level nonvanishing statement available from the constants
projection alone. -/
theorem nonTrivialGauge_identityMinor_constantOne (N : ℕ) :
    IdentityMinorPreservationHypothesis
      (PallLean.Paper93.Substantive.nonTrivialGauge N)
      (constantOneFamily N) := by
  intro _k _hk
  rw [constantOneFamily, nonTrivialGauge_projection_one]
  exact one_ne_zero

/-- P-side collapse for `Substantive.nonTrivialGauge` at the concrete
multilinear SPDP rank functional, with explicit bound `0`, for derivative
order `κ ≥ 1`. -/
theorem nonTrivialGauge_pSideCollapse_spdpRank_zeroBound
    {N : ℕ} (B : SPDP.BlockPartition N) {κ ℓ : ℕ} (hκ : 1 ≤ κ)
    (family : ℕ → MvPolynomial (Fin N) ℚ) :
    PSideCollapseHypothesis (PallLean.Paper93.Substantive.nonTrivialGauge N)
      family (spdpRankFunctional B κ ℓ) := by
  refine ⟨fun _ => 0, ?_⟩
  intro k
  unfold spdpRankFunctional
  rw [nonTrivialGauge_projection_eq_piStarConcrete N]
  exact PallLean.Paper93.Substantive.piStar_rank_bounded
    (N := N) (B := B) (κ := κ) (ℓ := ℓ) (family k) hκ

/-- Bundle of all currently provable N-frame hypotheses for the constants
projection, specialised to the constant-one family and concrete SPDP rank. -/
theorem nonTrivialGauge_constantOne_hypotheses
    {N : ℕ} (B : SPDP.BlockPartition N) {κ ℓ : ℕ} (hκ : 1 ≤ κ) :
    AdmissibleGauge (PallLean.Paper93.Substantive.nonTrivialGauge N) ∧
      RankMonotoneHypothesis (PallLean.Paper93.Substantive.nonTrivialGauge N)
        (spdpRankFunctional B κ ℓ) ∧
      IdentityMinorPreservationHypothesis
        (PallLean.Paper93.Substantive.nonTrivialGauge N)
        (constantOneFamily N) ∧
      PSideCollapseHypothesis
        (PallLean.Paper93.Substantive.nonTrivialGauge N)
        (constantOneFamily N) (spdpRankFunctional B κ ℓ) := by
  refine ⟨nonTrivialGauge_admissible N,
    nonTrivialGauge_rankMonotone_spdpRank B κ ℓ,
    nonTrivialGauge_identityMinor_constantOne N,
    nonTrivialGauge_pSideCollapse_spdpRank_zeroBound B hκ
      (constantOneFamily N)⟩

#print axioms nonTrivialGauge_projection_eq_piStarConcrete
#print axioms nonTrivialGauge_admissible
#print axioms nonTrivialGauge_rankMonotone_spdpRank
#print axioms nonTrivialGauge_identityMinor_constantOne
#print axioms nonTrivialGauge_pSideCollapse_spdpRank_zeroBound
#print axioms nonTrivialGauge_constantOne_hypotheses

end NFrame
end Paper93
end PallLean
