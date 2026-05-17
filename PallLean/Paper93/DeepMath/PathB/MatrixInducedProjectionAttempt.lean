import PallLean.Paper93.DeepMath.PathB.GodMoveLift
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeMapPiPhi
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeNPBridge
import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeIdentityObstructions

/-!
# First concrete matrix-induced projection attempt

The matrix-level variational route produces `IsAmplituhedronGauge A 𝒥`, but the
final GodMove compressor lives on the Cook--Levin polynomial space.  This file
makes the first honest attempt at an induced polynomial projection using the
only currently available concrete polynomial projection in the codebase:
`satDeciderGaugeMapPiPhi`.

Outcome: the map is kernel-clean and rank-monotone, and it preserves the NP
identity-minor lower bound.  But the flat Cook--Levin specialization is the
identity map, so it cannot satisfy the P-side collapse field at paper scale.
This is useful: it proves that the real GodMove compressor must be a genuinely
new non-flat/non-identity projection, not merely the current matrix gauge
wrapped around `piPhi`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine

/-- First concrete attempt at turning a matrix amplituhedron gauge into a
polynomial-space SAT-decider gauge: use the existing flat `piPhi` projection.

The arguments `A` and `𝒥` are retained in the signature because this is the
correct bridge shape.  The definition deliberately ignores them: this captures
that the current codebase has no nontrivial action of matrix amplituhedron data
on Cook--Levin polynomial variables yet. -/
noncomputable def matrixGaugeToPolynomialProjectionPiPhi
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_A : Matrix (Fin n) (Fin n) ℝ)
    (_𝒥 : Finset (Finset (Fin n))) :
    SATDeciderGaugeMap M n hn2 htb hns :=
  satDeciderGaugeMapPiPhi M n hn2 htb hns

/-- The current matrix-induced attempt is definitionally the flat `piPhi`
candidate. -/
theorem matrixGaugeToPolynomialProjectionPiPhi_eq_piPhi
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (𝒥 : Finset (Finset (Fin n))) :
    matrixGaugeToPolynomialProjectionPiPhi M n hn2 htb hns A 𝒥 =
      satDeciderGaugeMapPiPhi M n hn2 htb hns := rfl

/-- Consequently, in the flat Cook--Levin specialization this induced attempt is
just the identity map. -/
theorem matrixGaugeToPolynomialProjectionPiPhi_eq_id
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (𝒥 : Finset (Finset (Fin n))) :
    matrixGaugeToPolynomialProjectionPiPhi M n hn2 htb hns A 𝒥 = LinearMap.id := by
  rw [matrixGaugeToPolynomialProjectionPiPhi_eq_piPhi]
  exact satDeciderGaugeMapPiPhi_eq_id M n hn2 htb hns

/-- The flat matrix-induced attempt is rank-monotone. -/
theorem matrixGaugeToPolynomialProjectionPiPhi_rankMonotonicity
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (𝒥 : Finset (Finset (Fin n))) :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns
      (matrixGaugeToPolynomialProjectionPiPhi M n hn2 htb hns A 𝒥) := by
  rw [matrixGaugeToPolynomialProjectionPiPhi_eq_piPhi]
  exact satDeciderGaugeMapPiPhi_rankMonotonicity M n hn2 htb hns

/-- At paper scale, the flat matrix-induced attempt preserves the NP
identity-minor lower bound. -/
theorem matrixGaugeToPolynomialProjectionPiPhi_npIdentityMinorPreservation
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (𝒥 : Finset (Finset (Fin n))) :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
      (matrixGaugeToPolynomialProjectionPiPhi M n hn2 htb hns A 𝒥) := by
  rw [matrixGaugeToPolynomialProjectionPiPhi_eq_id]
  exact satDeciderGaugeNPIdentityMinorPreservation_id M n hn hn2 htb hns

/-- But at paper scale this flat induced attempt cannot satisfy the P-side
collapse field.  It is the identity map, so the existing NP lower bound and
arithmetic gap obstruct `≤ n^200`. -/
theorem matrixGaugeToPolynomialProjectionPiPhi_not_pSideBound_at_large_n
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (𝒥 : Finset (Finset (Fin n))) :
    ¬ SATDeciderGaugePSideBound M n hn2 htb hns
      (matrixGaugeToPolynomialProjectionPiPhi M n hn2 htb hns A 𝒥) := by
  rw [matrixGaugeToPolynomialProjectionPiPhi_eq_id]
  exact identitySATDeciderGauge_not_pSideBound_at_large_n M n hn hn2 htb hns

/-- Therefore the flat matrix-induced attempt cannot realize the full GodMove
compressor fields for a SAT decider at paper scale. -/
theorem not_matrixGaugeRealizesSATGauge_piPhi_at_large_n
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (𝒥 : Finset (Finset (Fin n))) :
    ¬ MatrixGaugeRealizesSATGauge M n hn hn2 htb hns A 𝒥
      (matrixGaugeToPolynomialProjectionPiPhi M n hn2 htb hns A 𝒥) := by
  intro hrealizes
  exact matrixGaugeToPolynomialProjectionPiPhi_not_pSideBound_at_large_n
    M n hn hn2 htb hns A 𝒥 hrealizes.p_side_bound

/-- The exact missing non-flat construction interface: a matrix gauge must
produce a polynomial projection satisfying the two fields that the flat `piPhi`
attempt cannot combine with NP preservation.  Rank monotonicity is separated
because it already follows for projection-style maps. -/
def NonflatMatrixPolynomialProjectionRealization
    (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (𝒥 : Finset (Finset (Fin n))) : Prop :=
  IsAmplituhedronGauge A 𝒥 ∧
    ∃ gauge : SATDeciderGaugeMap M n hn2 htb hns,
      gauge ≠ matrixGaugeToPolynomialProjectionPiPhi M n hn2 htb hns A 𝒥 ∧
      SATDeciderGaugeRankMonotonicity M n hn2 htb hns gauge ∧
      SATDeciderGaugePSideBound M n hn2 htb hns gauge ∧
      SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns gauge

/-- A non-flat realization immediately supplies the existing matrix-to-global
realization package. -/
theorem matrixGaugeRealizesSATGauge_of_nonflatRealization
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (𝒥 : Finset (Finset (Fin n)))
    (h : NonflatMatrixPolynomialProjectionRealization M n hn hn2 htb hns A 𝒥) :
    ∃ gauge : SATDeciderGaugeMap M n hn2 htb hns,
      MatrixGaugeRealizesSATGauge M n hn hn2 htb hns A 𝒥 gauge := by
  rcases h with ⟨hmatrix, gauge, _hne_flat, hrank, hp, hnp⟩
  exact ⟨gauge,
    { matrix_gauge := hmatrix
      rank_monotone := hrank
      p_side_bound := hp
      preserves_identity_minor := hnp }⟩

/-! ## Axiom audit anchors -/
#print axioms matrixGaugeToPolynomialProjectionPiPhi_eq_piPhi
#print axioms matrixGaugeToPolynomialProjectionPiPhi_eq_id
#print axioms matrixGaugeToPolynomialProjectionPiPhi_rankMonotonicity
#print axioms matrixGaugeToPolynomialProjectionPiPhi_npIdentityMinorPreservation
#print axioms matrixGaugeToPolynomialProjectionPiPhi_not_pSideBound_at_large_n
#print axioms not_matrixGaugeRealizesSATGauge_piPhi_at_large_n
#print axioms matrixGaugeRealizesSATGauge_of_nonflatRealization

end PallLean.Paper93.DeepMath.PathB
