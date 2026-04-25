import PallLean.Paper93.Paper283.RouteBStrictMatrixCertificate

/-!
# Route B automatic eigenvalue norm bound

This file removes one more non-structural datum from the strict Route B
matrix certificate.  For a positive semidefinite matrix, every eigenvalue is
nonnegative, so each eigenvalue is bounded by

`1 + sum_i eigenvalue_i`.

This is a finite-dimensional bound.  It is not the final spectral theorem, and
it does not use any keepFOB/profile-collapse/Route-A adapter input.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open TuringMachine
open PaperFaithfulSeparation
open PallLean.Paper93.DeepMath.PathB

/-- A canonical finite upper bound for the PSD eigenvalues used by Route B.

The extra `1` makes the bound strictly positive even in the zero-dimensional
or zero-matrix cases. -/
noncomputable def routeBEigenvalueSumNormBound {N : Nat}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef) : Real :=
  1 + ∑ i, hA.1.eigenvalues i

/-- The canonical finite PSD eigenvalue bound is positive. -/
theorem routeBEigenvalueSumNormBound_pos {N : Nat}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef) :
    0 < routeBEigenvalueSumNormBound A hA := by
  have hsum_nonneg : 0 ≤ ∑ i, hA.1.eigenvalues i := by
    exact Finset.sum_nonneg
      (fun i _ => posSemidef_eigenvalues_nonneg A hA i)
  unfold routeBEigenvalueSumNormBound
  linarith

/-- Every PSD eigenvalue is bounded by the canonical finite sum bound. -/
theorem eigenvalues_le_routeBEigenvalueSumNormBound {N : Nat}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef) :
    ∀ i, hA.1.eigenvalues i <= routeBEigenvalueSumNormBound A hA := by
  intro i
  have hle_sum :
      hA.1.eigenvalues i <= ∑ j, hA.1.eigenvalues j := by
    exact Finset.single_le_sum
      (f := fun j => hA.1.eigenvalues j)
      (fun j _ => posSemidef_eigenvalues_nonneg A hA j)
      (Finset.mem_univ i)
  unfold routeBEigenvalueSumNormBound
  linarith

/-- Bridge B spectral hypotheses with both shifted positive-definiteness and
the finite eigenvalue norm bound discharged from PSD data. -/
theorem bridgeB_spectral_hypotheses_of_posSemidef_with_auto_shiftPosDef_autoNormBound
    {N : Nat} {theta : Real}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (htheta : 0 < theta)
    (hshift_eigenvalues_eq_one_add_theta_mul :
      ∀ i,
        (one_add_smul_posSemidef_posDef_of_pos A hA htheta).1.eigenvalues i =
          1 + theta * hA.1.eigenvalues i) :
    BridgeBSpectralHypotheses theta (routeBEigenvalueSumNormBound A hA)
      (Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det))
      A.rank hA.1.eigenvalues := by
  exact
    bridgeB_spectral_hypotheses_of_posSemidef_with_auto_shiftPosDef
      (theta := theta) (normBound := routeBEigenvalueSumNormBound A hA)
      A hA htheta hshift_eigenvalues_eq_one_add_theta_mul
      (eigenvalues_le_routeBEigenvalueSumNormBound A hA)

/-- Bridge B rank lower bound with shifted positive-definiteness and the
finite eigenvalue norm bound discharged from PSD data. -/
theorem bridgeB_rank_lower_of_posSemidef_with_auto_shiftPosDef_autoNormBound
    {N : Nat} {theta delta : Real}
    {activeCard : Nat}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (htheta : 0 < theta)
    (hshift_eigenvalues_eq_one_add_theta_mul :
      ∀ i,
        (one_add_smul_posSemidef_posDef_of_pos A hA htheta).1.eigenvalues i =
          1 + theta * hA.1.eigenvalues i)
    (hlower :
      delta * (activeCard : Real) <=
        Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det)) :
    (delta / bridgeBLogCapacity theta (routeBEigenvalueSumNormBound A hA)) *
        (activeCard : Real) <= (A.rank : Real) := by
  exact
    bridgeB_rank_lower_of_posSemidef_with_auto_shiftPosDef
      (theta := theta) (normBound := routeBEigenvalueSumNormBound A hA)
      (delta := delta) (activeCard := activeCard)
      A hA htheta (routeBEigenvalueSumNormBound_pos A hA)
      hshift_eigenvalues_eq_one_add_theta_mul
      (eigenvalues_le_routeBEigenvalueSumNormBound A hA)
      hlower

/-- Strict Route B matrix certificate with the eigenvalue norm bound derived
from PSD data rather than supplied as a separate field. -/
def RouteBStrictAutoNormMatrixCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (N d : Nat)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (theta delta rankLogRate : Real)
    (A : Matrix (Fin N) (Fin N) Real)
    (hA : A.PosSemidef)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)),
    ∃ htheta : 0 < theta,
      0 < alpha ∧ 0 < alpha0 ∧ 2 <= gadgetN ∧
      (∀ i,
        (one_add_smul_posSemidef_posDef_of_pos A hA htheta).1.eigenvalues i =
          1 + theta * hA.1.eigenvalues i) ∧
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        rankLogRate
        (Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det))
        delta ∧
      PallLean.Paper93.NFrame.AdmissibleGauge Pi ∧
      RouteBProjectionRankCompatible M n hn2 htb hns A.rank Pi ∧
      RouteBMatrixToSATGaugeFunctoriality
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        (bridgeBLogCapacity theta (routeBEigenvalueSumNormBound A hA))
        delta A.rank Pi

/-- Auto-norm Route B matrix certificates supply strict matrix certificates. -/
theorem routeBStrictMatrixCertificate_of_autoNormMatrixCertificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (cert : RouteBStrictAutoNormMatrixCertificate M n hn2 htb hns) :
    RouteBStrictMatrixCertificate M n hn2 htb hns := by
  rcases cert with
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, delta, rankLogRate, A, hA, Pi,
      htheta, halpha, halpha0, hgadgetN,
      hshift_eigs, hlower, hAdm, hcompat, hfun⟩
  exact
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, routeBEigenvalueSumNormBound A hA, delta, rankLogRate,
      A, hA, Pi,
      htheta, halpha, halpha0, hgadgetN,
      routeBEigenvalueSumNormBound_pos A hA,
      hshift_eigs,
      eigenvalues_le_routeBEigenvalueSumNormBound A hA,
      hlower, hAdm, hcompat, hfun⟩

/-- Auto-norm matrix certificates supply the generic Route B per-instance
certificate. -/
theorem routeBPerInstanceCertificate_of_autoNormMatrixCertificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (cert : RouteBStrictAutoNormMatrixCertificate M n hn2 htb hns) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_strictMatrixCertificate
    (routeBStrictMatrixCertificate_of_autoNormMatrixCertificate cert)

/-- Auto-norm matrix certificate form of the per-instance rich-projection
target. -/
theorem cookLevinRichProjectionTarget_of_autoNormMatrixCertificate
    {M : DTM} {n : Nat} {hn : n ≥ 2 ^ 804} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (cert : RouteBStrictAutoNormMatrixCertificate M n hn2 htb hns) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_strictMatrixCertificate
    (routeBStrictMatrixCertificate_of_autoNormMatrixCertificate cert)

/-- Uniform auto-norm Route B certificates discharge the rich-projection
frontier. -/
theorem cookLevinRichProjectionDischarge_of_autoNormMatrixCertificates
    (hcert :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        RouteBStrictAutoNormMatrixCertificate M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_of_strictMatrixCertificates
    (fun M n hn hn2 htb hns hdec =>
      routeBStrictMatrixCertificate_of_autoNormMatrixCertificate
        (hcert M n hn hn2 htb hns hdec))

/-- Contradiction-strength endpoint from uniform auto-norm Route B matrix
certificates. -/
theorem noBoundedSATDeciderAtPaperScale_of_autoNormMatrixCertificates
    (hcert :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        RouteBStrictAutoNormMatrixCertificate M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_strictMatrixCertificates
    (fun M n hn hn2 htb hns hdec =>
      routeBStrictMatrixCertificate_of_autoNormMatrixCertificate
        (hcert M n hn hn2 htb hns hdec))

/-! ## Axiom audit anchors -/

#print axioms routeBEigenvalueSumNormBound_pos
#print axioms eigenvalues_le_routeBEigenvalueSumNormBound
#print axioms bridgeB_spectral_hypotheses_of_posSemidef_with_auto_shiftPosDef_autoNormBound
#print axioms bridgeB_rank_lower_of_posSemidef_with_auto_shiftPosDef_autoNormBound
#print axioms routeBStrictMatrixCertificate_of_autoNormMatrixCertificate
#print axioms routeBPerInstanceCertificate_of_autoNormMatrixCertificate
#print axioms cookLevinRichProjectionTarget_of_autoNormMatrixCertificate
#print axioms cookLevinRichProjectionDischarge_of_autoNormMatrixCertificates
#print axioms noBoundedSATDeciderAtPaperScale_of_autoNormMatrixCertificates

end PallLean.Paper93.Paper283
