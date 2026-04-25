import PallLean.Paper93.Paper283.RouteBEigenvalueNormBound
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# Route B shifted eigenvalue composition via functional calculus

The remaining Bridge B spectral-composition input is the affine shifted
eigenvalue identity

`eigenvalues(I + theta A) = 1 + theta * eigenvalues(A)`.

Mathlib's Hermitian functional calculus gives the right route: for a Hermitian
matrix `A`, `cfc (fun x => 1 + theta * x) A` has characteristic polynomial
with roots `1 + theta * eigenvalues(A)`.  This file packages that route into
the active Route B certificate vocabulary without importing any SAT/profile
adapter content.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open TuringMachine
open PaperFaithfulSeparation
open PallLean.Paper93.DeepMath.PathB

/-- Witnessed shifted eigenvalue composition statement. -/
def BridgeBShiftedEigenvalueCompositionOfPos {N : Nat}
    (theta : Real) (A : Matrix (Fin N) (Fin N) Real)
    (hA : A.PosSemidef) (htheta : 0 < theta) : Prop :=
  ∀ i,
    (one_add_smul_posSemidef_posDef_of_pos A hA htheta).1.eigenvalues i =
      1 + theta * hA.1.eigenvalues i

/-- The Hermitian functional-calculus characteristic-polynomial target for
the affine shift `x ↦ 1 + theta * x`. -/
theorem bridgeB_affine_cfc_charpoly {N : Nat}
    (theta : Real) (A : Matrix (Fin N) (Fin N) Real)
    (hA : A.PosSemidef) :
    (cfc (fun x : Real => 1 + theta * x) A).charpoly =
      ∏ i, (Polynomial.X -
        Polynomial.C ((1 + theta * hA.1.eigenvalues i) : Real)) := by
  simpa using
      (Matrix.IsHermitian.charpoly_cfc_eq
      (A := A) (𝕜 := Real) hA.1 (fun x : Real => 1 + theta * x))

/-- The matrix-level affine CFC identity for the Bridge B shift. -/
theorem bridgeB_affine_cfc_eq_shift {N : Nat}
    (theta : Real) (A : Matrix (Fin N) (Fin N) Real)
    (hA : A.PosSemidef) :
    cfc (fun x : Real => 1 + theta * x) A =
      (1 : Matrix (Fin N) (Fin N) Real) + theta • A := by
  calc
    cfc (fun x : Real => 1 + theta * x) A
        =
        (algebraMap Real (Matrix (Fin N) (Fin N) Real)) 1 +
          cfc (fun x : Real => theta * x) A := by
          rw [cfc_const_add
            (R := Real) (A := Matrix (Fin N) (Fin N) Real)
            (p := IsSelfAdjoint)
            (r := 1) (f := fun x : Real => theta * x) (a := A)
            (ha := hA.1)]
    _ = (1 : Matrix (Fin N) (Fin N) Real) + theta • A := by
          rw [cfc_const_mul_id
            (R := Real) (A := Matrix (Fin N) (Fin N) Real)
            (p := IsSelfAdjoint) (r := theta) (a := A) (ha := hA.1)]
          simp

/-- Bridge B spectral hypotheses from the named shifted-eigenvalue composition
statement and the automatic finite PSD eigenvalue bound. -/
theorem bridgeB_spectral_hypotheses_of_shiftedEigenvalueComposition_autoNorm
    {N : Nat} {theta : Real}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (htheta : 0 < theta)
    (hcomp : BridgeBShiftedEigenvalueCompositionOfPos theta A hA htheta) :
    BridgeBSpectralHypotheses theta (routeBEigenvalueSumNormBound A hA)
      (Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det))
      A.rank hA.1.eigenvalues := by
  exact
    bridgeB_spectral_hypotheses_of_posSemidef_with_auto_shiftPosDef_autoNormBound
      A hA htheta hcomp

/-- Auto-norm matrix certificate variant that exposes the remaining shifted
eigenvalue composition as a named Route B spectral field. -/
def RouteBStrictAutoNormShiftedMatrixCertificate
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
      BridgeBShiftedEigenvalueCompositionOfPos theta A hA htheta ∧
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

/-- The named shifted-composition certificate is exactly the auto-norm
certificate expected by the current Route B assembly. -/
theorem routeBStrictAutoNormMatrixCertificate_of_shiftedMatrixCertificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (cert : RouteBStrictAutoNormShiftedMatrixCertificate M n hn2 htb hns) :
    RouteBStrictAutoNormMatrixCertificate M n hn2 htb hns := by
  rcases cert with
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, delta, rankLogRate, A, hA, Pi,
      htheta, halpha, halpha0, hgadgetN,
      hshift_eigs, hlower, hAdm, hcompat, hfun⟩
  exact
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, delta, rankLogRate, A, hA, Pi,
      htheta, halpha, halpha0, hgadgetN,
      hshift_eigs, hlower, hAdm, hcompat, hfun⟩

/-! ## Axiom audit anchors -/

#print axioms bridgeB_affine_cfc_charpoly
#print axioms bridgeB_affine_cfc_eq_shift
#print axioms bridgeB_spectral_hypotheses_of_shiftedEigenvalueComposition_autoNorm
#print axioms routeBStrictAutoNormMatrixCertificate_of_shiftedMatrixCertificate

end PallLean.Paper93.Paper283
