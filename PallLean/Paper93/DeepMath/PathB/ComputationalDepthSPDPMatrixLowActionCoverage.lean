import PallLean.Paper93.DeepMath.PathB.Theorem207FrontierStubs
import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef

/-!
# SPDP matrix route to corrected low-action God-Move coverage

This file adds the concrete bridge requested after calibrating Theorem 207's
coverage target.

The corrected target is not “every observer fits every exponent”.  It is:

every strict observer admits a low-action representative with its own exponent.

The SPDP/matrix route can supply that by giving, for each strict observer, a
family of matrix-level God-Move gauges together with the actual polynomial
capacity inequality for the observer's live-boundary trajectory.

The important point is that the matrix certificate must prove the inequality

```lean
Ls.toTrajectory.liveBoundaryRank n input time ≤ n ^ k
```

It is not enough to merely encode `Ls` into a matrix.  This file performs the
mechanical Lean conversion from such a certificate to low-action coverage and
then to the strict-port no-decider endpoint.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation

/-- Matrix/SPDP low-action certificate for one strict observer.

`matrixGaugeAt` is the positive-geometry/SPDP matrix surface at each input
length.  The load-bearing field is `liveBoundaryRank_le_poly_from_matrix`: it
is where the matrix construction must actually prove the polynomial live-boundary
capacity bound. -/
structure SPDPMatrixLowActionCertificate
    (enc : ThreeCNFEncoding)
    (Ls : StrictDynamicNFrameLagrangianObserver enc) : Type 1 where
  k : Nat
  matrixGaugeAt :
    forall n : Nat,
      exists A : Matrix (Fin n) (Fin n) ℝ,
        exists 𝒥 : Finset (Finset (Fin n)),
          IsAmplituhedronGauge A 𝒥
  liveBoundaryRank_le_poly_from_matrix :
    forall n : Nat,
      forall input : Fin n -> Bool,
      forall time : Nat,
        Ls.toTrajectory.liveBoundaryRank n input time <= n ^ k

/-- A matrix/SPDP low-action certificate gives the exact low-action observer.
The base observer is definitionally the same strict observer; only the
polynomial capacity field is supplied by the matrix certificate. -/
noncomputable def lowActionStrictObserver_of_spdpMatrixCertificate
    {enc : ThreeCNFEncoding}
    {Ls : StrictDynamicNFrameLagrangianObserver enc}
    (C : SPDPMatrixLowActionCertificate enc Ls) :
    LowActionStrictDynamicNFrameLagrangianObserver enc where
  base := Ls
  k := C.k
  liveBoundaryRank_le_poly := C.liveBoundaryRank_le_poly_from_matrix

/-- The SPDP matrix certificate gives one corrected coverage datum. -/
noncomputable def strictObserverLowActionCoverageDatum_of_spdpMatrixCertificate
    {enc : ThreeCNFEncoding}
    {Ls : StrictDynamicNFrameLagrangianObserver enc}
    (C : SPDPMatrixLowActionCertificate enc Ls) :
    StrictObserverLowActionGodMoveCoverageDatum enc Ls where
  lowActionObserver := lowActionStrictObserver_of_spdpMatrixCertificate C
  liveBoundaryRank_eq := by
    intro n input time
    rfl

/-- Uniform SPDP matrix certificates for all strict observers. -/
def SPDPMatrixLowActionCoverage
    (enc : ThreeCNFEncoding) : Prop :=
  forall Ls : StrictDynamicNFrameLagrangianObserver enc,
    Nonempty (SPDPMatrixLowActionCertificate enc Ls)

/-- The exact non-circular polynomial-bound target underneath the SPDP matrix
coverage statement.  The matrix positivity side is not the hard part: the
identity matrix already supplies a gauge.  The content is proving that each
strict observer's live-boundary trajectory has some polynomial exponent. -/
def StrictObserverLiveBoundaryPolynomialBound
    (enc : ThreeCNFEncoding) : Prop :=
  forall Ls : StrictDynamicNFrameLagrangianObserver enc,
    exists k : Nat,
      forall n : Nat,
        forall input : Fin n -> Bool,
        forall time : Nat,
          Ls.toTrajectory.liveBoundaryRank n input time <= n ^ k

/-- Identity matrices supply the matrix-gauge side at every length. -/
theorem identityMatrixGaugeAt_all_lengths :
    forall n : Nat,
      exists A : Matrix (Fin n) (Fin n) ℝ,
        exists 𝒥 : Finset (Finset (Fin n)),
          IsAmplituhedronGauge A 𝒥 := by
  intro n
  exact ⟨1, ∅, identity_isAmplituhedronGauge_empty⟩

/-- The matrix socket is discharged as soon as the live-boundary polynomial
bound is proved.  This shows precisely where the remaining mathematics lives:
not in constructing a matrix gauge, but in deriving `≤ n^k` for the strict
observer trajectory. -/
theorem spdpMatrixLowActionCoverage_of_liveBoundaryPolynomialBound
    {enc : ThreeCNFEncoding}
    (Hpoly : StrictObserverLiveBoundaryPolynomialBound enc) :
    SPDPMatrixLowActionCoverage enc := by
  intro Ls
  rcases Hpoly Ls with ⟨k, hk⟩
  exact ⟨{
    k := k
    matrixGaugeAt := identityMatrixGaugeAt_all_lengths
    liveBoundaryRank_le_poly_from_matrix := hk
  }⟩

/-- If there is no encoded SAT-deciding DTM, the coverage statement is
vacuously true because strict observers contain such a decider.  This is useful
as an audit theorem only; using it to prove the separation would be circular. -/
theorem spdpMatrixLowActionCoverage_of_no_DTMDecidesSATWithEncoding
    {enc : ThreeCNFEncoding}
    (hno : Not (exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M)) :
    SPDPMatrixLowActionCoverage enc := by
  intro Ls
  exact False.elim (hno ⟨Ls.M, Ls.decides⟩)

/-- Uniform matrix certificates discharge the corrected C2 obligation package. -/
noncomputable def strictObserverLowActionGodMoveCoverageObligations_of_spdpMatrixCoverage
    {enc : ThreeCNFEncoding}
    (Hmatrix : SPDPMatrixLowActionCoverage enc) :
    StrictObserverLowActionGodMoveCoverageObligations enc where
  coverageDatum := by
    intro Ls
    exact strictObserverLowActionCoverageDatum_of_spdpMatrixCertificate
      (Classical.choice (Hmatrix Ls))

/-- Uniform matrix certificates give corrected per-observer low-action coverage. -/
theorem perObserverStrictLowActionGodMoveCoverage_of_spdpMatrixCoverage
    {enc : ThreeCNFEncoding}
    (Hmatrix : SPDPMatrixLowActionCoverage enc) :
    PerObserverStrictLowActionGodMoveCoverage enc :=
  strictObserverLowActionGodMoveCoverage_theorem enc
    (strictObserverLowActionGodMoveCoverageObligations_of_spdpMatrixCoverage Hmatrix)

/-- Matrix route to the strict no-decider endpoint. -/
theorem no_DTMDecidesSATWithEncoding_of_theorem207StrictPort_and_spdpMatrixCoverage
    (enc : ThreeCNFEncoding)
    (Hport : Theorem207StrictLiveBoundaryPort enc)
    (Hmatrix : SPDPMatrixLowActionCoverage enc) :
    Not (exists M : TuringMachine.DTM,
      DTMDecidesSATWithEncoding enc M) :=
  no_DTMDecidesSATWithEncoding_of_theorem207StrictPort_and_perObserverCoverage
    enc Hport
    (perObserverStrictLowActionGodMoveCoverage_of_spdpMatrixCoverage Hmatrix)

/-- Fully bridged standard readout from strict port, SPDP matrix coverage, and
the chosen standard-model equivalence package. -/
theorem standardPvsNP_of_theorem207StrictPort_spdpMatrixCoverage_and_standardBridge
    (enc : ThreeCNFEncoding)
    (Hport : Theorem207StrictLiveBoundaryPort enc)
    (Hmatrix : SPDPMatrixLowActionCoverage enc)
    (Ostd : StandardPvsNPBridgeObligations enc) :
    (standardPvsNPBridge_instance enc Ostd).standardPvsNP := by
  have hno :
      Not (exists M : TuringMachine.DTM,
        DTMDecidesSATWithEncoding enc M) :=
    no_DTMDecidesSATWithEncoding_of_theorem207StrictPort_and_spdpMatrixCoverage
      enc Hport Hmatrix
  exact (standardPvsNPBridge_instance enc Ostd).standardPvsNP_iff_no_encodedSATDecider.mpr hno

/-! ## Axiom audit anchors -/
#print axioms lowActionStrictObserver_of_spdpMatrixCertificate
#print axioms strictObserverLowActionCoverageDatum_of_spdpMatrixCertificate
#print axioms identityMatrixGaugeAt_all_lengths
#print axioms spdpMatrixLowActionCoverage_of_liveBoundaryPolynomialBound
#print axioms spdpMatrixLowActionCoverage_of_no_DTMDecidesSATWithEncoding
#print axioms strictObserverLowActionGodMoveCoverageObligations_of_spdpMatrixCoverage
#print axioms perObserverStrictLowActionGodMoveCoverage_of_spdpMatrixCoverage
#print axioms no_DTMDecidesSATWithEncoding_of_theorem207StrictPort_and_spdpMatrixCoverage
#print axioms standardPvsNP_of_theorem207StrictPort_spdpMatrixCoverage_and_standardBridge

end PallLean.Paper93.DeepMath.PathB
