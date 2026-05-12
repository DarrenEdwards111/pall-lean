import PallLean.Paper93.Paper283.RouteBProjectedPWindowControlProof
import PallLean.Paper93.Paper283.RouteBZeroProfileQuotientedCompressionProof
import PallLean.Paper93.DeepMath.PathB.ZeroProfileConcreteNormalFormProgress

/-!
# Route B projected/log-window final certificate

This module retargets the final Route B consumer away from the older
`RouteBPerInstanceCertificate` path.  The old path builds the full
`CookLevinRichProjectionTarget`, so it still asks for global rank
monotonicity through SPDP image containment and for an unprojected P-window
bound.

The paper-faithful projected route is smaller: at paper scale, a selected
projection with

* the direct projected P-side upper bound, and
* the projected NP identity-minor lower bound on the same image

already contradicts a bounded SAT decider.  The old rich-projection discharge
is recovered only afterward, through the existing no-decider equivalence.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open SymmetricPowerBound
open WithinProfileBound
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- At the paper scale, `n ≥ 2^804` supplies the side condition `n ≥ 4`
needed by the concreteW local chart/row-embedding route. -/
theorem routeBProjectedLogWindow_paperScale_ge_four
    {n : Nat} (hn : n >= 2 ^ 804) : n >= 4 := by
  have hpow : (4 : Nat) <= 2 ^ 804 := by
    calc
      (4 : Nat) = 2 ^ 2 := by norm_num
      _ <= 2 ^ 804 := by
        exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  exact le_trans hpow hn

/-- Corrected final Route B certificate for one Cook-Levin instance.

This is deliberately not `RouteBPerInstanceCertificate`: it does not ask for
full SPDP image containment, rank monotonicity, or an unprojected P-window
promotion.  It packages exactly the two rank statements that the projected
Route B extraction must put on the same selected gauge image. -/
structure RouteBProjectedLogWindowFinalCertificate
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    Type where
  Pi : PallLean.Paper93.NFrame.CandidateGauge
    (RouteBCookLevinDim M n hn2 htb hns)
  p_side :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)
  np_lower_bound :
    RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)

/-- The projected NP lower bound packaged in the corrected certificate is the
NP-preservation field needed by the existing contradiction lemma. -/
theorem routeBProjectedLogWindowFinalCertificate_npPreservation
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (cert :
      RouteBProjectedLogWindowFinalCertificate M n hn2 htb hns) :
    SATDeciderGaugeNPIdentityMinorPreservation M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns cert.Pi) :=
  satDeciderGaugeNPIdentityMinorPreservation_of_projected_compiled_lower_bound
    M n hn2 htb hns
    (routeBNFrameCandidateAsSATGauge M n hn2 htb hns cert.Pi)
    cert.np_lower_bound

/-- A corrected projected/log-window Route B certificate contradicts a bounded
SAT decider at paper scale.  No rank-monotonicity or global SPDP containment
is used here. -/
theorem false_of_routeBProjectedLogWindowFinalCertificate
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hdec : DecidesSAT M)
    (cert :
      RouteBProjectedLogWindowFinalCertificate M n hn2 htb hns) :
    False :=
  satDeciderGauge_pSide_and_npIdentityMinor_incompatible_at_large_n
    M n hn hn2 htb hns
    (routeBNFrameCandidateAsSATGauge M n hn2 htb hns cert.Pi)
    hdec cert.p_side
    (routeBProjectedLogWindowFinalCertificate_npPreservation
      M n hn2 htb hns cert)

/-- Uniform corrected projected/log-window Route B certificates rule out
bounded SAT deciders at the paper scale. -/
theorem noBoundedSATDeciderAtPaperScale_of_routeBProjectedLogWindowFinalCertificates
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBProjectedLogWindowFinalCertificate M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale := by
  intro M n hn hn2 htb hns hdec
  exact
    false_of_routeBProjectedLogWindowFinalCertificate
      M n hn hn2 htb hns hdec
      (hcert M n hn hn2 htb hns hdec)

/-- The old rich-projection discharge follows from corrected
projected/log-window Route B certificates only through the established
no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_routeBProjectedLogWindowFinalCertificates
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        RouteBProjectedLogWindowFinalCertificate M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_routeBProjectedLogWindowFinalCertificates
      hcert)

/-- Constructor from the two primitive projected Route B consumers:
a projected P-window finite-span cover and a fixed-embed NP certificate. -/
noncomputable def routeBProjectedLogWindowFinalCertificate_of_projectedPWindowCover_npCertificate
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (cover :
      RouteBRicherGaugeProjectedPWindowFiniteSpanCover
        M n hn2 htb hns Pi)
    (npCert :
      RouteBNPIdentityMinorFixedEmbedCertificate M n hn2 htb hns Pi) :
    RouteBProjectedLogWindowFinalCertificate M n hn2 htb hns where
  Pi := Pi
  p_side :=
    routeBRicherGauge_projectedPSideBound_of_projectedFiniteSpanCover
      M n hn2 htb hns Pi cover
  np_lower_bound :=
    routeBSATProjectedNPIdentityMinorLowerBound_of_fixed_embed_certificate
      M n hn2 htb hns Pi npCert

/-- Concrete singleton-quotient zero-profile normal forms feed the corrected
projected/log-window final certificate for any selected Route B gauge, once
the projected P-window is contained in that quotiented zero-profile span and
the NP fixed-embed certificate is supplied. -/
noncomputable def routeBProjectedLogWindowFinalCertificate_of_concreteSingletonQuotient
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    {typeBudget : Nat}
    (D :
      ZeroProfileConcreteNormalFormData n (Nat.log 2 n) typeBudget)
    (hmap :
      ZeroProfileConcreteNormalFormRowMap
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
        D)
    (hbudget : typeBudget <= withinProfileBound (Nat.log 2 n))
    (hcontrol :
      RouteBProjectedPWindowControlledByZeroProfileProjection
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
        Pi)
    (npCert :
      RouteBNPIdentityMinorFixedEmbedCertificate M n hn2 htb hns Pi) :
    RouteBProjectedLogWindowFinalCertificate M n hn2 htb hns where
  Pi := Pi
  p_side :=
    routeBRicherGauge_projectedPSideBound_of_zeroProfileQuotientedShiftCommonSpan
      M n hn2 htb hns
      (zeroProfileQuotientBySingletonShiftProjection
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
      Pi
      (cookLevinZeroProfileQuotientedShiftCommonSpan_of_concreteSingletonQuotientRowMap
        M n hn2 htb hns D hmap hbudget)
      hcontrol
      (routeB_withinProfileBound_log_le_pow_200 n hn2)
  np_lower_bound :=
    routeBSATProjectedNPIdentityMinorLowerBound_of_fixed_embed_certificate
      M n hn2 htb hns Pi npCert

/-- Concrete projected zero-profile normal forms feed the corrected
projected/log-window final certificate for any selected Route B gauge and any
projection/normalizer.  This is the direct final consumer for the paper's
Boolean/multilinear quotient route: no singleton-killing kernel or residual
payment is required by the final projected rank comparison. -/
noncomputable def routeBProjectedLogWindowFinalCertificate_of_concreteProjectedNormalForms
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)
    {typeBudget : Nat}
    (D :
      ZeroProfileConcreteNormalFormData n (Nat.log 2 n) typeBudget)
    (hmap :
      ZeroProfileConcreteNormalFormRowMap
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project D)
    (hbudget : typeBudget <= withinProfileBound (Nat.log 2 n))
    (hcontrol :
      RouteBProjectedPWindowControlledByZeroProfileProjection
        M n hn2 htb hns project Pi)
    (npCert :
      RouteBNPIdentityMinorFixedEmbedCertificate M n hn2 htb hns Pi) :
    RouteBProjectedLogWindowFinalCertificate M n hn2 htb hns where
  Pi := Pi
  p_side :=
    routeBRicherGauge_projectedPSideBound_of_zeroProfileProjectedCommonSpanWithBudget
      M n hn2 htb hns project Pi
      (zeroProfileProjectedCommonSpanWithBudget_of_concreteRowMap
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project D hmap)
      hcontrol
      (hbudget.trans (routeB_withinProfileBound_log_le_pow_200 n hn2))
  np_lower_bound :=
    routeBSATProjectedNPIdentityMinorLowerBound_of_fixed_embed_certificate
      M n hn2 htb hns Pi npCert

/-- Boolean-normalized concrete zero-profile normal forms feed the corrected
projected/log-window final certificate.  This is the named final hook for the
paper's `x_i^2 = x_i` multilinear quotient normalizer. -/
noncomputable def routeBProjectedLogWindowFinalCertificate_of_booleanConcreteNormalForms
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    {typeBudget : Nat}
    (D :
      ZeroProfileConcreteNormalFormData n (Nat.log 2 n) typeBudget)
    (hmap :
      ZeroProfileConcreteNormalFormRowMap
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (zeroProfileBooleanNormalizeLinearMap (n := n)) D)
    (hbudget : typeBudget <= withinProfileBound (Nat.log 2 n))
    (hcontrol :
      RouteBProjectedPWindowControlledByZeroProfileProjection
        M n hn2 htb hns
        (zeroProfileBooleanNormalizeLinearMap (n := n)) Pi)
    (npCert :
      RouteBNPIdentityMinorFixedEmbedCertificate M n hn2 htb hns Pi) :
    RouteBProjectedLogWindowFinalCertificate M n hn2 htb hns :=
  routeBProjectedLogWindowFinalCertificate_of_concreteProjectedNormalForms
    M n hn2 htb hns Pi
    (zeroProfileBooleanNormalizeLinearMap (n := n))
    D hmap hbudget hcontrol npCert

/-- Head-span specialization of the Boolean-normalized final hook.  The NP
side is supplied by the existing coupled-sheet source identity minor, so the
remaining inputs are exactly the Boolean normal-form row classifier, its
budget, and projected P-window containment for the selected head-span gauge. -/
noncomputable def routeBProjectedLogWindowFinalCertificate_of_headSpan_booleanConcreteNormalForms
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {typeBudget : Nat}
    (D :
      ZeroProfileConcreteNormalFormData n (Nat.log 2 n) typeBudget)
    (hmap :
      ZeroProfileConcreteNormalFormRowMap
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (zeroProfileBooleanNormalizeLinearMap (n := n)) D)
    (hbudget : typeBudget <= withinProfileBound (Nat.log 2 n))
    (hcontrol :
      RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowControlledByZeroProfileProjection
        M n hn2 htb hns
        (zeroProfileBooleanNormalizeLinearMap (n := n))) :
    RouteBProjectedLogWindowFinalCertificate M n hn2 htb hns :=
  routeBProjectedLogWindowFinalCertificate_of_booleanConcreteNormalForms
    M n hn2 htb hns
    (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns)
    D hmap hbudget
    (by
      simpa [RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowControlledByZeroProfileProjection]
        using hcontrol)
    (routeBPaperFaithfulPiPhiHeadSpan_identityMinorFixedEmbedCertificate
      M n hn2 htb hns
      (routeBRicherConcreteNPWitnessQ_sourceIdentityMinorLowerBound
        M n hn hn2 htb hns))

/-- Paper-faithful head-span specialization: a quotiented zero-profile
normal-form span can feed the corrected final certificate once it controls the
projected P-window for the selected head-span gauge. -/
noncomputable def routeBProjectedLogWindowFinalCertificate_of_headSpan_zeroProfileQuotiented
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)
    (hquot :
      CookLevinZeroProfileQuotientedShiftCommonSpan
        M n hn2 htb hns project)
    (hcontrol :
      RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowControlledByZeroProfileProjection
        M n hn2 htb hns project) :
    RouteBProjectedLogWindowFinalCertificate M n hn2 htb hns where
  Pi := routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns
  p_side :=
    routeBPaperFaithfulPiPhiHeadSpan_projectedPSideBound_of_zeroProfileQuotientedShiftCommonSpan
      M n hn2 htb hns project hquot hcontrol
  np_lower_bound := by
    simpa [routeBPaperFaithfulPiPhiHeadSpanProjection] using
      routeBPaperFaithfulPiPhiHeadSpan_projectedNPIdentityMinorLowerBound_of_source
        M n hn2 htb hns
        (routeBRicherConcreteNPWitnessQ_sourceIdentityMinorLowerBound
          M n hn hn2 htb hns)

/-- Pointwise projected P-window row identity is sufficient for the corrected
head-span final certificate.  This is the narrow proof-facing form of the
remaining P-window obligation: no global admissible-query promotion is used. -/
noncomputable def routeBProjectedLogWindowFinalCertificate_of_headSpan_zeroProfileQuotiented_rowIdentity
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)
    (hquot :
      CookLevinZeroProfileQuotientedShiftCommonSpan
        M n hn2 htb hns project)
    (hrow :
      RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileRowIdentity
        M n hn2 htb hns project) :
    RouteBProjectedLogWindowFinalCertificate M n hn2 htb hns :=
  routeBProjectedLogWindowFinalCertificate_of_headSpan_zeroProfileQuotiented
    M n hn hn2 htb hns project hquot
    (routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowControlledByZeroProfileProjection_of_rowIdentity
      M n hn2 htb hns project hrow)

/-- Concrete projected normal forms plus the pointwise projected P-window row
identity feed the corrected head-span final certificate directly. -/
noncomputable def routeBProjectedLogWindowFinalCertificate_of_headSpan_concreteProjectedNormalForms_rowIdentity
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (project :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)
    {typeBudget : Nat}
    (D :
      ZeroProfileConcreteNormalFormData n (Nat.log 2 n) typeBudget)
    (hmap :
      ZeroProfileConcreteNormalFormRowMap
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        project D)
    (hbudget : typeBudget <= withinProfileBound (Nat.log 2 n))
    (hrow :
      RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileRowIdentity
        M n hn2 htb hns project) :
    RouteBProjectedLogWindowFinalCertificate M n hn2 htb hns :=
  routeBProjectedLogWindowFinalCertificate_of_concreteProjectedNormalForms
    M n hn2 htb hns
    (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns)
    project D hmap hbudget
    (routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowControlledByZeroProfileProjection_of_rowIdentity
      M n hn2 htb hns project hrow)
    (routeBPaperFaithfulPiPhiHeadSpan_identityMinorFixedEmbedCertificate
      M n hn2 htb hns
      (routeBRicherConcreteNPWitnessQ_sourceIdentityMinorLowerBound
        M n hn hn2 htb hns))

/-- Concrete `concreteW` zero-profile classifier plus pointwise projected row
identity feeds the corrected head-span final certificate.  The row classifier
is not an assumption here: it is constructed from the direct `concreteW`
per-type row-embedding package. -/
noncomputable def routeBProjectedLogWindowFinalCertificate_of_headSpan_concreteWRowEmbeddings_id_rowIdentity
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4)
    (hrow :
      RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileRowIdentity
        M n hn2 htb hns
        (LinearMap.id :
          MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)) :
    RouteBProjectedLogWindowFinalCertificate M n hn2 htb hns :=
  routeBProjectedLogWindowFinalCertificate_of_headSpan_concreteProjectedNormalForms_rowIdentity
    M n hn hn2 htb hns
    (LinearMap.id :
      MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)
    (zeroProfileConcreteNormalFormData_singletonZeroProfile_concreteW
      (κ := Nat.log 2 n) hn4)
    (zeroProfileConcreteNormalFormRowMap_id_concreteW_of_rowEmbeddings
      M n hn2 htb hns hn4 hRowEmbeddings)
    (zeroProfileSymmetricProfileDim_zeroProfileHistogram_le_withinProfileBound
      (Nat.log 2 n))
    hrow

/-- Paper-scale convenience form of the concreteW classifier final hook: the
`n ≥ 4` side condition required by `concreteW` follows from `n ≥ 2^804`. -/
noncomputable def routeBProjectedLogWindowFinalCertificate_of_headSpan_concreteWRowEmbeddings_id_rowIdentity_paperScale
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns
          (routeBProjectedLogWindow_paperScale_ge_four hn))
    (hrow :
      RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileRowIdentity
        M n hn2 htb hns
        (LinearMap.id :
          MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)) :
    RouteBProjectedLogWindowFinalCertificate M n hn2 htb hns :=
  routeBProjectedLogWindowFinalCertificate_of_headSpan_concreteWRowEmbeddings_id_rowIdentity
    M n hn hn2 htb hns
    (routeBProjectedLogWindow_paperScale_ge_four hn)
    hRowEmbeddings hrow

/-- Exact singleton-quotient projected-finrank budget plus pointwise row
identity feeds the corrected head-span final certificate.  This is the narrow
paper-faithful final gate for the quotient route: prove the projected quotient
budget and prove the selected P-window row identity. -/
noncomputable def routeBProjectedLogWindowFinalCertificate_of_headSpan_singletonQuotient_projectedTypeBudget_rowIdentity
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hbudget :
      zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
        withinProfileBound (Nat.log 2 n))
    (hrow :
      RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileRowIdentity
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    RouteBProjectedLogWindowFinalCertificate M n hn2 htb hns :=
  routeBProjectedLogWindowFinalCertificate_of_headSpan_zeroProfileQuotiented_rowIdentity
    M n hn hn2 htb hns
    (zeroProfileQuotientBySingletonShiftProjection
      (fun i => (cookLevinFactorList M n hn2 htb hns).get i))
    (cookLevinZeroProfileQuotientedShiftCommonSpan_of_singletonQuotient_projectedTypeBudget
      M n hn2 htb hns hbudget)
    hrow

/-- Concrete `concreteW` row embeddings discharge the exact singleton-quotient
budget for the corrected head-span final certificate.  The only remaining
input is the selected singleton-quotient row identity. -/
noncomputable def routeBProjectedLogWindowFinalCertificate_of_headSpan_singletonQuotient_concreteW_rowEmbeddings_rowIdentity
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4)
    (hrow :
      RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileRowIdentity
        M n hn2 htb hns
        (zeroProfileQuotientBySingletonShiftProjection
          (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    RouteBProjectedLogWindowFinalCertificate M n hn2 htb hns :=
  routeBProjectedLogWindowFinalCertificate_of_headSpan_singletonQuotient_projectedTypeBudget_rowIdentity
    M n hn hn2 htb hns
    (cookLevinZeroProfileSingletonQuotientProjectedTypeBudget_le_withinProfileBound_of_concreteW_rowEmbeddings
      M n hn2 htb hns hn4 hRowEmbeddings)
    hrow

/-- Concrete `concreteW` row embeddings give a budgeted zero-profile span after
applying the selected head-span projection.  The only remaining input is the
selected head-span row identity. -/
noncomputable def routeBProjectedLogWindowFinalCertificate_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_rowIdentity
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4)
    (hrow :
      RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileRowIdentity
        M n hn2 htb hns
        (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)) :
    RouteBProjectedLogWindowFinalCertificate M n hn2 htb hns where
  Pi := routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns
  p_side :=
    routeBRicherGauge_projectedPSideBound_of_zeroProfileProjectedCommonSpanWithBudget
      M n hn2 htb hns
      (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)
      (routeBPaperFaithfulPiPhiHeadSpanGauge M n hn2 htb hns)
      (zeroProfileProjectedCommonSpanWithBudget_of_id_projectedCommonSpan
        (fun i => (cookLevinFactorList M n hn2 htb hns).get i)
        (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)
        (zeroProfileProjectedCommonSpanWithBudget_id_concreteW_of_rowEmbeddings
          M n hn2 htb hns hn4 hRowEmbeddings))
      (by
        simpa [RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowControlledByZeroProfileProjection]
          using
            routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowControlledByZeroProfileProjection_of_rowIdentity
              M n hn2 htb hns
              (routeBPaperFaithfulPiPhiHeadSpanProjection M n hn2 htb hns)
              hrow)
      ((zeroProfileSymmetricProfileDim_zeroProfileHistogram_le_withinProfileBound
        (Nat.log 2 n)).trans
        (routeB_withinProfileBound_log_le_pow_200 n hn2))
  np_lower_bound := by
    simpa [routeBPaperFaithfulPiPhiHeadSpanProjection] using
      routeBPaperFaithfulPiPhiHeadSpan_projectedNPIdentityMinorLowerBound_of_source
        M n hn2 htb hns
        (routeBRicherConcreteNPWitnessQ_sourceIdentityMinorLowerBound
          M n hn hn2 htb hns)

/-- Retarget plus absence of a visible residual projection escape closes the
selected head-span row identity; concrete `concreteW` row embeddings provide
the projected zero-profile span after applying that same projection. -/
noncomputable def routeBProjectedLogWindowFinalCertificate_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_retarget_noResidualProjectionEscape
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4)
    (retarget :
      RouteBPaperFaithfulPiPhiHeadSpanProjectionRetarget
        M n hn2 htb hns)
    (hnoEscape :
      ¬ RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowCompiledDerivativeResidualProjectionEscape
          M n hn2 htb hns) :
    RouteBProjectedLogWindowFinalCertificate M n hn2 htb hns :=
  routeBProjectedLogWindowFinalCertificate_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_rowIdentity
    M n hn hn2 htb hns hn4 hRowEmbeddings
    (routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowZeroProfileRowIdentity_of_retarget_of_residual_chosenComplement
      M n hn2 htb hns retarget
      ((routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowCompiledDerivativeResidualChosenComplement_iff_no_residualProjectionEscape
        M n hn2 htb hns).mpr hnoEscape))

/-- Checked stable-map inputs plus absence of the concrete residual projection
escape close the selected head-span final certificate without constructing the
old retarget package, whose global admissible-query log-window field is
Lean-refuted. -/
noncomputable def routeBProjectedLogWindowFinalCertificate_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_checkedInputs_noResidualProjectionEscape
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hn4 : n >= 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns hn4)
    (hinputs :
      RouteBPaperFaithfulPiPhiHeadSpanCheckedStableMapInputs
        M n hn2 htb hns)
    (hnoEscape :
      ¬ RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowCompiledDerivativeResidualProjectionEscape
          M n hn2 htb hns) :
    RouteBProjectedLogWindowFinalCertificate M n hn2 htb hns :=
  routeBProjectedLogWindowFinalCertificate_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_rowIdentity
    M n hn hn2 htb hns hn4 hRowEmbeddings
    (routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowZeroProfileRowIdentity_of_checkedStableMapInputs_of_residual_chosenComplement
      M n hn2 htb hns hinputs
      ((routeBPaperFaithfulPiPhiHeadSpan_projectedPWindowCompiledDerivativeResidualChosenComplement_iff_no_residualProjectionEscape
        M n hn2 htb hns).mpr hnoEscape))

/-- Paper-scale convenience form of the corrected selected-projection
head-span final certificate. -/
noncomputable def routeBProjectedLogWindowFinalCertificate_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_retarget_noResidualProjectionEscape_paperScale
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns
          (routeBProjectedLogWindow_paperScale_ge_four hn))
    (retarget :
      RouteBPaperFaithfulPiPhiHeadSpanProjectionRetarget
        M n hn2 htb hns)
    (hnoEscape :
      ¬ RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowCompiledDerivativeResidualProjectionEscape
          M n hn2 htb hns) :
    RouteBProjectedLogWindowFinalCertificate M n hn2 htb hns :=
  routeBProjectedLogWindowFinalCertificate_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_retarget_noResidualProjectionEscape
    M n hn hn2 htb hns
    (routeBProjectedLogWindow_paperScale_ge_four hn)
    hRowEmbeddings retarget hnoEscape

/-- Paper-scale convenience form of the checked-input selected-projection
head-span final certificate. -/
noncomputable def routeBProjectedLogWindowFinalCertificate_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_checkedInputs_noResidualProjectionEscape_paperScale
    (M : DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn2 htb hns
          (routeBProjectedLogWindow_paperScale_ge_four hn))
    (hinputs :
      RouteBPaperFaithfulPiPhiHeadSpanCheckedStableMapInputs
        M n hn2 htb hns)
    (hnoEscape :
      ¬ RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowCompiledDerivativeResidualProjectionEscape
          M n hn2 htb hns) :
    RouteBProjectedLogWindowFinalCertificate M n hn2 htb hns :=
  routeBProjectedLogWindowFinalCertificate_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_checkedInputs_noResidualProjectionEscape
    M n hn hn2 htb hns
    (routeBProjectedLogWindow_paperScale_ge_four hn)
    hRowEmbeddings hinputs hnoEscape

/-- Uniform head-span quotiented zero-profile certificates rule out bounded
SAT deciders without passing through the false global log-window query
promotion. -/
theorem noBoundedSATDeciderAtPaperScale_of_headSpan_zeroProfileQuotiented
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists project :
          MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat,
          CookLevinZeroProfileQuotientedShiftCommonSpan
            M n hn2 htb hns project ∧
          RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowControlledByZeroProfileProjection
            M n hn2 htb hns project) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBProjectedLogWindowFinalCertificates
    (by
      intro M n hn hn2 htb hns hdec
      let hx := hcert M n hn hn2 htb hns hdec
      let project := Classical.choose hx
      have hspec := Classical.choose_spec hx
      exact
        routeBProjectedLogWindowFinalCertificate_of_headSpan_zeroProfileQuotiented
          M n hn hn2 htb hns project hspec.1 hspec.2)

/-- The old rich-projection discharge follows from the corrected head-span
zero-profile route only through the no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_headSpan_zeroProfileQuotiented
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists project :
          MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat,
          CookLevinZeroProfileQuotientedShiftCommonSpan
            M n hn2 htb hns project ∧
          RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowControlledByZeroProfileProjection
            M n hn2 htb hns project) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_headSpan_zeroProfileQuotiented hcert)

/-- Uniform concrete `concreteW` zero-profile classifiers plus the selected
head-span row identity rule out bounded SAT deciders through the corrected
projected/log-window consumer. -/
theorem noBoundedSATDeciderAtPaperScale_of_headSpan_concreteWRowEmbeddings_id_rowIdentity
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileRowIdentity
            M n hn2 htb hns
            (LinearMap.id :
              MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBProjectedLogWindowFinalCertificates
    (by
      intro M n hn hn2 htb hns hdec
      let hx := hcert M n hn hn2 htb hns hdec
      let hn4 := Classical.choose hx
      have hspec := Classical.choose_spec hx
      exact
        routeBProjectedLogWindowFinalCertificate_of_headSpan_concreteWRowEmbeddings_id_rowIdentity
          M n hn hn2 htb hns hn4 hspec.1 hspec.2)

/-- Uniform concreteW row embeddings plus the selected head-span row identity
rule out bounded SAT deciders.  Compared with the existential form above, the
zero-profile classifier is now fully constructed from the supplied local
row-embedding theorem at the paper-scale `n ≥ 4` side condition. -/
theorem noBoundedSATDeciderAtPaperScale_of_headSpan_concreteWRowEmbeddings_id_rowIdentity_universal
    (hRowEmbeddings :
      forall (M : DTM) (n : Nat) (hn2 : n >= 2) (hn4 : n >= 4)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
          M n hn2 htb hns hn4)
    (hrow :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileRowIdentity
          M n hn2 htb hns
          (LinearMap.id :
            MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBProjectedLogWindowFinalCertificates
    (by
      intro M n hn hn2 htb hns hdec
      exact
        routeBProjectedLogWindowFinalCertificate_of_headSpan_concreteWRowEmbeddings_id_rowIdentity_paperScale
          M n hn hn2 htb hns
          (hRowEmbeddings M n hn2
            (routeBProjectedLogWindow_paperScale_ge_four hn) htb hns)
          (hrow M n hn hn2 htb hns))

/-- Uniform exact singleton-quotient projected-finrank budget plus row identity
rule out bounded SAT deciders. -/
theorem noBoundedSATDeciderAtPaperScale_of_headSpan_singletonQuotient_projectedTypeBudget_rowIdentity
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
          withinProfileBound (Nat.log 2 n) ∧
        RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileRowIdentity
          M n hn2 htb hns
          (zeroProfileQuotientBySingletonShiftProjection
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBProjectedLogWindowFinalCertificates
    (by
      intro M n hn hn2 htb hns hdec
      exact
        routeBProjectedLogWindowFinalCertificate_of_headSpan_singletonQuotient_projectedTypeBudget_rowIdentity
          M n hn hn2 htb hns
          (hcert M n hn hn2 htb hns hdec).1
          (hcert M n hn hn2 htb hns hdec).2)

/-- Uniform corrected head-span certificates from concrete `concreteW`
row embeddings, projection retarget, and absence of residual projection
escapes for the selected head-span projection. -/
theorem noBoundedSATDeciderAtPaperScale_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_retarget_noResidualProjectionEscape
    (hRowEmbeddings :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
          M n hn2 htb hns
            (routeBProjectedLogWindow_paperScale_ge_four _hn))
    (hretarget :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        RouteBPaperFaithfulPiPhiHeadSpanProjectionRetarget
          M n hn2 htb hns)
    (hnoEscape :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        ¬ RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowCompiledDerivativeResidualProjectionEscape
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBProjectedLogWindowFinalCertificates
    (by
      intro M n hn hn2 htb hns hdec
      exact
        routeBProjectedLogWindowFinalCertificate_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_retarget_noResidualProjectionEscape_paperScale
          M n hn hn2 htb hns
          (hRowEmbeddings M n hn hn2 htb hns)
          (hretarget M n hn hn2 htb hns)
          (hnoEscape M n hn hn2 htb hns))

/-- Uniform checked-input selected-projection certificates from concrete
`concreteW` row embeddings, checked stable-map inputs, and absence of residual
projection escapes.  This is the positive replacement for the refuted retarget
consumer. -/
theorem noBoundedSATDeciderAtPaperScale_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_checkedInputs_noResidualProjectionEscape
    (hRowEmbeddings :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
          M n hn2 htb hns
            (routeBProjectedLogWindow_paperScale_ge_four _hn))
    (hinputs :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        RouteBPaperFaithfulPiPhiHeadSpanCheckedStableMapInputs
          M n hn2 htb hns)
    (hnoEscape :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        ¬ RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowCompiledDerivativeResidualProjectionEscape
          M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBProjectedLogWindowFinalCertificates
    (by
      intro M n hn hn2 htb hns hdec
      exact
        routeBProjectedLogWindowFinalCertificate_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_checkedInputs_noResidualProjectionEscape_paperScale
          M n hn hn2 htb hns
          (hRowEmbeddings M n hn hn2 htb hns)
          (hinputs M n hn hn2 htb hns)
          (hnoEscape M n hn hn2 htb hns))

/-- The old rich-projection discharge follows from the concrete `concreteW`
classifier route only through the no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_headSpan_concreteWRowEmbeddings_id_rowIdentity
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        exists hn4 : n >= 4,
          PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
            M n hn2 htb hns hn4 ∧
          RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileRowIdentity
            M n hn2 htb hns
            (LinearMap.id :
              MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_headSpan_concreteWRowEmbeddings_id_rowIdentity
      hcert)

/-- Legacy rich-projection discharge from the universal concreteW classifier
and selected row-identity route, mediated only by the no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_headSpan_concreteWRowEmbeddings_id_rowIdentity_universal
    (hRowEmbeddings :
      forall (M : DTM) (n : Nat) (hn2 : n >= 2) (hn4 : n >= 4)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
          M n hn2 htb hns hn4)
    (hrow :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileRowIdentity
          M n hn2 htb hns
          (LinearMap.id :
            MvPolynomial (Fin n) Rat →ₗ[Rat] MvPolynomial (Fin n) Rat)) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_headSpan_concreteWRowEmbeddings_id_rowIdentity_universal
      hRowEmbeddings hrow)

/-- The old rich-projection discharge follows from the exact singleton-quotient
projected route only through the no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_headSpan_singletonQuotient_projectedTypeBudget_rowIdentity
    (hcert :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n)
        (_hdec : DecidesSAT M),
        zeroProfileSingletonQuotientProjectedTypeBudget (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i) <=
          withinProfileBound (Nat.log 2 n) ∧
        RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowZeroProfileRowIdentity
          M n hn2 htb hns
          (zeroProfileQuotientBySingletonShiftProjection
            (fun i => (cookLevinFactorList M n hn2 htb hns).get i))) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_headSpan_singletonQuotient_projectedTypeBudget_rowIdentity
      hcert)

/-- Legacy rich-projection discharge from the corrected selected-projection
head-span route, mediated only by the no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_retarget_noResidualProjectionEscape
    (hRowEmbeddings :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
          M n hn2 htb hns
            (routeBProjectedLogWindow_paperScale_ge_four _hn))
    (hretarget :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        RouteBPaperFaithfulPiPhiHeadSpanProjectionRetarget
          M n hn2 htb hns)
    (hnoEscape :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        ¬ RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowCompiledDerivativeResidualProjectionEscape
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_retarget_noResidualProjectionEscape
      hRowEmbeddings hretarget hnoEscape)

/-- Legacy rich-projection discharge from the checked-input selected-projection
route, mediated only by the no-decider equivalence. -/
theorem cookLevinRichProjectionDischarge_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_checkedInputs_noResidualProjectionEscape
    (hRowEmbeddings :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
          M n hn2 htb hns
            (routeBProjectedLogWindow_paperScale_ge_four _hn))
    (hinputs :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        RouteBPaperFaithfulPiPhiHeadSpanCheckedStableMapInputs
          M n hn2 htb hns)
    (hnoEscape :
      forall (M : DTM) (n : Nat) (_hn : n >= 2 ^ 804) (hn2 : n >= 2)
        (htb : M.timeBound <= 4) (hns : M.numStates <= n),
        ¬ RouteBPaperFaithfulPiPhiHeadSpanProjectedPWindowCompiledDerivativeResidualProjectionEscape
          M n hn2 htb hns) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_checkedInputs_noResidualProjectionEscape
      hRowEmbeddings hinputs hnoEscape)

/-! ## Axiom audit anchors -/

#print axioms RouteBProjectedLogWindowFinalCertificate
#print axioms routeBProjectedLogWindow_paperScale_ge_four
#print axioms routeBProjectedLogWindowFinalCertificate_npPreservation
#print axioms false_of_routeBProjectedLogWindowFinalCertificate
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBProjectedLogWindowFinalCertificates
#print axioms cookLevinRichProjectionDischarge_of_routeBProjectedLogWindowFinalCertificates
#print axioms routeBProjectedLogWindowFinalCertificate_of_projectedPWindowCover_npCertificate
#print axioms routeBProjectedLogWindowFinalCertificate_of_concreteSingletonQuotient
#print axioms routeBProjectedLogWindowFinalCertificate_of_concreteProjectedNormalForms
#print axioms routeBProjectedLogWindowFinalCertificate_of_booleanConcreteNormalForms
#print axioms routeBProjectedLogWindowFinalCertificate_of_headSpan_booleanConcreteNormalForms
#print axioms routeBProjectedLogWindowFinalCertificate_of_headSpan_zeroProfileQuotiented
#print axioms routeBProjectedLogWindowFinalCertificate_of_headSpan_zeroProfileQuotiented_rowIdentity
#print axioms routeBProjectedLogWindowFinalCertificate_of_headSpan_concreteProjectedNormalForms_rowIdentity
#print axioms routeBProjectedLogWindowFinalCertificate_of_headSpan_concreteWRowEmbeddings_id_rowIdentity
#print axioms routeBProjectedLogWindowFinalCertificate_of_headSpan_concreteWRowEmbeddings_id_rowIdentity_paperScale
#print axioms routeBProjectedLogWindowFinalCertificate_of_headSpan_singletonQuotient_projectedTypeBudget_rowIdentity
#print axioms routeBProjectedLogWindowFinalCertificate_of_headSpan_singletonQuotient_concreteW_rowEmbeddings_rowIdentity
#print axioms routeBProjectedLogWindowFinalCertificate_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_rowIdentity
#print axioms routeBProjectedLogWindowFinalCertificate_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_retarget_noResidualProjectionEscape
#print axioms routeBProjectedLogWindowFinalCertificate_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_retarget_noResidualProjectionEscape_paperScale
#print axioms routeBProjectedLogWindowFinalCertificate_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_checkedInputs_noResidualProjectionEscape
#print axioms routeBProjectedLogWindowFinalCertificate_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_checkedInputs_noResidualProjectionEscape_paperScale
#print axioms noBoundedSATDeciderAtPaperScale_of_headSpan_zeroProfileQuotiented
#print axioms cookLevinRichProjectionDischarge_of_headSpan_zeroProfileQuotiented
#print axioms noBoundedSATDeciderAtPaperScale_of_headSpan_concreteWRowEmbeddings_id_rowIdentity
#print axioms noBoundedSATDeciderAtPaperScale_of_headSpan_concreteWRowEmbeddings_id_rowIdentity_universal
#print axioms noBoundedSATDeciderAtPaperScale_of_headSpan_singletonQuotient_projectedTypeBudget_rowIdentity
#print axioms noBoundedSATDeciderAtPaperScale_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_retarget_noResidualProjectionEscape
#print axioms noBoundedSATDeciderAtPaperScale_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_checkedInputs_noResidualProjectionEscape
#print axioms cookLevinRichProjectionDischarge_of_headSpan_concreteWRowEmbeddings_id_rowIdentity
#print axioms cookLevinRichProjectionDischarge_of_headSpan_concreteWRowEmbeddings_id_rowIdentity_universal
#print axioms cookLevinRichProjectionDischarge_of_headSpan_singletonQuotient_projectedTypeBudget_rowIdentity
#print axioms cookLevinRichProjectionDischarge_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_retarget_noResidualProjectionEscape
#print axioms cookLevinRichProjectionDischarge_of_headSpan_headSpanProjection_concreteW_rowEmbeddings_checkedInputs_noResidualProjectionEscape

end PallLean.Paper93.Paper283
