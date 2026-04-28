import PallLean.Paper93.Paper283.RouteBProjectedPWindowAssembly

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
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

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

/-! ## Axiom audit anchors -/

#print axioms RouteBProjectedLogWindowFinalCertificate
#print axioms routeBProjectedLogWindowFinalCertificate_npPreservation
#print axioms false_of_routeBProjectedLogWindowFinalCertificate
#print axioms noBoundedSATDeciderAtPaperScale_of_routeBProjectedLogWindowFinalCertificates
#print axioms cookLevinRichProjectionDischarge_of_routeBProjectedLogWindowFinalCertificates
#print axioms routeBProjectedLogWindowFinalCertificate_of_projectedPWindowCover_npCertificate
#print axioms routeBProjectedLogWindowFinalCertificate_of_headSpan_zeroProfileQuotiented
#print axioms noBoundedSATDeciderAtPaperScale_of_headSpan_zeroProfileQuotiented
#print axioms cookLevinRichProjectionDischarge_of_headSpan_zeroProfileQuotiented

end PallLean.Paper93.Paper283
