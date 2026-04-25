import PallLean.Paper93.Paper283.RouteBFunctorialTransportCertificate
import PallLean.Paper93.DeepMath.PathB.ProjectedNPIdentityPreservationProgress

/-!
# Route B transport for the projected NP identity-minor field

This file isolates the Route B/Paper283 wrapper around the existing
paper-faithful fixed-embed criterion for projected NP identity minors.

The point is deliberately narrow: for a selected NFrame candidate `Pi`, an
embedded source obstruction fixed by the induced SAT gauge, an extraction
identity for the compiled Cook-Levin polynomial, and a source lower bound give
the exact `RouteBSATProjectedNPIdentityMinorLowerBound` field required by the
Route B transport certificate.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

/-- Fixed-embed/extraction/source certificate for the Route B projected
NP identity-minor lower-bound field.

This is the Route B-facing version of the paper-faithful criterion: the
selected NFrame candidate, viewed as a SAT gauge, fixes an embedded coupled
sheet `Q`; the compiled Cook-Levin polynomial extracts to that fixed image;
and `Q` carries the source identity-minor lower bound. -/
structure RouteBNPIdentityMinorFixedEmbedCertificate
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)) : Type where
  Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns)
  fixed_embed :
    routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi
        (CoupledSheetPoly.embed
          (flatCookLevinUVSplit M n hn2 htb hns) Q) =
      CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q
  extracts_compiled :
    routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi
        (CoupledSheetPoly.embed
          (flatCookLevinUVSplit M n hn2 htb hns) Q)
  source_lower_bound :
    SourceIdentityMinorLowerBound n
      (flatCookLevinUVSplit M n hn2 htb hns)
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n) Q

/-- Direct Route B projected NP lower-bound reduction from the reusable
fixed-embed, extraction, and source lower-bound hypotheses. -/
theorem routeBSATProjectedNPIdentityMinorLowerBound_of_fixed_embed_extraction_source
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (hfix :
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) Q) =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q) :
    RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) :=
  flatProjectedCompiledLowerBound_of_fixed_embed_extraction_source
    M n hn2 htb hns Q
    (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)
    hfix hextract hsource

/-- Certificate form of
`routeBSATProjectedNPIdentityMinorLowerBound_of_fixed_embed_extraction_source`.
-/
theorem routeBSATProjectedNPIdentityMinorLowerBound_of_fixed_embed_certificate
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hcert :
      RouteBNPIdentityMinorFixedEmbedCertificate M n hn2 htb hns Pi) :
    RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) := by
  rcases hcert with ⟨Q, hfix, hextract, hsource⟩
  exact
    routeBSATProjectedNPIdentityMinorLowerBound_of_fixed_embed_extraction_source
      M n hn2 htb hns Pi Q hfix hextract hsource

/-- The fixed-embed certificate supplies the NP component of the primitive
Route B transport certificate, once the image-containment and P-side fields
are supplied separately. -/
theorem routeBFunctorialTransportCertificate_of_npIdentityMinorFixedEmbedCertificate
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (himage :
      SATDeciderGaugeSPDPSubspaceImageContainment M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi))
    (hpside :
      RouteBSATUnprojectedPSideRankBound M n hn2 htb hns)
    (hcert :
      RouteBNPIdentityMinorFixedEmbedCertificate M n hn2 htb hns Pi) :
    RouteBFunctorialTransportCertificate M n hn2 htb hns Pi :=
  { image_containment := himage
    unprojected_p_side_rank_bound := hpside
    projected_np_identity_minor_lower_bound :=
      routeBSATProjectedNPIdentityMinorLowerBound_of_fixed_embed_certificate
        M n hn2 htb hns Pi hcert }

/-- With the other two primitive transport obligations fixed, the
fixed-embed certificate discharges all Route B NFrame SAT subgoals for the
selected projection. -/
theorem routeBNFrameGaugeSubgoals_of_npIdentityMinorFixedEmbedCertificate
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (himage :
      SATDeciderGaugeSPDPSubspaceImageContainment M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi))
    (hpside :
      RouteBSATUnprojectedPSideRankBound M n hn2 htb hns)
    (hcert :
      RouteBNPIdentityMinorFixedEmbedCertificate M n hn2 htb hns Pi) :
    RouteBNFrameGaugeSubgoals M n hn2 htb hns Pi :=
  routeBNFrameGaugeSubgoals_of_transportCertificate
    M n hn2 htb hns Pi
    (routeBFunctorialTransportCertificate_of_npIdentityMinorFixedEmbedCertificate
      M n hn2 htb hns Pi himage hpside hcert)

/-! ## Axiom audit anchors -/

#print axioms routeBSATProjectedNPIdentityMinorLowerBound_of_fixed_embed_extraction_source
#print axioms routeBSATProjectedNPIdentityMinorLowerBound_of_fixed_embed_certificate
#print axioms routeBFunctorialTransportCertificate_of_npIdentityMinorFixedEmbedCertificate
#print axioms routeBNFrameGaugeSubgoals_of_npIdentityMinorFixedEmbedCertificate

end PallLean.Paper93.Paper283
