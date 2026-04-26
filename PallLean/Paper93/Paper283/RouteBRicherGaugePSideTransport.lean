import PallLean.Paper93.Paper283.RouteBTransportSPDPContainment

/-!
# Route B richer-gauge P-side transport

This file records reusable Route B criteria for an arbitrary richer
`NFrame.CandidateGauge` at the Cook-Levin dimension.  The criteria are
kernel-only and conditional on explicit linear-algebra inputs:

* generator-level commutation gives SPDP image containment;
* finite-span covers of the Cook-Levin P-window give projected or
  unprojected P-side rank bounds;
* SPDP image containment transports an unprojected P-side bound to the
  projected P-side bound by rank monotonicity.

No profile-collapse surface and no `keepFOB` projection is used as a source of
truth.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

/-- Generator-level commutation criterion for a richer Route B candidate.

For every Cook-Levin SPDP generator, applying the candidate projection before
forming the generator is the same as projecting the corresponding unprojected
generator.  This explicit commutation hypothesis is enough to place every
projected generator in the image of the unprojected SPDP subspace. -/
def RouteBRicherGaugeGeneratorCommutation
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)) : Prop :=
  forall (kappa ell : Nat)
    (p : MvPolynomial (Fin (RouteBCookLevinDim M n hn2 htb hns)) Rat)
    (S : List (Fin (RouteBCookLevinDim M n hn2 htb hns)))
    (m : MvPolynomial (Fin (RouteBCookLevinDim M n hn2 htb hns)) Rat),
    S.length = kappa ->
    m.totalDegree <= ell ->
    m.vars <= S.toFinset ->
    SPDP.isBlockAdmissible
      (cook_levin_compilation M n hn2 htb hns).partition S ->
    mlProj
        (m * SPDP.iterDerivList S
          ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) p)) =
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)
        (mlProj (m * SPDP.iterDerivList S p))

/-- Explicit subspace-containment criterion for a richer Route B candidate.

This is the direct SAT-decider specialization of the kernel criterion in
`SATDeciderGaugeRankMonotoneCriterion`, named here in Route B gauge language. -/
def RouteBRicherGaugeSPDPSubspaceContainment
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)) : Prop :=
  forall (kappa ell : Nat)
    (p : MvPolynomial (Fin (RouteBCookLevinDim M n hn2 htb hns)) Rat),
    mlBlockedSpdpSubspace
        (cook_levin_compilation M n hn2 htb hns).partition
        kappa ell
        ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) p) <=
      Submodule.map
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)
        (mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition kappa ell p)

/-- The unprojected Cook-Levin P-window subspace. -/
noncomputable abbrev routeBRicherGaugeUnprojectedPWindowSubspace
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) :
    Submodule Rat
      (MvPolynomial (Fin (RouteBCookLevinDim M n hn2 htb hns)) Rat) :=
  mlBlockedSpdpSubspace
    (cook_levin_compilation M n hn2 htb hns).partition
    (Nat.log 2 n) (Nat.log 2 n)
    (compiledPoly (cook_levin_compilation M n hn2 htb hns))

/-- The projected Cook-Levin P-window subspace for a richer candidate. -/
noncomputable abbrev routeBRicherGaugeProjectedPWindowSubspace
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)) :
    Submodule Rat
      (MvPolynomial (Fin (RouteBCookLevinDim M n hn2 htb hns)) Rat) :=
  mlBlockedSpdpSubspace
    (cook_levin_compilation M n hn2 htb hns).partition
    (Nat.log 2 n) (Nat.log 2 n)
    ((routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)
      (compiledPoly (cook_levin_compilation M n hn2 htb hns)))

/-- A finite-span cover of the unprojected P-window.  Supplying this data is
exactly enough to prove `RouteBSATUnprojectedPSideRankBound`. -/
structure RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) where
  span :
    Submodule Rat
      (MvPolynomial (Fin (RouteBCookLevinDim M n hn2 htb hns)) Rat)
  finite : Module.Finite Rat span
  contains :
    routeBRicherGaugeUnprojectedPWindowSubspace M n hn2 htb hns <= span
  rank_bound : Module.finrank Rat span <= n ^ 200

/-- A finite-span cover of the projected P-window for a selected richer
candidate.  Supplying this data is exactly enough to prove the projected
`SATDeciderGaugePSideBound` field directly. -/
structure RouteBRicherGaugeProjectedPWindowFiniteSpanCover
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)) where
  span :
    Submodule Rat
      (MvPolynomial (Fin (RouteBCookLevinDim M n hn2 htb hns)) Rat)
  finite : Module.Finite Rat span
  contains :
    routeBRicherGaugeProjectedPWindowSubspace M n hn2 htb hns Pi <= span
  rank_bound : Module.finrank Rat span <= n ^ 200

/-- Generator commutation supplies the existing generator-image transport
criterion for the richer candidate. -/
theorem routeBRicherGauge_generatorImageTransport_of_generatorCommutation
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hcomm :
      RouteBRicherGaugeGeneratorCommutation M n hn2 htb hns Pi) :
    RouteBSPDPGeneratorImageTransport M n hn2 htb hns Pi := by
  intro kappa ell p S m hSlen hmdeg hmvars hadm
  refine
    ⟨mlProj (m * SPDP.iterDerivList S p),
      Submodule.subset_span ⟨S, m, hSlen, hmdeg, hmvars, hadm, rfl⟩, ?_⟩
  exact (hcomm kappa ell p S m hSlen hmdeg hmvars hadm).symm

/-- Generator commutation proves the SPDP image-containment field for the
richer candidate. -/
theorem routeBRicherGauge_spdpImageContainment_of_generatorCommutation
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hcomm :
      RouteBRicherGaugeGeneratorCommutation M n hn2 htb hns Pi) :
    SATDeciderGaugeSPDPSubspaceImageContainment M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) :=
  routeBSPDPImageContainment_of_generatorImageTransport
    M n hn2 htb hns Pi
    (routeBRicherGauge_generatorImageTransport_of_generatorCommutation
      M n hn2 htb hns Pi hcomm)

/-- A direct subspace-containment hypothesis is exactly the SPDP
image-containment field consumed downstream. -/
theorem routeBRicherGauge_spdpImageContainment_of_subspaceContainment
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hcontain :
      RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns Pi) :
    SATDeciderGaugeSPDPSubspaceImageContainment M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) :=
  hcontain

/-- A finite-span cover of the unprojected P-window proves the flat
Cook-Levin P-side rank bound. -/
theorem routeBRicherGauge_unprojectedPSideRankBound_of_finiteSpanCover
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns) :
    RouteBSATUnprojectedPSideRankBound M n hn2 htb hns := by
  unfold RouteBSATUnprojectedPSideRankBound mlBlockedSpdpRank
  letI := cover.finite
  exact le_trans (Submodule.finrank_mono cover.contains) cover.rank_bound

/-- A finite-span cover of the projected P-window proves the projected P-side
field directly, without using the unprojected P-side route. -/
theorem routeBRicherGauge_projectedPSideBound_of_projectedFiniteSpanCover
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (cover :
      RouteBRicherGaugeProjectedPWindowFiniteSpanCover
        M n hn2 htb hns Pi) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) := by
  unfold SATDeciderGaugePSideBound mlBlockedSpdpRank
  letI := cover.finite
  exact le_trans (Submodule.finrank_mono cover.contains) cover.rank_bound

/-- SPDP image containment transports an unprojected P-side bound to the
projected P-side field for the richer candidate. -/
theorem routeBRicherGauge_projectedPSideBound_of_spdpContainment
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hcontain :
      SATDeciderGaugeSPDPSubspaceImageContainment M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi))
    (hunprojected :
      RouteBSATUnprojectedPSideRankBound M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) :=
  satDeciderGaugePSideBound_of_rankMonotone_of_unprojected_bound
    M n hn2 htb hns
    (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)
    (satDeciderGaugeRankMonotonicity_of_spdpSubspaceImageContainment
      M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)
      hcontain)
    hunprojected

/-- Generator commutation and a finite-span cover of the unprojected P-window
prove the projected P-side field by the monotonicity route. -/
theorem routeBRicherGauge_projectedPSideBound_of_commutation_finiteSpanCover
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hcomm :
      RouteBRicherGaugeGeneratorCommutation M n hn2 htb hns Pi)
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) :=
  routeBRicherGauge_projectedPSideBound_of_spdpContainment
    M n hn2 htb hns Pi
    (routeBRicherGauge_spdpImageContainment_of_generatorCommutation
      M n hn2 htb hns Pi hcomm)
    (routeBRicherGauge_unprojectedPSideRankBound_of_finiteSpanCover
      M n hn2 htb hns cover)

/-- Direct SPDP subspace containment and a finite-span cover of the
unprojected P-window prove the projected P-side field. -/
theorem routeBRicherGauge_projectedPSideBound_of_subspaceContainment_finiteSpanCover
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hcontain :
      RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns Pi)
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns) :
    SATDeciderGaugePSideBound M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi) :=
  routeBRicherGauge_projectedPSideBound_of_spdpContainment
    M n hn2 htb hns Pi
    (routeBRicherGauge_spdpImageContainment_of_subspaceContainment
      M n hn2 htb hns Pi hcontain)
    (routeBRicherGauge_unprojectedPSideRankBound_of_finiteSpanCover
      M n hn2 htb hns cover)

/-- The primitive Route B transport certificate follows from direct SPDP
subspace containment, an unprojected P-window finite-span cover, and the
separate projected NP identity-minor lower bound. -/
theorem routeBRicherGauge_transportCertificate_of_subspaceContainment_finiteSpanCover
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hcontain :
      RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns Pi)
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns)
    (hNP :
      RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)) :
    RouteBFunctorialTransportCertificate M n hn2 htb hns Pi :=
  { image_containment :=
      routeBRicherGauge_spdpImageContainment_of_subspaceContainment
        M n hn2 htb hns Pi hcontain
    unprojected_p_side_rank_bound :=
      routeBRicherGauge_unprojectedPSideRankBound_of_finiteSpanCover
        M n hn2 htb hns cover
    projected_np_identity_minor_lower_bound := hNP }

/-- The primitive Route B transport certificate follows from generator
commutation, an unprojected P-window finite-span cover, and the separate
projected NP identity-minor lower bound. -/
theorem routeBRicherGauge_transportCertificate_of_commutation_finiteSpanCover
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hcomm :
      RouteBRicherGaugeGeneratorCommutation M n hn2 htb hns Pi)
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns)
    (hNP :
      RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)) :
    RouteBFunctorialTransportCertificate M n hn2 htb hns Pi :=
  { image_containment :=
      routeBRicherGauge_spdpImageContainment_of_generatorCommutation
        M n hn2 htb hns Pi hcomm
    unprojected_p_side_rank_bound :=
      routeBRicherGauge_unprojectedPSideRankBound_of_finiteSpanCover
        M n hn2 htb hns cover
    projected_np_identity_minor_lower_bound := hNP }

/-! ## Axiom audit anchors -/

#print axioms routeBRicherGauge_generatorImageTransport_of_generatorCommutation
#print axioms routeBRicherGauge_spdpImageContainment_of_generatorCommutation
#print axioms routeBRicherGauge_spdpImageContainment_of_subspaceContainment
#print axioms routeBRicherGauge_unprojectedPSideRankBound_of_finiteSpanCover
#print axioms routeBRicherGauge_projectedPSideBound_of_projectedFiniteSpanCover
#print axioms routeBRicherGauge_projectedPSideBound_of_spdpContainment
#print axioms routeBRicherGauge_projectedPSideBound_of_commutation_finiteSpanCover
#print axioms routeBRicherGauge_projectedPSideBound_of_subspaceContainment_finiteSpanCover
#print axioms routeBRicherGauge_transportCertificate_of_subspaceContainment_finiteSpanCover
#print axioms routeBRicherGauge_transportCertificate_of_commutation_finiteSpanCover

end PallLean.Paper93.Paper283
