import PallLean.Paper93.Paper283.RouteBExplicitComplementProjectionPolicyProgress
import PallLean.Paper93.Paper283.RouteBRicherGaugeReducedCertificate

/-!
# Route B reduced certificates for explicit-complement gauges

The explicit first-square-avoiding complement policy should not have to pass
through the arbitrary selected finite-row projection.  This file connects the
explicit with-complement gauge directly to the reduced Route B certificate
surface.

The hard projection obligation remains `KernelGeneratorZeroWithComplement`.
Once that is supplied, the SPDP side is available for the explicit gauge
itself; the remaining matrix/rank/P-window/NP inputs are the same reduced
certificate inputs as before.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open TuringMachine
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open PallLean.Paper93.DeepMath.PathB

attribute [local instance] Classical.dec

/-- The explicit-complement gauge is admissible at the current NFrame surface. -/
theorem routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement_admissible
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C) :
    PallLean.Paper93.NFrame.AdmissibleGauge
      (routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement
        M n hn2 htb hns C hC) := by
  unfold PallLean.Paper93.NFrame.AdmissibleGauge
  exact ⟨0, by simp⟩

/-- The explicit-complement gauge has the same projection rank as the concrete
prepended multilinear finite-row span. -/
theorem routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement_projectionRank_eq_spanFinrank
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C) :
    PallLean.Paper93.Concrete.projectionRank
        (routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement
          M n hn2 htb hns C hC) =
      (Module.finrank Rat
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns)) : Real) := by
  unfold PallLean.Paper93.Concrete.projectionRank
  rw [show
      LinearMap.range
          (routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement
            M n hn2 htb hns C hC).projection =
        finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns) by
    simpa [routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement,
      routeBRicherFiniteRowsCandidateGaugeWithComplement] using
      routeBRicherFiniteRowsCandidateGaugeWithComplement_range
        M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearRows M n hn2 htb hns)
        C hC]

/-- Rank compatibility for the explicit-complement gauge follows from the
finite-row span rank budget. -/
theorem routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement_rankCompatible_of_spanFinrank_le
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (rankA : Nat)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (hrank :
      (Module.finrank Rat
          (finiteRowsSubmodule
            (routeBRicherConcreteNPPrependedMultilinearRows
              M n hn2 htb hns)) : Real) <=
        (rankA : Real)) :
    RouteBProjectionRankCompatible M n hn2 htb hns rankA
      (routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement
        M n hn2 htb hns C hC) := by
  unfold RouteBProjectionRankCompatible
  rw [
    routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement_projectionRank_eq_spanFinrank
      M n hn2 htb hns C hC]
  exact hrank

/-- Primitive transport certificate for the explicit-complement gauge. -/
theorem routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement_transportCertificate
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (hcontain :
      RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement
          M n hn2 htb hns C hC))
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns)
    (hNP :
      RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement
            M n hn2 htb hns C hC))) :
    RouteBFunctorialTransportCertificate M n hn2 htb hns
      (routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement
        M n hn2 htb hns C hC) :=
  routeBRicherGauge_transportCertificate_of_subspaceContainment_finiteSpanCover
    M n hn2 htb hns
    (routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement
      M n hn2 htb hns C hC)
    hcontain cover hNP

/-- Reduced Route B certificate constructor for the explicit-complement gauge,
using direct SPDP containment for that same gauge. -/
theorem routeBReducedCertificate_of_richerConcreteNPWithComplement_eigenvalueFloor
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {theta delta rankLogRate lambdaFloor : Real}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (S : Finset (Fin N))
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hgadgetN : 2 <= gadgetN)
    (hrate_nonneg : 0 <= rankLogRate)
    (hdelta_rate : delta <= rankLogRate * (kappa : Real))
    (hlambdaFloor_nonneg : 0 <= lambdaFloor)
    (hfloor : forall i, i ∈ S -> lambdaFloor <= hA.1.eigenvalues i)
    (hbudget :
      rankLogRate *
          ((∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
            (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN v).rank) :
            Real) <=
        (S.card : Real) * Real.log (1 + theta * lambdaFloor))
    (hrank :
      (Module.finrank Rat
          (finiteRowsSubmodule
            (routeBRicherConcreteNPPrependedMultilinearRows
              M n hn2 htb hns)) : Real) <=
        (A.rank : Real))
    (hcontain :
      RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
        (routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement
          M n hn2 htb hns C hC))
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns)
    (hNP :
      RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement
            M n hn2 htb hns C hC))) :
    RouteBReducedCertificate M n hn2 htb hns := by
  refine
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, delta, rankLogRate, A, hA,
      routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement
        M n hn2 htb hns C hC,
      htheta, halpha, halpha0, hgadgetN, ?_, ?_, ?_, ?_⟩
  · exact
      bridgeA_rankLogDetLowerHypotheses_of_shifted_logdet_eigenvalue_floor_on_finset
        alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        A hA S htheta hrate_nonneg hdelta_rate hlambdaFloor_nonneg
        hfloor hbudget
  · exact
      routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement_admissible
        M n hn2 htb hns C hC
  · exact
      routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement_rankCompatible_of_spanFinrank_le
        M n hn2 htb hns A.rank C hC hrank
  · exact
      routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement_transportCertificate
        M n hn2 htb hns C hC hcontain cover hNP

/-- Reduced Route B certificate constructor for the explicit-complement gauge
using the local generator-zero frontier on the chosen complement. -/
theorem routeBReducedCertificate_of_richerConcreteNPWithComplement_kernelGeneratorZero_eigenvalueFloor
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {theta delta rankLogRate lambdaFloor : Real}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (S : Finset (Fin N))
    (C : Submodule Rat (SATDeciderGaugeSpace M n hn2 htb hns))
    (hC :
      IsCompl
        (finiteRowsSubmodule
          (routeBRicherConcreteNPPrependedMultilinearRows
            M n hn2 htb hns))
        C)
    (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hgadgetN : 2 <= gadgetN)
    (hrate_nonneg : 0 <= rankLogRate)
    (hdelta_rate : delta <= rankLogRate * (kappa : Real))
    (hlambdaFloor_nonneg : 0 <= lambdaFloor)
    (hfloor : forall i, i ∈ S -> lambdaFloor <= hA.1.eigenvalues i)
    (hbudget :
      rankLogRate *
          ((∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
            (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN v).rank) :
            Real) <=
        (S.card : Real) * Real.log (1 + theta * lambdaFloor))
    (hrank :
      (Module.finrank Rat
          (finiteRowsSubmodule
            (routeBRicherConcreteNPPrependedMultilinearRows
              M n hn2 htb hns)) : Real) <=
        (A.rank : Real))
    (hzero :
      RouteBRicherConcreteNPPrependedMultilinearKernelGeneratorZeroWithComplement
        M n hn2 htb hns C hC)
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns)
    (hNP :
      RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement
            M n hn2 htb hns C hC))) :
    RouteBReducedCertificate M n hn2 htb hns :=
  routeBReducedCertificate_of_richerConcreteNPWithComplement_eigenvalueFloor
    M n hn2 htb hns alpha beta alpha0 kappa gadgetN G chi Phi
    A hA S C hC htheta halpha halpha0 hgadgetN hrate_nonneg
    hdelta_rate hlambdaFloor_nonneg hfloor hbudget hrank
    (routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement_spdpSubspaceContainment_of_kernelGenerator_zeroWithComplement
      M n hn2 htb hns C hC hzero)
    cover hNP

/-! ## Axiom audit anchors -/

#print axioms routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement_admissible
#print axioms routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement_projectionRank_eq_spanFinrank
#print axioms routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement_rankCompatible_of_spanFinrank_le
#print axioms routeBRicherConcreteNPPrependedMultilinearGaugeWithComplement_transportCertificate
#print axioms routeBReducedCertificate_of_richerConcreteNPWithComplement_eigenvalueFloor
#print axioms routeBReducedCertificate_of_richerConcreteNPWithComplement_kernelGeneratorZero_eigenvalueFloor

end PallLean.Paper93.Paper283
