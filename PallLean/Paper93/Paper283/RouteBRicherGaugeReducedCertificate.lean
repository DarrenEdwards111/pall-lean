import PallLean.Paper93.Paper283.RouteBReducedCertificate
import PallLean.Paper93.Paper283.RouteBRicherGaugeFiniteSpan
import PallLean.Paper93.Paper283.RouteBRicherGaugeNPTransport
import PallLean.Paper93.Paper283.RouteBRicherGaugePSideTransport
import PallLean.Paper93.Paper283.RouteBBridgeASpectralLower

/-!
# Route B reduced certificates from richer finite-span gauges

This file connects the new Route B pieces:

* finite-span `NFrame.CandidateGauge`s;
* Bridge A shifted-logdet lower bounds from eigenvalue floors;
* richer-gauge SPDP/P-side transport;
* finite-row NP identity-minor transport.

The result is a direct constructor for `RouteBReducedCertificate`.  The theorem
does not assert the concrete Cook-Levin witness rows or spectral floor; those
remain the explicit mathematical inputs.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

/-- Every finite-row Route B candidate is admissible for the current NFrame
API.  The present admissibility predicate only requires `0` to lie in the
projection range, which holds for any linear projection. -/
theorem routeBRicherFiniteRowsCandidateGauge_admissible
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    PallLean.Paper93.NFrame.AdmissibleGauge
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows) := by
  unfold PallLean.Paper93.NFrame.AdmissibleGauge
  exact ⟨0, by simp⟩

/-- The projection rank of the finite-row candidate is the finrank of the row
span it projects onto. -/
theorem routeBRicherFiniteRowsCandidateGauge_projectionRank_eq_spanFinrank
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns) :
    PallLean.Paper93.Concrete.projectionRank
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows) =
      (Module.finrank Rat (finiteRowsSubmodule rows) : Real) := by
  unfold PallLean.Paper93.Concrete.projectionRank
  rw [routeBRicherFiniteRowsCandidateGauge_range]

/-- Rank-compatibility constructor for a finite-row Route B candidate. -/
theorem routeBRicherFiniteRowsCandidateGauge_rankCompatible_of_spanFinrank_le
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (rankA : Nat)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hrank :
      (Module.finrank Rat (finiteRowsSubmodule rows) : Real) <=
        (rankA : Real)) :
    RouteBProjectionRankCompatible M n hn2 htb hns rankA
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows) := by
  unfold RouteBProjectionRankCompatible
  rw [routeBRicherFiniteRowsCandidateGauge_projectionRank_eq_spanFinrank]
  exact hrank

/-- Transport certificate for the finite-row candidate from direct SPDP
containment, an unprojected P-window finite-span cover, and the finite-row
fixed-embed NP certificate data. -/
theorem routeBRicherFiniteRowsCandidateGauge_transportCertificate
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
    (hcontain :
      RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows))
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (i : Fin m)
    (hrow :
      rows i =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q) :
    RouteBFunctorialTransportCertificate M n hn2 htb hns
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows) := by
  have hNP :
      RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
        (routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)) := by
    exact
      routeBSATProjectedNPIdentityMinorLowerBound_of_fixed_embed_certificate
        M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
        (routeBRicherFiniteRowsCandidateGauge_npIdentityMinorFixedEmbedCertificate
          M n hn2 htb hns rows i Q hrow hextract hsource)
  exact
    routeBRicherGauge_transportCertificate_of_subspaceContainment_finiteSpanCover
      M n hn2 htb hns
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
      hcontain cover hNP

/-- End-to-end reduced Route B certificate constructor for the finite-row
candidate, using the Bridge A eigenvalue-floor lower-bound criterion.

The remaining assumptions are now the concrete Route B data:
the spectral floor/budget, a rank budget for the finite row span, SPDP image
containment, the P-window cover, and the fixed-row NP identity-minor data. -/
theorem routeBReducedCertificate_of_richerFiniteRows_eigenvalueFloor
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {theta delta rankLogRate lambdaFloor : Real}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (S : Finset (Fin N))
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
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
      (Module.finrank Rat (finiteRowsSubmodule rows) : Real) <=
        (A.rank : Real))
    (hcontain :
      RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows))
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (i : Fin m)
    (hrow :
      rows i =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q) :
    RouteBReducedCertificate M n hn2 htb hns := by
  refine
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, delta, rankLogRate, A, hA,
      routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows,
      htheta, halpha, halpha0, hgadgetN, ?_, ?_, ?_, ?_⟩
  · exact
      bridgeA_rankLogDetLowerHypotheses_of_shifted_logdet_eigenvalue_floor_on_finset
        alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        A hA S htheta hrate_nonneg hdelta_rate hlambdaFloor_nonneg
        hfloor hbudget
  · exact
      routeBRicherFiniteRowsCandidateGauge_admissible M n hn2 htb hns rows
  · exact
      routeBRicherFiniteRowsCandidateGauge_rankCompatible_of_spanFinrank_le
        M n hn2 htb hns A.rank rows hrank
  · exact
      routeBRicherFiniteRowsCandidateGauge_transportCertificate
        M n hn2 htb hns rows hcontain cover Q i hrow hextract hsource

/-- End-to-end Route B per-instance certificate constructor for the same
finite-row/eigenvalue-floor surface.  This is just the reduced certificate
above promoted through `routeBPerInstanceCertificate_of_reducedCertificate`,
so downstream work can stay on the many-row/windowed finite-span interface
without re-entering the one-local-block Bridge A adapter. -/
theorem routeBPerInstanceCertificate_of_richerFiniteRows_eigenvalueFloor
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {theta delta rankLogRate lambdaFloor : Real}
    (A : Matrix (Fin N) (Fin N) Real) (hA : A.PosSemidef)
    (S : Finset (Fin N))
    {m : Nat}
    (rows : Fin m -> SATDeciderGaugeSpace M n hn2 htb hns)
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
      (Module.finrank Rat (finiteRowsSubmodule rows) : Real) <=
        (A.rank : Real))
    (hcontain :
      RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows))
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns)
    (Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns))
    (i : Fin m)
    (hrow :
      rows i =
        CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q)
    (hextract :
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
        routeBNFrameCandidateAsSATGauge M n hn2 htb hns
          (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
          (CoupledSheetPoly.embed
            (flatCookLevinUVSplit M n hn2 htb hns) Q))
    (hsource :
      SourceIdentityMinorLowerBound n
        (flatCookLevinUVSplit M n hn2 htb hns)
        (cook_levin_compilation M n hn2 htb hns).partition
        (Nat.log 2 n) (Nat.log 2 n) Q) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_reducedCertificate
    (routeBReducedCertificate_of_richerFiniteRows_eigenvalueFloor
      M n hn2 htb hns alpha beta alpha0 kappa gadgetN G chi Phi
      A hA S rows htheta halpha halpha0 hgadgetN hrate_nonneg
      hdelta_rate hlambdaFloor_nonneg hfloor hbudget hrank hcontain cover
      Q i hrow hextract hsource)

/-! ## Axiom audit anchors -/

#print axioms routeBRicherFiniteRowsCandidateGauge_admissible
#print axioms routeBRicherFiniteRowsCandidateGauge_projectionRank_eq_spanFinrank
#print axioms routeBRicherFiniteRowsCandidateGauge_rankCompatible_of_spanFinrank_le
#print axioms routeBRicherFiniteRowsCandidateGauge_transportCertificate
#print axioms routeBReducedCertificate_of_richerFiniteRows_eigenvalueFloor
#print axioms routeBPerInstanceCertificate_of_richerFiniteRows_eigenvalueFloor

end PallLean.Paper93.Paper283
