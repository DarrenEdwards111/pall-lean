import PallLean.Paper93.Paper283.RouteBStrictMatrixCertificate

/-!
# Route B matrix-to-SAT functoriality with rank-narrowed NP input

This file isolates one smaller Route B functoriality package.  The existing
`RouteBMatrixToSATGaugeFunctoriality` asks the NP identity-minor transport to
consume the full projection-rank compatibility hypothesis.  The wrapper below
only asks that NP transport to consume the concrete nonnegative projection-rank
consequence; the full compatibility hypothesis is still available to the
P-side transport and is used to derive the NP side condition.

No profile-collapse, `keepFOB`, or adapter content is used here.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open MultilinearSPDP
open PaperFaithfulSeparation
open TuringMachine
open PallLean.Paper93.DeepMath.PathB

/-- Rank-narrowed Route B matrix-to-SAT functoriality package.

Compared with `RouteBMatrixToSATGaugeFunctoriality`, the NP identity-minor
field only receives the nonnegative projection-rank consequence.  The bridge
back to the older package derives that consequence from
`RouteBProjectionRankCompatible`. -/
structure RouteBMatrixToSATGaugeRankNarrowFunctoriality {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : forall v : Fin N, LocalGadget N v)
    (capacity delta : Real) (rankA : Nat)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)) : Prop where
  spdp_image_containment :
    SATDeciderGaugeSPDPSubspaceImageContainment M n hn2 htb hns
      (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)
  pSide_of_routeB_rank :
    RouteBAnalyticRankCoreOutput
        alpha beta alpha0 kappa G chi Phi gadgetFamily capacity delta rankA ->
      RouteBProjectionRankCompatible M n hn2 htb hns rankA Pi ->
        RouteBSATUnprojectedPSideRankBound M n hn2 htb hns
  npIdentityMinor_of_routeB_rank_nonneg :
    RouteBAnalyticRankCoreOutput
        alpha beta alpha0 kappa G chi Phi gadgetFamily capacity delta rankA ->
      0 <= PallLean.Paper93.Concrete.projectionRank Pi ->
        RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
          (routeBNFrameCandidateAsSATGauge M n hn2 htb hns Pi)

/-- The rank-narrowed functoriality package constructs the existing
`RouteBMatrixToSATGaugeFunctoriality` package by deriving the NP field's
nonnegative rank input from `RouteBProjectionRankCompatible`. -/
theorem routeBMatrixToSATGaugeFunctoriality_of_rankNarrowFunctoriality
    {N d : Nat}
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (gadgetFamily : forall v : Fin N, LocalGadget N v)
    (capacity delta : Real) (rankA : Nat)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hfun :
      RouteBMatrixToSATGaugeRankNarrowFunctoriality
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
        capacity delta rankA Pi) :
    RouteBMatrixToSATGaugeFunctoriality
      M n hn2 htb hns alpha beta alpha0 kappa G chi Phi gadgetFamily
      capacity delta rankA Pi := by
  refine
    { spdp_image_containment := hfun.spdp_image_containment
      pSide_of_routeB_rank := ?_
      npIdentityMinor_of_routeB_rank := ?_ }
  · intro hanalytic hcompat
    exact hfun.pSide_of_routeB_rank hanalytic hcompat
  · intro hanalytic hcompat
    exact hfun.npIdentityMinor_of_routeB_rank_nonneg hanalytic
      (projectionRank_nonneg_of_routeBProjectionRankCompatible
        M n hn2 htb hns rankA Pi hcompat)

/-- Strict matrix certificate variant using the rank-narrowed functoriality
package.  This keeps the analytic and matrix-side fields identical to
`RouteBStrictMatrixCertificate`, changing only the functoriality hypothesis. -/
def RouteBStrictMatrixRankNarrowCertificate
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) : Prop :=
  exists (N d : Nat)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (theta normBound delta rankLogRate : Real)
    (A : Matrix (Fin N) (Fin N) Real)
    (hA : A.PosSemidef)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns)),
    exists htheta : 0 < theta,
      0 < alpha /\ 0 < alpha0 /\ 2 <= gadgetN /\
      0 < normBound /\
      (forall i,
        (one_add_smul_posSemidef_posDef_of_pos A hA htheta).1.eigenvalues i =
          1 + theta * hA.1.eigenvalues i) /\
      (forall i, hA.1.eigenvalues i <= normBound) /\
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        rankLogRate
        (Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det))
        delta /\
      PallLean.Paper93.NFrame.AdmissibleGauge Pi /\
      RouteBProjectionRankCompatible M n hn2 htb hns A.rank Pi /\
      RouteBMatrixToSATGaugeRankNarrowFunctoriality
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        (bridgeBLogCapacity theta normBound) delta A.rank Pi

/-- A strict rank-narrowed certificate supplies the existing strict Route B
matrix certificate. -/
theorem routeBStrictMatrixCertificate_of_rankNarrowCertificate
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (cert : RouteBStrictMatrixRankNarrowCertificate M n hn2 htb hns) :
    RouteBStrictMatrixCertificate M n hn2 htb hns := by
  rcases cert with
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, normBound, delta, rankLogRate, A, hA, Pi,
      htheta, halpha, halpha0, hgadgetN, hnorm,
      hshift_eigs, heigs_bound, hlower, hAdm, hcompat, hfun⟩
  exact
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, normBound, delta, rankLogRate, A, hA, Pi,
      htheta, halpha, halpha0, hgadgetN, hnorm,
      hshift_eigs, heigs_bound, hlower, hAdm, hcompat,
      routeBMatrixToSATGaugeFunctoriality_of_rankNarrowFunctoriality
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        (bridgeBLogCapacity theta normBound) delta A.rank Pi hfun⟩

/-- Rank-narrowed strict certificates supply the generic Route B per-instance
certificate through the existing strict certificate bridge. -/
theorem routeBPerInstanceCertificate_of_rankNarrowCertificate
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (cert : RouteBStrictMatrixRankNarrowCertificate M n hn2 htb hns) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_strictMatrixCertificate
    (routeBStrictMatrixCertificate_of_rankNarrowCertificate cert)

/-! ## Axiom audit anchors -/

#print axioms routeBMatrixToSATGaugeFunctoriality_of_rankNarrowFunctoriality
#print axioms routeBStrictMatrixCertificate_of_rankNarrowCertificate
#print axioms routeBPerInstanceCertificate_of_rankNarrowCertificate

end PallLean.Paper93.Paper283
