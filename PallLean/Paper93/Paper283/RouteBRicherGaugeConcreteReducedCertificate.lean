import PallLean.Paper93.Paper283.RouteBRicherGaugeReducedCertificate

/-!
# Concrete reduced Route B certificate for richer finite-span gauges

This file packages the remaining concrete finite-span Route B obligations at
the surface consumed by
`routeBReducedCertificate_of_richerFiniteRows_eigenvalueFloor`.

The final gauge supplied to the reduced certificate is always the finite-row
candidate `routeBRicherFiniteRowsCandidateGauge`; this file does not use the
constants gauge, the `keepFOB` projection, or profile-generator transport.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open TuringMachine
open PaperFaithfulCompilation
open PaperFaithfulSeparation
open PallLean.Paper93.DeepMath.PathB

/-- Concrete finite-span Route B certificate after the reusable reductions in
`RouteBRicherGaugeReducedCertificate`.

The fields are the exact remaining inputs needed by
`routeBReducedCertificate_of_richerFiniteRows_eigenvalueFloor`: concrete
matrix/eigenvalue-floor data, finite-row rank, SPDP containment, a finite-span
cover of the unprojected P-window, and one embedded NP identity-minor witness
row with extraction and source lower-bound data. -/
structure RouteBRicherGaugeConcreteReducedCertificate
    (M : DTM) (n : Nat) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n) where
  N : Nat
  d : Nat
  alpha : Real
  beta : Real
  alpha0 : Real
  kappa : Nat
  gadgetN : Nat
  G : PallLean.Paper93.Concrete.RegularGraphFixed N d
  chi : TseitinCharge N
  Phi : Fin N -> Real
  theta : Real
  delta : Real
  rankLogRate : Real
  lambdaFloor : Real
  A : Matrix (Fin N) (Fin N) Real
  hA : A.PosSemidef
  spectralWindow : Finset (Fin N)
  rowCount : Nat
  rows : Fin rowCount -> SATDeciderGaugeSpace M n hn2 htb hns
  theta_pos : 0 < theta
  alpha_pos : 0 < alpha
  alpha0_pos : 0 < alpha0
  gadgetN_ge_two : 2 <= gadgetN
  rankLogRate_nonneg : 0 <= rankLogRate
  delta_le_rankLogRate_kappa : delta <= rankLogRate * (kappa : Real)
  lambdaFloor_nonneg : 0 <= lambdaFloor
  eigenvalue_floor :
    forall i, i ∈ spectralWindow -> lambdaFloor <= hA.1.eigenvalues i
  spectral_floor_budget :
    rankLogRate *
        ((∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
          (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN v).rank) :
          Real) <=
      (spectralWindow.card : Real) * Real.log (1 + theta * lambdaFloor)
  rowSpan_rank_le_matrix_rank :
    (Module.finrank Rat (finiteRowsSubmodule rows) : Real) <=
      (A.rank : Real)
  spdp_containment :
    RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
      (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
  p_window_cover :
    RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns
  Q : CoupledSheetPoly (flatCookLevinUVSplit M n hn2 htb hns)
  witness_row : Fin rowCount
  witness_row_eq_embed :
    rows witness_row =
      CoupledSheetPoly.embed (flatCookLevinUVSplit M n hn2 htb hns) Q
  extracts_compiled :
    routeBNFrameCandidateAsSATGauge M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)) =
      routeBNFrameCandidateAsSATGauge M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns rows)
        (CoupledSheetPoly.embed
          (flatCookLevinUVSplit M n hn2 htb hns) Q)
  source_lower_bound :
    SourceIdentityMinorLowerBound n
      (flatCookLevinUVSplit M n hn2 htb hns)
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n) Q

/-- The concrete finite-span certificate supplies the reduced Route B
certificate by feeding the finite-row constructor from
`RouteBRicherGaugeReducedCertificate`. -/
theorem routeBReducedCertificate_of_richerGaugeConcreteReducedCertificate
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (cert :
      RouteBRicherGaugeConcreteReducedCertificate M n hn2 htb hns) :
    RouteBReducedCertificate M n hn2 htb hns :=
  routeBReducedCertificate_of_richerFiniteRows_eigenvalueFloor
    (N := cert.N) (d := cert.d)
    M n hn2 htb hns
    cert.alpha cert.beta cert.alpha0 cert.kappa cert.gadgetN
    cert.G cert.chi cert.Phi
    (theta := cert.theta) (delta := cert.delta)
    (rankLogRate := cert.rankLogRate)
    (lambdaFloor := cert.lambdaFloor)
    cert.A cert.hA cert.spectralWindow cert.rows
    cert.theta_pos cert.alpha_pos cert.alpha0_pos cert.gadgetN_ge_two
    cert.rankLogRate_nonneg cert.delta_le_rankLogRate_kappa
    cert.lambdaFloor_nonneg cert.eigenvalue_floor cert.spectral_floor_budget
    cert.rowSpan_rank_le_matrix_rank cert.spdp_containment
    cert.p_window_cover cert.Q cert.witness_row cert.witness_row_eq_embed
    cert.extracts_compiled cert.source_lower_bound

/-- The concrete finite-span certificate reaches the final per-instance Route B
interface through the reduced certificate layer. -/
theorem routeBPerInstanceCertificate_of_richerGaugeConcreteReducedCertificate
    {M : DTM} {n : Nat} {hn2 : n >= 2}
    {htb : M.timeBound <= 4} {hns : M.numStates <= n}
    (cert :
      RouteBRicherGaugeConcreteReducedCertificate M n hn2 htb hns) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_reducedCertificate
    (routeBReducedCertificate_of_richerGaugeConcreteReducedCertificate cert)

/-! ## Axiom audit anchors -/

#print axioms routeBReducedCertificate_of_richerGaugeConcreteReducedCertificate
#print axioms routeBPerInstanceCertificate_of_richerGaugeConcreteReducedCertificate

end PallLean.Paper93.Paper283
