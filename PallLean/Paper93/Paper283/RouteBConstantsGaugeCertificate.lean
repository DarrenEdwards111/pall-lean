import PallLean.Paper93.Paper283.RouteBReducedCertificate
import PallLean.Paper93.Paper283.RouteBGaugeCandidate

/-!
# Route B certificate specialised to the concrete constants gauge

`RouteBGaugeCandidate` constructs the current unconditional nonzero N-frame
candidate at the Cook-Levin dimension: the constants projection.  This file
specialises the reduced Route B certificate to that candidate and discharges
the raw `AdmissibleGauge` field with the candidate theorem.

This is not a claim that the constants projection is the final paper `Π⋆`.
It is the strongest full finite-range N-frame candidate currently present in
the repository, and it exposes the exact remaining obligations for that
candidate: rank compatibility and primitive SAT-side transport.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open TuringMachine
open PaperFaithfulSeparation
open PallLean.Paper93.DeepMath.PathB

/-- The concrete constants N-frame gauge at the Cook-Levin Route B dimension. -/
noncomputable abbrev routeBConstantsGauge
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns) :=
  routeBConstantsCandidateGauge M n hn2 htb hns

/-- The constants gauge is admissible for the current full N-frame
`AdmissibleGauge` predicate. -/
theorem routeBConstantsGauge_admissible
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    PallLean.Paper93.NFrame.AdmissibleGauge
      (routeBConstantsGauge M n hn2 htb hns) := by
  exact routeBConstantsCandidateGauge_admissible M n hn2 htb hns

/-- Route B reduced certificate with `Pi` fixed to the concrete constants
gauge.  The gauge and admissibility fields are no longer inputs. -/
def RouteBConstantsGaugeReducedCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (N d : Nat)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (theta delta rankLogRate : Real)
    (A : Matrix (Fin N) (Fin N) Real)
    (_hA : A.PosSemidef),
    ∃ _htheta : 0 < theta,
      0 < alpha ∧ 0 < alpha0 ∧ 2 <= gadgetN ∧
      BridgeARankLogDetLowerHypotheses
        alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        rankLogRate
        (Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det))
        delta ∧
      RouteBProjectionRankCompatible M n hn2 htb hns A.rank
        (routeBConstantsGauge M n hn2 htb hns) ∧
      RouteBFunctorialTransportCertificate M n hn2 htb hns
        (routeBConstantsGauge M n hn2 htb hns)

/-- Constants-gauge certificates supply the reduced Route B
certificate by filling the concrete gauge and its admissibility proof. -/
theorem routeBReducedCertificate_of_constantsGauge
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (cert :
      RouteBConstantsGaugeReducedCertificate M n hn2 htb hns) :
    RouteBReducedCertificate M n hn2 htb hns := by
  rcases cert with
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, delta, rankLogRate, A, hA,
      htheta, halpha, halpha0, hgadgetN,
      hlower, hcompat, htransport⟩
  exact
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, delta, rankLogRate, A, hA,
      routeBConstantsGauge M n hn2 htb hns,
      htheta, halpha, halpha0, hgadgetN, hlower,
      routeBConstantsGauge_admissible M n hn2 htb hns,
      hcompat, htransport⟩

/-- Per-instance Route B endpoint from the constants-gauge reduced
certificate. -/
theorem routeBPerInstanceCertificate_of_constantsGauge
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (cert :
      RouteBConstantsGaugeReducedCertificate M n hn2 htb hns) :
    RouteBPerInstanceCertificate M n hn2 htb hns :=
  routeBPerInstanceCertificate_of_reducedCertificate
    (routeBReducedCertificate_of_constantsGauge cert)

/-! ## Axiom audit anchors -/

#print axioms routeBConstantsGauge_admissible
#print axioms routeBReducedCertificate_of_constantsGauge
#print axioms routeBPerInstanceCertificate_of_constantsGauge

end PallLean.Paper93.Paper283
