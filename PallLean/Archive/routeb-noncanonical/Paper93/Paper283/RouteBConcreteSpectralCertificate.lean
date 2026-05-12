import PallLean.Paper93.Paper283.RouteBFinalAssembly

/-!
# Route B concrete spectral certificate

This file refines the existential `RouteBPerInstanceCertificate` from
`RouteBFinalAssembly` by discharging its spectral package from an actual
positive semidefinite matrix via `BridgeBSpectralReal`.

The remaining non-spectral inputs are still explicit: Bridge A's lower
log-det estimate, the admissible NFrame candidate, projection-rank
compatibility, and the Route B matrix-to-SAT functoriality package.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators
open TuringMachine
open PaperFaithfulSeparation
open PallLean.Paper93.DeepMath.PathB

/-- Concrete spectral Route B data for one Cook-Levin SAT-decider instance.

Compared with `RouteBPerInstanceCertificate`, this package does not ask for a
free `BridgeBSpectralHypotheses` field.  It asks instead for a concrete PSD
matrix `A`, positive-definiteness of the shifted matrix `I + theta A`, the
shifted eigenvalue identity, and a pointwise norm bound on the eigenvalues of
`A`. -/
def ConcreteSpectralRouteBPerInstanceCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∃ (N d : Nat)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (A : Matrix (Fin N) (Fin N) Real)
    (theta normBound delta : Real)
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hA : A.PosSemidef)
    (hshift :
      ((1 : Matrix (Fin N) (Fin N) Real) + theta • A).PosDef),
      0 < alpha ∧ 0 < alpha0 ∧ 2 <= gadgetN ∧
      (∀ i, hshift.1.eigenvalues i = 1 + theta * hA.1.eigenvalues i) ∧
      (∀ i, hA.1.eigenvalues i <= normBound) ∧
      0 < theta ∧ 0 < normBound ∧
      delta *
          ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
            Real) <=
        Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det) ∧
      PallLean.Paper93.NFrame.AdmissibleGauge Pi ∧
      RouteBProjectionRankCompatible M n hn2 htb hns A.rank Pi ∧
      RouteBMatrixToSATGaugeFunctoriality
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        (bridgeBLogCapacity theta normBound) delta A.rank Pi

/-- Build the generic Route B per-instance certificate from an actual PSD
matrix and the shifted spectral data needed by `BridgeBSpectralReal`. -/
theorem routeBPerInstanceCertificate_of_posSemidef_shift_spectral_data
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (A : Matrix (Fin N) (Fin N) Real)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hgadgetN : 2 <= gadgetN)
    {theta normBound delta : Real}
    (hA : A.PosSemidef)
    (hshift :
      ((1 : Matrix (Fin N) (Fin N) Real) + theta • A).PosDef)
    (hshift_eigenvalues_eq_one_add_theta_mul :
      ∀ i, hshift.1.eigenvalues i = 1 + theta * hA.1.eigenvalues i)
    (heigenvalues_le_normBound :
      ∀ i, hA.1.eigenvalues i <= normBound)
    (htheta : 0 < theta) (hnorm : 0 < normBound)
    (hLogLower :
      delta *
          ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
            Real) <=
        Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det))
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hAdm : PallLean.Paper93.NFrame.AdmissibleGauge Pi)
    (hcompat :
      RouteBProjectionRankCompatible M n hn2 htb hns A.rank Pi)
    (hfun :
      RouteBMatrixToSATGaugeFunctoriality
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        (bridgeBLogCapacity theta normBound) delta A.rank Pi) :
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  refine
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi,
      theta, normBound,
      Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det),
      delta, A.rank, hA.1.eigenvalues, Pi, ?_⟩
  exact
    ⟨halpha, halpha0, hgadgetN, htheta, hnorm,
      bridgeB_spectral_hypotheses_of_posSemidef_with_shift_posDef_and_shift_eigenvalues_eq_one_add_theta_mul_and_eigenvalue_bound
        (theta := theta) (normBound := normBound)
        A hA hshift hshift_eigenvalues_eq_one_add_theta_mul
        heigenvalues_le_normBound,
      hLogLower, hAdm, hcompat, hfun⟩

/-- Existential concrete spectral certificates refine the generic Route B
per-instance certificate interface. -/
theorem routeBPerInstanceCertificate_of_concreteSpectralRouteBCertificate
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (cert :
      ConcreteSpectralRouteBPerInstanceCertificate M n hn2 htb hns) :
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  rcases cert with
    ⟨N, d, alpha, beta, alpha0, kappa, gadgetN, G, chi, Phi, A,
      theta, normBound, delta, Pi, hA, hshift,
      halpha, halpha0, hgadgetN,
      hshift_eigenvalues_eq_one_add_theta_mul,
      heigenvalues_le_normBound, htheta, hnorm, hLogLower, hAdm, hcompat,
      hfun⟩
  exact routeBPerInstanceCertificate_of_posSemidef_shift_spectral_data
    (M := M) (n := n) (hn2 := hn2) (htb := htb) (hns := hns)
    alpha beta alpha0 kappa gadgetN G chi Phi A
    halpha halpha0 hgadgetN hA hshift
    hshift_eigenvalues_eq_one_add_theta_mul heigenvalues_le_normBound
    htheta hnorm hLogLower Pi hAdm hcompat hfun

/-- Direct per-instance final target from the concrete PSD spectral data. -/
theorem cookLevinRichProjectionTarget_of_posSemidef_shift_spectral_data
    {M : DTM} {n : Nat} {hn : n ≥ 2 ^ 804} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    {N d : Nat}
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (A : Matrix (Fin N) (Fin N) Real)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hgadgetN : 2 <= gadgetN)
    {theta normBound delta : Real}
    (hA : A.PosSemidef)
    (hshift :
      ((1 : Matrix (Fin N) (Fin N) Real) + theta • A).PosDef)
    (hshift_eigenvalues_eq_one_add_theta_mul :
      ∀ i, hshift.1.eigenvalues i = 1 + theta * hA.1.eigenvalues i)
    (heigenvalues_le_normBound :
      ∀ i, hA.1.eigenvalues i <= normBound)
    (htheta : 0 < theta) (hnorm : 0 < normBound)
    (hLogLower :
      delta *
          ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
            Real) <=
        Real.log (((1 : Matrix (Fin N) (Fin N) Real) + theta • A).det))
    (Pi : PallLean.Paper93.NFrame.CandidateGauge
      (RouteBCookLevinDim M n hn2 htb hns))
    (hAdm : PallLean.Paper93.NFrame.AdmissibleGauge Pi)
    (hcompat :
      RouteBProjectionRankCompatible M n hn2 htb hns A.rank Pi)
    (hfun :
      RouteBMatrixToSATGaugeFunctoriality
        M n hn2 htb hns alpha beta alpha0 kappa G chi Phi
        (cookLevinPocketLocalGadgetFamily N alpha kappa gadgetN)
        (bridgeBLogCapacity theta normBound) delta A.rank Pi) :
    CookLevinRichProjectionTarget M n hn hn2 htb hns :=
  cookLevinRichProjectionTarget_of_routeBCertificate
    (hn := hn)
    (routeBPerInstanceCertificate_of_posSemidef_shift_spectral_data
      (M := M) (n := n) (hn2 := hn2) (htb := htb) (hns := hns)
      alpha beta alpha0 kappa gadgetN G chi Phi A
      halpha halpha0 hgadgetN hA hshift
      hshift_eigenvalues_eq_one_add_theta_mul heigenvalues_le_normBound
      htheta hnorm hLogLower Pi hAdm hcompat hfun)

/-- Uniform concrete spectral Route B certificates discharge the final
no-bounded-SAT-decider endpoint through Route B data alone. -/
theorem noBoundedSATDeciderAtPaperScale_of_concreteSpectralRouteBCertificates
    (hcert :
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
        (_hdec : DecidesSAT M),
        ConcreteSpectralRouteBPerInstanceCertificate M n hn2 htb hns) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_routeBCertificates
    (fun M n hn hn2 htb hns hdec =>
      routeBPerInstanceCertificate_of_concreteSpectralRouteBCertificate
        (hcert M n hn hn2 htb hns hdec))

/-! ## Axiom audit anchors -/

#print axioms routeBPerInstanceCertificate_of_posSemidef_shift_spectral_data
#print axioms routeBPerInstanceCertificate_of_concreteSpectralRouteBCertificate
#print axioms cookLevinRichProjectionTarget_of_posSemidef_shift_spectral_data
#print axioms noBoundedSATDeciderAtPaperScale_of_concreteSpectralRouteBCertificates

end PallLean.Paper93.Paper283
