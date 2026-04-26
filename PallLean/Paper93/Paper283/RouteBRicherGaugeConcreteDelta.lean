import PallLean.Paper93.Paper283.RouteBRicherGaugeConcreteAssembly

/-!
# Concrete Route B delta schedule

This file closes the scalar side condition left by
`RouteBRicherGaugeConcreteAssembly`: the local barrier parameter `delta` is
chosen to be exactly `rankLogRate * kappa` for the checked log-divided rank
schedule.
-/

namespace PallLean.Paper93.Paper283

open PallLean.Paper93.DeepMath.BridgeB
open PallLean.Paper93.DeepMath.GadgetRank

/-- The concrete log-divided rank-log rate used by the Route B assembly. -/
noncomputable def routeBRicherGaugeConcreteRankLogRate
    (alpha : Real) (kappa gadgetN : Nat) (eta theta : Real) : Real :=
  Real.log (1 + theta * eta) /
    ((pocketFamily alpha kappa gadgetN).rank : Real)

/-- The concrete scalar side-condition schedule:
`delta = rankLogRate * kappa`. -/
noncomputable def routeBRicherGaugeConcreteDelta
    (alpha : Real) (kappa gadgetN : Nat) (eta theta : Real) : Real :=
  routeBRicherGaugeConcreteRankLogRate alpha kappa gadgetN eta theta *
    (kappa : Real)

/-- The explicit delta schedule closes
`delta <= rankLogRate * kappa` by reflexivity. -/
theorem routeBRicherGaugeConcreteDelta_le_rankLogRate_kappa
    (alpha : Real) (kappa gadgetN : Nat) (eta theta : Real) :
    routeBRicherGaugeConcreteDelta alpha kappa gadgetN eta theta <=
      routeBRicherGaugeConcreteRankLogRate alpha kappa gadgetN eta theta *
        (kappa : Real) := by
  rfl

/-- Concrete Route B certificate with the scalar side condition closed by the
explicit choice `delta := rankLogRate * kappa`.

After this specialization the only remaining Route B semantic assumptions are
SPDP containment for the concrete one-row candidate and the unprojected
P-window finite-span cover. -/
theorem routeBPerInstanceCertificate_of_richerGaugeConcreteAssembly_deltaEqRateKappa
    {N d : Nat}
    (M : TuringMachine.DTM) (n : Nat) (hn : n >= 2 ^ 804) (hn2 : n >= 2)
    (htb : M.timeBound <= 4) (hns : M.numStates <= n)
    (alpha beta alpha0 : Real) (kappa gadgetN : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    {eta theta : Real}
    (hN : 1 <= N)
    (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0)
    (hkappa : 0 < kappa) (hgadgetN : 2 <= gadgetN)
    (hcontain :
      RouteBRicherGaugeSPDPSubspaceContainment M n hn2 htb hns
        (routeBRicherFiniteRowsCandidateGauge M n hn2 htb hns
          (routeBRicherConcreteNPWitnessRows M n hn2 htb hns)))
    (cover :
      RouteBRicherGaugeUnprojectedPWindowFiniteSpanCover M n hn2 htb hns) :
    RouteBPerInstanceCertificate M n hn2 htb hns := by
  exact
    routeBPerInstanceCertificate_of_richerGaugeConcreteAssembly_logDivBudget
      (N := N) (d := d)
      M n hn hn2 htb hns
      alpha beta alpha0 kappa gadgetN G chi Phi
      (eta := eta) (theta := theta)
      (delta := routeBRicherGaugeConcreteDelta alpha kappa gadgetN eta theta)
      hN heta htheta halpha halpha0 hkappa hgadgetN
      (by
        rw [routeBRicherGaugeConcreteDelta,
          routeBRicherGaugeConcreteRankLogRate])
      hcontain cover

/-! ## Axiom audit anchors -/

#print axioms routeBRicherGaugeConcreteRankLogRate
#print axioms routeBRicherGaugeConcreteDelta
#print axioms routeBRicherGaugeConcreteDelta_le_rankLogRate_kappa
#print axioms routeBPerInstanceCertificate_of_richerGaugeConcreteAssembly_deltaEqRateKappa

end PallLean.Paper93.Paper283
