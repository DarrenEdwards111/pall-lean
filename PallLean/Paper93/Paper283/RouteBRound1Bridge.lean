import PallLean.Paper93.DeepMath.PathB.NFrameLagrangianBundle
import PallLean.Paper93.Paper283.BridgeAConcreteGadget
import PallLean.Paper93.Paper283.BridgeBSpectralSandwich
import PallLean.Paper93.Paper283.FullChain283

/-!
# Route B bridge to the round-1 N-Frame work

The early PathB N-Frame files formalised useful §28.3 pieces, but they lived
outside the active `Paper283` chain.  This file deliberately imports that
round-1 bundle and connects it to the currently active Route B core.

The theorem below is still conditional on the genuinely analytic inputs:

* the spectral/log-det expansion and eigenvalue bounds packaged as
  `BridgeBSpectralHypotheses`;
* the lower log-det estimate `delta * |S| <= logDet`.

But it now uses the checked round-1 Bridge B determinant/rank reduction and
the checked Cook-Levin `κ`-pocket rank theorem inside the active Paper283
composition.
-/

namespace PallLean.Paper93.Paper283

open scoped BigOperators

/-- Route B active core using:

* round-1 Bridge B spectral/det-rank reduction,
* the checked Cook-Levin `κ`-pocket rank theorem,
* the active Paper283 Bridge A/B rank-budget language.

This is the current load-bearing §28.3 bridge shape before the final
matrix-rank-to-SAT/SPDP gauge functor is supplied. -/
theorem routeB_round1_cookLevin_spectral_core {N d : Nat}
    (alpha beta alpha0 : Real) (kappa n : Nat)
    (G : PallLean.Paper93.Concrete.RegularGraphFixed N d)
    (chi : TseitinCharge N) (Phi : Fin N -> Real)
    (halpha : 0 < alpha) (halpha0 : 0 < alpha0) (hn : 2 <= n)
    {theta normBound logDet delta : Real} {rankA : Nat}
    {eigenvalues : Fin N -> Real}
    (htheta : 0 < theta) (hnorm : 0 < normBound)
    (hspec :
      BridgeBSpectralHypotheses theta normBound logDet rankA eigenvalues)
    (hLogLower :
      delta *
          ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
            Real) <= logDet) :
    (activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card *
        kappa <=
      ∑ v ∈ activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi,
        ((cookLevinPocketLocalGadgetFamily N alpha kappa n) v).rank
    ∧
    (delta / bridgeBLogCapacity theta normBound) *
        ((activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card :
          Real) <=
      (rankA : Real) := by
  constructor
  · exact bridgeA_activeSet_rank_budget_cookLevin_kappa
      alpha beta alpha0 kappa n G chi Phi halpha halpha0 hn
  · exact bridgeB_rank_lower_from_spectral_logdet_sandwich
      (theta := theta) (normBound := normBound)
      (logDet := logDet) (delta := delta)
      (activeCard :=
        (activeSet (N := N) (d := d) alpha beta alpha0 G chi Phi).card)
      (rankA := rankA) (eigenvalues := eigenvalues)
      htheta hnorm hspec hLogLower

/-! ## Axiom audit anchors -/

#print axioms routeB_round1_cookLevin_spectral_core

end PallLean.Paper93.Paper283
