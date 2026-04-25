import PallLean.Paper93.Paper283.BridgeBRankSandwich
import PallLean.Paper93.DeepMath.PathB.BridgeBDetRankReduction

/-!
# Bridge B spectral/log-det sandwich wrapper

This file connects the checked Bridge B arithmetic reduction to the Paper283
rank-sandwich endpoint.

The fully analytic spectral theorem needed by the paper has three concrete
inputs:

* a log-det expansion as a sum over shifted eigenvalues;
* non-negativity and an operator-norm upper bound for those eigenvalues;
* identification of the matrix rank with the number of positive eigenvalues.

Given exactly those hypotheses, the upper bound

`logDet <= rank(A) * log (1 + theta * normBound)`

is proved and then fed into `bridgeB_rank_lower_from_logdet_sandwich`.
-/

namespace PallLean.Paper93.Paper283

open Finset

/-- The spectral hypotheses still needed for the paper-level Bridge B log-det
upper bound, packaged without hiding them behind a `True` placeholder.  The
eigenvalue list is an explicit parameter so the package remains proof-only. -/
structure BridgeBSpectralHypotheses {N : Nat}
    (theta normBound logDet : Real) (rankA : Nat)
    (eigenvalues : Fin N -> Real) : Prop where
  /-- Spectral/log-det expansion:
  `log det(I + theta A) = sum_i log(1 + theta * lambda_i)`. -/
  logDet_eq_sum :
    logDet = ∑ i, Real.log (1 + theta * eigenvalues i)
  eigenvalues_nonneg : ∀ i, 0 <= eigenvalues i
  eigenvalues_le_norm : ∀ i, eigenvalues i <= normBound
  rank_eq_positive_eigenvalue_count :
    rankA = (Finset.univ.filter (fun i => 0 < eigenvalues i)).card

/-- From explicit spectral hypotheses, Bridge B's log-det upper bound follows
from the already checked arithmetic determinant/rank reduction. -/
theorem bridgeB_logdet_upper_from_spectral_hypotheses
    {N : Nat} {theta normBound logDet : Real} {rankA : Nat}
    {eigenvalues : Fin N -> Real}
    (htheta : 0 < theta)
    (hspec :
      BridgeBSpectralHypotheses theta normBound logDet rankA eigenvalues) :
    logDet <= (rankA : Real) * bridgeBLogCapacity theta normBound := by
  rcases hspec with ⟨hlogDet, hnonneg, hbound, hrank⟩
  unfold bridgeBLogCapacity
  rw [hlogDet]
  exact
    PallLean.Paper93.DeepMath.PathB.BridgeBDetRankReduction.det_rank_inequality_from_eigenvalues
        (n := N) (θ := theta) htheta
        (eigenvalues := eigenvalues)
        (h_nonneg := hnonneg)
        (operator_norm := normBound)
        (h_bound := hbound)
        (rk := rankA)
        (h_rk_count := hrank)

/-- Paper-shaped Bridge B rank lower bound from an explicit spectral/log-det
upper-bound hypothesis package and a lower log-det estimate. -/
theorem bridgeB_rank_lower_from_spectral_logdet_sandwich
    {N : Nat} {theta normBound logDet delta : Real}
    {activeCard rankA : Nat}
    {eigenvalues : Fin N -> Real}
    (htheta : 0 < theta)
    (hnorm : 0 < normBound)
    (hspec :
      BridgeBSpectralHypotheses theta normBound logDet rankA eigenvalues)
    (hlower : delta * (activeCard : Real) <= logDet) :
    (delta / bridgeBLogCapacity theta normBound) *
        (activeCard : Real) <= (rankA : Real) := by
  exact bridgeB_rank_lower_from_logdet_sandwich
    (theta := theta)
    (normBound := normBound)
    (logDet := logDet)
    (delta := delta)
    (activeCard := activeCard)
    (rankA := rankA)
    (bridgeBLogCapacity_pos htheta hnorm)
    hlower
    (bridgeB_logdet_upper_from_spectral_hypotheses
      (N := N) (theta := theta) (normBound := normBound)
      (logDet := logDet) (rankA := rankA)
      (eigenvalues := eigenvalues) htheta hspec)

/-! ## Axiom audit anchors -/

#print axioms bridgeB_logdet_upper_from_spectral_hypotheses
#print axioms bridgeB_rank_lower_from_spectral_logdet_sandwich

end PallLean.Paper93.Paper283
