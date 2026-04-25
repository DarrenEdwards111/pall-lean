import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Bridge B rank from a log-det sandwich

Paper §28.3 Bridge B uses a two-sided estimate:

`delta * |S| <= logdet <= rank(A) * log(1 + theta * ||A||)`.

The spectral/log-det work is the hard analytic input.  This file proves the
rank extraction once that input is available.  It is intentionally independent
of the older profile-collapse route.
-/

namespace PallLean.Paper93.Paper283

/-- The positive logarithmic capacity factor in Bridge B.  In the paper this is
`log(1 + theta * ||A||)` after the relevant operator-norm normalisation. -/
noncomputable def bridgeBLogCapacity (theta normBound : Real) : Real :=
  Real.log (1 + theta * normBound)

/-- The Bridge B capacity factor is positive when both parameters are
positive. -/
theorem bridgeBLogCapacity_pos
    {theta normBound : Real} (htheta : 0 < theta)
    (hnorm : 0 < normBound) :
    0 < bridgeBLogCapacity theta normBound := by
  unfold bridgeBLogCapacity
  have hprod : 0 < theta * normBound := mul_pos htheta hnorm
  have hgt : (1 : Real) < 1 + theta * normBound := by linarith
  exact Real.log_pos hgt

/-- Pure Bridge B algebra: a lower log-det bound and an upper spectral/rank
bound imply a quantitative real lower bound on the matrix rank. -/
theorem bridgeB_rank_lower_real_from_sandwich
    {logDet capacity delta : Real} {activeCard rankA : Nat}
    (hcapacity : 0 < capacity)
    (hlower : delta * (activeCard : Real) <= logDet)
    (hupper : logDet <= (rankA : Real) * capacity) :
    (delta / capacity) * (activeCard : Real) <= (rankA : Real) := by
  have hcombined :
      delta * (activeCard : Real) <= (rankA : Real) * capacity :=
    le_trans hlower hupper
  calc
    (delta / capacity) * (activeCard : Real)
        = (delta * (activeCard : Real)) / capacity := by ring
    _ <= (rankA : Real) := (div_le_iff₀ hcapacity).mpr hcombined

/-- Bridge B in its paper-shaped capacity form. -/
theorem bridgeB_rank_lower_from_logdet_sandwich
    {theta normBound logDet delta : Real} {activeCard rankA : Nat}
    (hcapacity : 0 < bridgeBLogCapacity theta normBound)
    (hlower : delta * (activeCard : Real) <= logDet)
    (hupper :
      logDet <= (rankA : Real) * bridgeBLogCapacity theta normBound) :
    (delta / bridgeBLogCapacity theta normBound) *
        (activeCard : Real) <= (rankA : Real) :=
  bridgeB_rank_lower_real_from_sandwich
    (capacity := bridgeBLogCapacity theta normBound)
    hcapacity hlower hupper

/-- If Bridge B's lower bound is genuinely positive, the resulting matrix rank
is nonzero. -/
theorem bridgeB_rank_pos_from_positive_logdet_sandwich
    {logDet capacity delta : Real} {activeCard rankA : Nat}
    (hdelta : 0 < delta)
    (hactive : 0 < activeCard)
    (hcapacity : 0 < capacity)
    (hlower : delta * (activeCard : Real) <= logDet)
    (hupper : logDet <= (rankA : Real) * capacity) :
    0 < rankA := by
  have hactive_real : 0 < (activeCard : Real) := Nat.cast_pos.mpr hactive
  have hleft_pos : 0 < delta * (activeCard : Real) :=
    mul_pos hdelta hactive_real
  have hcombined :
      delta * (activeCard : Real) <= (rankA : Real) * capacity :=
    le_trans hlower hupper
  have hrank_capacity_pos : 0 < (rankA : Real) * capacity :=
    lt_of_lt_of_le hleft_pos hcombined
  have hrank_nonneg : 0 <= (rankA : Real) := Nat.cast_nonneg rankA
  have hrank_real_pos : 0 < (rankA : Real) := by nlinarith
  exact Nat.cast_pos.mp hrank_real_pos

/-! ## Axiom audit anchors -/

#print axioms bridgeBLogCapacity_pos
#print axioms bridgeB_rank_lower_real_from_sandwich
#print axioms bridgeB_rank_lower_from_logdet_sandwich
#print axioms bridgeB_rank_pos_from_positive_logdet_sandwich

end PallLean.Paper93.Paper283
