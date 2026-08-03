import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameMultiChargeInformationBarrier

/-!
# Near-complete continuation information is necessary

The multi-charge law says `2^m <= 2^q * r`.  This file converts that product
bound into an explicit lower bound on retained continuation bits.

If the desired fibre capacity is below `2^t`, then every valid Boolean charge
fingerprint must satisfy

```text
m <= q + t,
```

or equivalently its information deficit `m - q` is at most `t`.  Polynomial
fibres therefore permit only logarithmic information loss.  At the tight endpoint,
the `m` coordinate charges give the identity fingerprint with singleton fibres,
but of course have the full `2^m` answer range.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameNearCompleteInformationEndpoint

open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameConflictHypergraphCapacityEndpoint
open PallLean.Paper93.DeepMath.PathB.NFrameMultiChargeInformationBarrier

/-! ## Explicit retained-bit lower bound -/

/-- If a `q`-bit fingerprint has fibres bounded by `r < 2^t`, it must retain all
but at most `t` of the `m` continuation bits. -/
theorem retainedBits_add_slack_ge_dimension
    {m q r t : Nat} (charge : Fin q -> Assignment m -> Bool)
    (hcap : FiberCapacityAtMost (chargeFingerprint charge) r)
    (hr : r < 2 ^ t) :
    m <= q + t := by
  by_contra hnot
  have hqt : q + t < m := by omega
  have htrade := chargeFingerprint_capacity_tradeoff charge hcap
  have hmul : 2 ^ q * r < 2 ^ q * 2 ^ t :=
    Nat.mul_lt_mul_of_pos_left hr (by positivity)
  have hadd : 2 ^ q * 2 ^ t = 2 ^ (q + t) := by
    exact (pow_add 2 q t).symm
  rw [hadd] at hmul
  have hpowers : 2 ^ (q + t) < 2 ^ m :=
    Nat.pow_lt_pow_right (by norm_num) hqt
  exact (Nat.not_lt_of_ge htrade) (lt_trans hmul hpowers)

/-- Equivalent deficit form: at most `t` continuation bits may be forgotten. -/
theorem informationDeficit_le_slack
    {m q r t : Nat} (charge : Fin q -> Assignment m -> Bool)
    (hcap : FiberCapacityAtMost (chargeFingerprint charge) r)
    (hr : r < 2 ^ t) :
    m - q <= t := by
  have h := retainedBits_add_slack_ge_dimension charge hcap hr
  omega

/-- Polynomial fibre capacity `m^d` yields the same conclusion whenever it lies
below the chosen binary slack `2^t`. -/
theorem polynomialFiber_forces_nearCompleteFingerprint
    {m q d t : Nat} (charge : Fin q -> Assignment m -> Bool)
    (hcap : FiberCapacityAtMost (chargeFingerprint charge) (m ^ d))
    (hpoly : m ^ d < 2 ^ t) :
    m - q <= t :=
  informationDeficit_le_slack charge hcap hpoly

/-! ## The same bound for abstract amplituhedron cells -/

/-- A cell decomposition with fibres below `2^t` needs at least `m-t` bits in
every faithful cell encoding. -/
theorem encodedCell_informationDeficit_le_slack
    {m q r t : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (cellOf : Assignment m -> Cell)
    (encode : Cell -> Assignment q) (hencode : Function.Injective encode)
    (hcap : FiberCapacityAtMost cellOf r)
    (hr : r < 2 ^ t) :
    m - q <= t := by
  have htrade := encodedCell_capacity_tradeoff cellOf encode hencode hcap
  by_contra hnot
  have hqt : q + t < m := by omega
  have hmul : 2 ^ q * r < 2 ^ q * 2 ^ t :=
    Nat.mul_lt_mul_of_pos_left hr (by positivity)
  have hadd : 2 ^ q * 2 ^ t = 2 ^ (q + t) := by
    exact (pow_add 2 q t).symm
  rw [hadd] at hmul
  have hpowers : 2 ^ (q + t) < 2 ^ m :=
    Nat.pow_lt_pow_right (by norm_num) hqt
  exact (Nat.not_lt_of_ge htrade) (lt_trans hmul hpowers)

/-! ## Tightness: retaining every coordinate gives singleton fibres -/

/-- The complete coordinate family of Boolean N-frame charges. -/
def coordinateCharges {m : Nat} (i : Fin m) (a : Assignment m) : Bool :=
  a i

/-- Its joint fingerprint is definitionally the original continuation label. -/
theorem coordinateFingerprint_eq {m : Nat} (a : Assignment m) :
    chargeFingerprint (coordinateCharges (m := m)) a = a := by
  rfl

/-- Full information gives exact fibre capacity one. -/
theorem coordinateFingerprint_fiberCapacity_one (m : Nat) :
    FiberCapacityAtMost
      (chargeFingerprint (coordinateCharges (m := m))) 1 := by
  intro c
  have hfilter :
      ((Finset.univ : Finset (Assignment m)).filter
        (fun a => chargeFingerprint coordinateCharges a = c)) = {c} := by
    ext a
    simp [coordinateFingerprint_eq]
  rw [hfilter]
  simp

/-- The tight endpoint records the tradeoff explicitly: singleton fibres require
the full `m`-bit carrier, which has `2^m` possible values. -/
theorem fullInformation_tight_endpoint (m : Nat) :
    FiberCapacityAtMost
        (chargeFingerprint (coordinateCharges (m := m))) 1 ∧
      Fintype.card (Assignment m) = 2 ^ m :=
  ⟨coordinateFingerprint_fiberCapacity_one m, by simp⟩

end PallLean.Paper93.DeepMath.PathB.NFrameNearCompleteInformationEndpoint

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameNearCompleteInformationEndpoint.retainedBits_add_slack_ge_dimension
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameNearCompleteInformationEndpoint.informationDeficit_le_slack
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameNearCompleteInformationEndpoint.encodedCell_informationDeficit_le_slack
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameNearCompleteInformationEndpoint.fullInformation_tight_endpoint
