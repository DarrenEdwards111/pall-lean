import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPNFrameTraceCapacity

/-!
# N-Frame holographic area law: bulk demand, boundary capacity, and reuse

This file formalizes the proposed black-hole/holographic refinement of the N-Frame trace route.
At radius `R` we compare:

```text
bulk task-label demand     = R^3 bits
boundary capacity per use = R^2 bits
```

An exact-recovery stabilized channel needs at least `R^3` capacity bits.  Therefore a holographic
boundary reused fewer than `R` times cannot recover the full injective bulk label.  The result is a
real area-versus-volume contradiction.

The pressure test is also tight.  Reusing the `R^2`-bit boundary exactly `R` times supplies `R^3`
total bit-capacity, and the identity channel realizes exact recovery.  Consequently a one-shot area
law is not yet a super-polynomial time lower bound: polynomially many boundary uses can stream the
bulk information.

Nothing here asserts that an arbitrary SAT solver obeys a physical holographic area law, nor that SAT
correctness forces recovery of the full bulk label.  Those remain solver-specific mathematical inputs.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPNFrameHolographicAreaLaw

open PallLean.Paper93.DeepMath.PathB.PvsNPNFrameTraceCapacity
open PvsNPNFrameTraceCapacity.StabilizedNFrameTraceChannel

/-- A stabilized `R^3`-bit bulk-label channel constrained by an `R^2`-bit holographic boundary on
each of `boundaryUses` sequential uses. -/
structure HolographicAreaLawChannel (R : Nat) where
  channel : StabilizedNFrameTraceChannel (R ^ 3)
  boundaryUses : Nat
  capacity_from_holography : channel.capacityBits ≤ boundaryUses * R ^ 2

namespace HolographicAreaLawChannel

/-- Exact recovery forces total reused boundary area to cover the bulk label demand. -/
theorem bulk_bits_le_reused_area {R : Nat} (H : HolographicAreaLawChannel R) :
    R ^ 3 ≤ H.boundaryUses * R ^ 2 :=
  le_trans H.channel.label_bits_le_capacity H.capacity_from_holography

/-- **Holographic area/volume contradiction.**  At positive radius, fewer than `R` uses of an
`R^2`-bit boundary cannot exactly recover an injective `R^3`-bit bulk label. -/
theorem impossible_below_radius_reuse {R : Nat} (H : HolographicAreaLawChannel R)
    (hR : 0 < R) (huses : H.boundaryUses < R) : False := by
  have hpos : 0 < R ^ 2 := Nat.pow_pos hR
  have hlt : H.boundaryUses * R ^ 2 < R ^ 3 := by
    calc
      H.boundaryUses * R ^ 2 < R * R ^ 2 :=
        (Nat.mul_lt_mul_right hpos).2 huses
      _ = R ^ 3 := by ring
  exact (not_lt_of_ge H.bulk_bits_le_reused_area) hlt

/-- In particular, a one-shot holographic boundary fails at every radius `R ≥ 2`. -/
theorem impossible_one_use {R : Nat} (H : HolographicAreaLawChannel R)
    (hone : H.boundaryUses = 1) (hR : 2 ≤ R) : False := by
  apply H.impossible_below_radius_reuse (by omega)
  omega

/-- Tight streaming countermodel: the boundary is reused exactly `R` times and the full bulk label
is retained.  Each use contributes `R^2` bits, so total capacity is `R^3`. -/
def saturatedStreamingChannel (R : Nat) : HolographicAreaLawChannel R where
  channel := identityTraceChannel (R ^ 3)
  boundaryUses := R
  capacity_from_holography := by
    rw [show R * R ^ 2 = R ^ 3 by ring]
    exact le_rfl

theorem saturated_boundaryUses (R : Nat) :
    (saturatedStreamingChannel R).boundaryUses = R := rfl

theorem saturated_total_boundary_capacity (R : Nat) :
    (saturatedStreamingChannel R).boundaryUses * R ^ 2 = R ^ 3 := by
  simp [saturatedStreamingChannel]
  ring

theorem saturated_recovers_bulk (R : Nat) :
    (saturatedStreamingChannel R).channel.capacityBits = R ^ 3 := rfl

/-!
## Verdict

The area law strengthens the static N-Frame capacity argument exactly as hoped:

```text
one boundary use: R^2 < R^3 bulk demand.
```

But a computation is a process, not a static storage snapshot.  The exact operational threshold is
`boundaryUses < R`; at `boundaryUses = R`, streaming saturates the lower bound.  Since `R` uses are
polynomial in both `R` and the encoded bulk size `R^3`, the area law alone does not yield P versus NP.
A successful continuation needs either a justified sub-`R` reuse bound for every alleged SAT solver,
or a decoding-complexity theorem showing that extracting the SAT decision from the holographic boundary
requires super-polynomial work despite sufficient total information capacity.
-/

end HolographicAreaLawChannel
end PallLean.Paper93.DeepMath.PathB.PvsNPNFrameHolographicAreaLaw

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameHolographicAreaLaw.HolographicAreaLawChannel.bulk_bits_le_reused_area
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameHolographicAreaLaw.HolographicAreaLawChannel.impossible_below_radius_reuse
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameHolographicAreaLaw.HolographicAreaLawChannel.impossible_one_use
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameHolographicAreaLaw.HolographicAreaLawChannel.saturated_total_boundary_capacity
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPNFrameHolographicAreaLaw.HolographicAreaLawChannel.saturated_recovers_bulk
