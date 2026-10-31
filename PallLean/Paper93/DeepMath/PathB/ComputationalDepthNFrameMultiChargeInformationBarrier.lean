import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameRamanujanFiberCapacityBarrier

/-!
# Multiple N-frame charges: the information/fibre tradeoff

One parity charge leaves fibres of size `2^(m-1)`.  The natural repair is to
conserve several independent Boolean charges.  This file gives the exact general
counting law.

A family of `q` Boolean charges is a fingerprint in `Assignment q`, hence has at
most `2^q` values.  If every fingerprint fibre contains at most `r` continuation
labels, then

```text
2^m <= 2^q * r.
```

Consequently a polynomial fibre bound requires the conserved fingerprint to
retain almost all of the `m` continuation bits.  A small collection of local
Ramanujan/N-frame observables cannot yield higher-order capacity merely by being
independent or edge-separating.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameMultiChargeInformationBarrier

open SATDepthMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPObserverSwitchToy
open PallLean.Paper93.DeepMath.PathB.NFrameConflictHypergraphCapacityEndpoint

/-! ## Boolean charge fingerprints -/

/-- Bundle `q` Boolean N-frame observables into their complete answer vector. -/
def chargeFingerprint {m q : Nat}
    (charge : Fin q -> Assignment m -> Bool) :
    Assignment m -> Assignment q :=
  fun a i => charge i a

/-- The carrier of `q` Boolean charges has exactly `2^q` possible values. -/
theorem chargeFingerprint_carrier_card (q : Nat) :
    Fintype.card (Assignment q) = 2 ^ q := by
  simp

/-- Fundamental information law: a `q`-bit fingerprint with fibres of capacity
`r` can cover at most `2^q * r` continuation labels. -/
theorem chargeFingerprint_capacity_tradeoff
    {m q r : Nat} (charge : Fin q -> Assignment m -> Bool)
    (hcap : FiberCapacityAtMost (chargeFingerprint charge) r) :
    2 ^ m <= 2 ^ q * r := by
  have hcover := assignment_card_le_cell_card_mul_capacity
    (chargeFingerprint charge) hcap
  simpa using hcover

/-- If the information-times-capacity budget lies below the cube size, some
fingerprint fibre must be larger than `r`. -/
theorem some_chargeFingerprint_fiber_exceeds
    {m q r : Nat} (charge : Fin q -> Assignment m -> Bool)
    (hgap : 2 ^ q * r < 2 ^ m) :
    ¬ FiberCapacityAtMost (chargeFingerprint charge) r := by
  intro hcap
  exact (Nat.not_lt_of_ge (chargeFingerprint_capacity_tradeoff charge hcap)) hgap

/-- In particular, `q` conserved Boolean charges and a polynomial fibre bound
`m^d` are incompatible whenever their combined information budget is below
`2^m`. -/
theorem no_small_charge_family_with_polynomial_fibers
    {m q d : Nat} (charge : Fin q -> Assignment m -> Bool)
    (hgap : 2 ^ q * m ^ d < 2 ^ m) :
    ¬ FiberCapacityAtMost (chargeFingerprint charge) (m ^ d) :=
  some_chargeFingerprint_fiber_exceeds charge hgap

/-! ## Arbitrary amplituhedron cells encoded by Boolean charges -/

/-- If every amplituhedron cell has a faithful `q`-bit name, the same
information/fibre tradeoff applies even when the cell type is abstract. -/
theorem encodedCell_capacity_tradeoff
    {m q r : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (cellOf : Assignment m -> Cell)
    (encode : Cell -> Assignment q) (hencode : Function.Injective encode)
    (hcap : FiberCapacityAtMost cellOf r) :
    2 ^ m <= 2 ^ q * r := by
  have hcover := assignment_card_le_cell_card_mul_capacity cellOf hcap
  have hcard : Fintype.card Cell <= 2 ^ q := by
    have := Fintype.card_le_of_injective encode hencode
    simpa using this
  exact le_trans hcover (Nat.mul_le_mul_right r hcard)

/-- Therefore no `q`-bit-encoded cell decomposition can simultaneously have
small fibres below the same exponential gap. -/
theorem no_encodedCells_with_small_fibers
    {m q r : Nat} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
    (cellOf : Assignment m -> Cell)
    (encode : Cell -> Assignment q) (hencode : Function.Injective encode)
    (hgap : 2 ^ q * r < 2 ^ m) :
    ¬ FiberCapacityAtMost cellOf r := by
  intro hcap
  exact (Nat.not_lt_of_ge
    (encodedCell_capacity_tradeoff cellOf encode hencode hcap)) hgap

/-! ## Solver-indexed endpoint -/

/-- A proposed solver-derived collection of too few conserved Boolean charges.
Correctness is required to bound every joint fingerprint fibre polynomially. -/
structure SolverMultiChargeCapacityFor
    (U : MachineModel) (D : DecisionMachine U) where
  m : Nat
  q : Nat
  d : Nat
  charge : Fin q -> Assignment m -> Bool
  capacity_of_decides : DecidesSAT U D ->
    FiberCapacityAtMost (chargeFingerprint charge) (m ^ d)
  informationGap : 2 ^ q * m ^ d < 2 ^ m

namespace SolverMultiChargeCapacityFor

variable {U : MachineModel} {D : DecisionMachine U}

/-- Such a charge package refutes the corresponding alleged solver. -/
theorem not_decidesSAT (P : SolverMultiChargeCapacityFor U D) :
    ¬ DecidesSAT U D := by
  intro hD
  exact no_small_charge_family_with_polynomial_fibers P.charge
    P.informationGap (P.capacity_of_decides hD)

end SolverMultiChargeCapacityFor

/-- Producing an information-gap charge package for every certified machine
rules out polynomial SAT decision. -/
theorem no_SATDecisionInP_of_multiChargeCapacity
    {U : MachineModel}
    (H : forall D : DecisionMachine U,
      Nonempty (SolverMultiChargeCapacityFor U D)) :
    ¬ SATDecisionInP U := by
  rintro ⟨D, hD⟩
  obtain ⟨P⟩ := H D
  exact P.not_decidesSAT hD

end PallLean.Paper93.DeepMath.PathB.NFrameMultiChargeInformationBarrier

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameMultiChargeInformationBarrier.chargeFingerprint_capacity_tradeoff
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameMultiChargeInformationBarrier.some_chargeFingerprint_fiber_exceeds
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameMultiChargeInformationBarrier.encodedCell_capacity_tradeoff
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameMultiChargeInformationBarrier.no_SATDecisionInP_of_multiChargeCapacity
