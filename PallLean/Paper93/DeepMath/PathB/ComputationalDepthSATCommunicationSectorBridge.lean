import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSectorSpaceTimeTradeoff
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTimeUnrolledTensorNetwork

/-!
# Certified SAT communication-cut to sector-discharge bridge

This module packages the strongest non-circular communication-lifting step.
A run is supplied with a certified family of `2^n` independently oriented SAT
sectors and a forced communication cut carrying at most `cutBits` bits per
round.  The local communication bound gives service capacity `2^cutBits`.
The resulting trajectory is converted to `CertifiedSectorDischarge`, so all
space-time and superpolynomial consequences are inherited.

Crucially, the independent-sector certification is a field of the restricted
interface.  It is not inferred from correctness of one SAT output bit.
-/

namespace PallLean.Paper93.DeepMath.PathB.SATCommunicationSectorBridge

open PallLean.Paper93.DeepMath.PathB.SectorSpaceTimeTradeoff
open PallLean.Paper93.DeepMath.PathB.TimeUnrolledTensorNetwork
open PallLean.Paper93.DeepMath.PathB.CircuitLBGrowth

/-- A SAT run with an explicit hard-sector orientation certificate across a
communication cut.  `unresolved t` counts the independently certified sectors
remaining after round `t`. -/
structure CertifiedCommunicationCutRun (n cutBits rounds : Nat) where
  unresolved : Nat → Nat
  certified_independent_load : unresolved 0 = 2 ^ n
  communication_cut_service :
    ∀ t, unresolved t ≤ unresolved (t + 1) + 2 ^ cutBits
  correct_terminal_orientation : unresolved rounds = 0

namespace CertifiedCommunicationCutRun

/-- The communication certificate is exactly a sector-discharge certificate
with service exponent `cutBits`. -/
def toSectorDischarge {n cutBits rounds : Nat}
    (C : CertifiedCommunicationCutRun n cutBits rounds) :
    CertifiedSectorDischarge n cutBits rounds where
  unresolved := C.unresolved
  initial_load := C.certified_independent_load
  bounded_step_service := C.communication_cut_service
  terminal_zero := C.correct_terminal_orientation

/-- Communication product lower bound: all rounds together must carry the
certified `2^n` sector load. -/
theorem communication_product {n cutBits rounds : Nat}
    (C : CertifiedCommunicationCutRun n cutBits rounds) :
    2 ^ n ≤ rounds * 2 ^ cutBits :=
  C.toSectorDischarge.space_time_product

/-- With a subcritical cut, the number of rounds is at least the remaining
exponent gap. -/
theorem communication_round_lower_bound {n cutBits rounds : Nat}
    (C : CertifiedCommunicationCutRun n cutBits rounds)
    (hcut : cutBits ≤ n) :
    2 ^ (n - cutBits) ≤ rounds :=
  C.toSectorDischarge.gap_time_lower_bound hcut

/-- The message/bond alphabet of a `cutBits`-bit cut has exactly `2^cutBits`
states. -/
theorem cut_bondDimension (cutBits : Nat) :
    bondDimension (Fin (2 ^ cutBits)) = 2 ^ cutBits := by
  simp [bondDimension]

end CertifiedCommunicationCutRun

/-- Family-level communication lower bound.  A non-polynomial exponent-gap
threshold forces non-polynomially many communication rounds. -/
theorem rounds_not_polyBounded_of_certified_cuts
    (cutBits rounds : Nat → Nat)
    (hcut : ∀ n, cutBits n ≤ n)
    (certificate : ∀ n, CertifiedCommunicationCutRun n (cutBits n) (rounds n))
    (hgap : ¬ PolyBounded (fun n => 2 ^ (n - cutBits n))) :
    ¬ PolyBounded rounds := by
  apply time_not_polyBounded_of_sector_gap cutBits rounds hcut
  · exact fun n => (certificate n).toSectorDischarge
  · exact hgap

end PallLean.Paper93.DeepMath.PathB.SATCommunicationSectorBridge

#print axioms PallLean.Paper93.DeepMath.PathB.SATCommunicationSectorBridge.CertifiedCommunicationCutRun.communication_product
#print axioms PallLean.Paper93.DeepMath.PathB.SATCommunicationSectorBridge.CertifiedCommunicationCutRun.communication_round_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.SATCommunicationSectorBridge.CertifiedCommunicationCutRun.cut_bondDimension
#print axioms PallLean.Paper93.DeepMath.PathB.SATCommunicationSectorBridge.rounds_not_polyBounded_of_certified_cuts
