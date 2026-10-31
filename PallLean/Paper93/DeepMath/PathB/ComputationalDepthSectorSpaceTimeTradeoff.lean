import PallLean.Paper93.DeepMath.PathB.ComputationalDepthObserverTimeDebt
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCircuitLBGrowth

/-!
# Quantitative sector space-time tradeoff

This module formalizes the non-circular arithmetic isolated by the fourth
Curiosity search.  A certified family carries `2^n` units of independent
semantic debt.  A computation with an `s`-bit configuration boundary can
service at most `2^s` units per step.  If the debt is completely discharged in
`T` steps, then

`2^n ≤ T * 2^s`, and, when `s ≤ n`, `2^(n-s) ≤ T`.

The certification of independent SAT sectors remains an explicit hypothesis;
the theorem does not infer it from a single decision bit or raw machine
locality.
-/

namespace PallLean.Paper93.DeepMath.PathB.SectorSpaceTimeTradeoff

open PallLean.Paper93.DeepMath.PathB.ObserverTimeDebt
open PallLean.Paper93.DeepMath.PathB.CircuitLBGrowth

/-- A concrete rate-limited discharge certificate for `2^n` independent
semantic sectors through an `s`-bit configuration boundary. -/
structure CertifiedSectorDischarge (n s T : Nat) where
  unresolved : Nat → Nat
  initial_load : unresolved 0 = 2 ^ n
  bounded_step_service : ∀ t, unresolved t ≤ unresolved (t + 1) + 2 ^ s
  terminal_zero : unresolved T = 0

namespace CertifiedSectorDischarge

/-- Integrated conservation: `T` steps of capacity `2^s` must cover the full
`2^n` certified sector load. -/
theorem space_time_product {n s T : Nat} (C : CertifiedSectorDischarge n s T) :
    2 ^ n ≤ T * 2 ^ s := by
  have h := correct_needs_action C.unresolved (fun _ => 2 ^ s)
    C.bounded_step_service T C.terminal_zero
  rw [C.initial_load] at h
  simpa [observerTimeAction, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] using h

/-- Cancelling the positive boundary capacity exposes the exponent gap:
`T ≥ 2^(n-s)`. -/
theorem gap_time_lower_bound {n s T : Nat} (C : CertifiedSectorDischarge n s T)
    (hsn : s ≤ n) :
    2 ^ (n - s) ≤ T := by
  have hsplit : (2 : Nat) ^ n = 2 ^ (n - s) * 2 ^ s := by
    rw [← pow_add]
    congr 1
    omega
  have htrade := C.space_time_product
  rw [hsplit] at htrade
  exact Nat.le_of_mul_le_mul_right htrade (by positivity)

end CertifiedSectorDischarge

/-- Family-level restricted superpolynomial conclusion.  If the exponent-gap
threshold itself is not polynomially bounded and every size has a certified
sector discharge, then the running time cannot be polynomially bounded. -/
theorem time_not_polyBounded_of_sector_gap
    (space time : Nat → Nat)
    (hspace : ∀ n, space n ≤ n)
    (certificate : ∀ n, CertifiedSectorDischarge n (space n) (time n))
    (hgap : ¬ PolyBounded (fun n => 2 ^ (n - space n))) :
    ¬ PolyBounded time := by
  intro htime
  apply hgap
  rcases htime with ⟨coefficient, exponent, hbound⟩
  exact ⟨coefficient, exponent, fun n =>
    le_trans ((certificate n).gap_time_lower_bound (hspace n)) (hbound n)⟩

end PallLean.Paper93.DeepMath.PathB.SectorSpaceTimeTradeoff

#print axioms PallLean.Paper93.DeepMath.PathB.SectorSpaceTimeTradeoff.CertifiedSectorDischarge.space_time_product
#print axioms PallLean.Paper93.DeepMath.PathB.SectorSpaceTimeTradeoff.CertifiedSectorDischarge.gap_time_lower_bound
#print axioms PallLean.Paper93.DeepMath.PathB.SectorSpaceTimeTradeoff.time_not_polyBounded_of_sector_gap
