import PallLean.Paper93.DeepMath.PathB.ComputationalDepthChargedCanonicalQueryAudit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthBranchingObserver

/-!
# Bridge: the charged continuation-quotient is a branching (holographic) observer

The charged dynamic-SPDP arc and the earlier observer-boundary programme reduce to the *same* socket
(`CookLevinFrontierHyp`).  This file makes one direction of that identification concrete at the object level:
the charged continuation-quotient of `ChargedContinuationQuotient` is literally an instance of the
`BranchingObserver` of `ComputationalDepthBranchingObserver`, so the boundary machinery proved there applies to
the charged model verbatim.

`chargedObserver M n` is the branching observer whose sectors are the finite reachable points at length `n` and
whose `view` is any injective encoding of the intrinsic quotient (the canonical rich scheme separates every
point, `canonical_profile_injective`, so its quotient is the full carrier).  The observer-boundary theorem
`exp_nonmergeable_sectors_force_boundary` then gives `chargedObserver_boundary_ge`: boundary entropy `≥ n`.

## What this bridge is — and is not

It is a **structural unification**: the two programmes are provably about the same object (a finite observer's
separating power at the boundary), so the observer-boundary results — the fooling/non-mergeability principle and
its calibrations — transfer to the charged setting.

It is **not** a separation and gives the charged *dynamic* measure no new leverage.  The `≥ n` here is the
*static* boundary (it holds for **every** charged machine, easy or hard, because the carrier already has `2^n`
inputs) — the same "static rank blows up on easy languages" horn seen in the equality stress test, now expressed
through the literal branching-observer machinery.  A useful lower bound still needs the min-over-decompositions
content of the observer-boundary programme's restricted rungs (`MinBoundaryRealized`,
`ObserverBlockDecompositionMin`), which no fixed-scheme charged measure supplies.  Nothing here is
`NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ChargedObserverBridge

open PallLean.Paper93.DeepMath.PathB.ChargedHolographicMachine
open PallLean.Paper93.DeepMath.PathB.ChargedLengthObserver
open PallLean.Paper93.DeepMath.PathB.BranchingObserver

/-- Boundary entropy carried by the charged reachable-point carrier: exactly enough bits to index it. -/
noncomputable def chargedEntropy (M : ChargedMachine) (n : Nat) : Nat :=
  Nat.clog 2 (Fintype.card (ReachablePoint M n))

theorem chargedCard_le (M : ChargedMachine) (n : Nat) :
    Fintype.card (ReachablePoint M n) ≤ 2 ^ chargedEntropy M n :=
  Nat.le_pow_clog (by norm_num) _

/-- An injective boundary view of the reachable points into the entropy-indexed interface. -/
noncomputable def chargedView (M : ChargedMachine) (n : Nat) :
    ReachablePoint M n → Fin (2 ^ chargedEntropy M n) :=
  fun p => Fin.castLE (chargedCard_le M n) ((Fintype.equivFin (ReachablePoint M n)) p)

theorem chargedView_injective (M : ChargedMachine) (n : Nat) :
    Function.Injective (chargedView M n) := by
  intro p q h
  apply (Fintype.equivFin (ReachablePoint M n)).injective
  exact Fin.castLE_injective (chargedCard_le M n) h

/-- **The charged continuation-quotient as a branching observer.**  Sectors are the finite reachable points;
the view separates them, matching the injective canonical quotient (`canonical_profile_injective`). -/
noncomputable def chargedObserver (M : ChargedMachine) (n : Nat) :
    BranchingObserver (ReachablePoint M n) where
  entropy := chargedEntropy M n
  view := chargedView M n

/-- All reachable points are mutually non-mergeable for the charged observer. -/
theorem chargedObserver_nonmergeable (M : ChargedMachine) (n : Nat) :
    (chargedObserver M n).Nonmergeable Finset.univ :=
  fun p _ q _ h => chargedView_injective M n h

/-- **Boundary lower bound via the observer-boundary theorem.**  The charged observer's boundary entropy is at
least `n` — obtained by applying the proved `exp_nonmergeable_sectors_force_boundary` to the `2^n`-plus reachable
points.  (Static, not a separation: it holds for every charged machine.) -/
theorem chargedObserver_boundary_ge (M : ChargedMachine) (n : Nat) :
    n ≤ (chargedObserver M n).entropy := by
  apply exp_nonmergeable_sectors_force_boundary (chargedObserver M n) Finset.univ
    (chargedObserver_nonmergeable M n)
  rw [Finset.card_univ, card_reachablePoint]
  exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

end PallLean.Paper93.DeepMath.PathB.ChargedObserverBridge

#print axioms PallLean.Paper93.DeepMath.PathB.ChargedObserverBridge.chargedObserver_nonmergeable
#print axioms PallLean.Paper93.DeepMath.PathB.ChargedObserverBridge.chargedObserver_boundary_ge
