import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPvsNPBoundedLocalAccessCompiler

/-!
# Dynamic boundary observers + positive dynamic SPDP + global God Move

This file implements the full restricted N-Frame combination:

`actual deterministic run → time-indexed boundary observer → positive SPDP events
 → prefix accumulation → global God-Move rank`.

SPDP events take values in `Nat`, so cancellation is impossible by construction.  The
global God Move is the sum of the causally observed event ranks over the run.  A
`BoundaryAccountsForSPDP` certificate requires every prefix to fit inside the exposed
boundary rank at that time.  Therefore an exponential global identity minor forces an
exponential final boundary rank and contradicts a bounded-local-access profile above
its polynomial ceiling.

The remaining unrestricted bridge is explicit: SAT correctness alone does not prove
that the actual run emits the positive events forming the exponential global minor.
-/

namespace PallLean.Paper93.DeepMath.PathB.PvsNPDynamicSPDPGlobalGodMove

open Finset
open PallLean.Paper93.DeepMath.PathB.PvsNPRunIndexedFaithfulTPhi
open PallLean.Paper93.DeepMath.PathB.PvsNPBoundedLocalAccessCompiler
open PallLean.Paper93.DeepMath.PathB.PvsNPNFrameRestrictedMERADecoder

variable {Input State : Type*}

/-- Positive SPDP event rank emitted at each real transition of an actual run. -/
structure DynamicPositiveSPDP (R : ActualDecisionRun Input State) where
  eventRank : Nat → Input → Nat

namespace DynamicPositiveSPDP

/-- SPDP rank accumulated before time `time`. -/
def prefixRank {R : ActualDecisionRun Input State}
    (S : DynamicPositiveSPDP R) (time : Nat) (x : Input) : Nat :=
  ∑ t ∈ Finset.range time, S.eventRank t x

/-- The global God Move is the complete positive SPDP accumulation. -/
def globalGodMoveRank {R : ActualDecisionRun Input State}
    (S : DynamicPositiveSPDP R) (x : Input) : Nat :=
  S.prefixRank R.steps x

/-- One more boundary step adds exactly its event rank. -/
theorem prefixRank_succ {R : ActualDecisionRun Input State}
    (S : DynamicPositiveSPDP R) (time : Nat) (x : Input) :
    S.prefixRank (time + 1) x = S.prefixRank time x + S.eventRank time x := by
  simpa [prefixRank] using
    (Finset.sum_range_succ (fun t => S.eventRank t x) time)

/-- **No cancellation.** Positive dynamic SPDP rank is monotone through time. -/
theorem prefixRank_mono {R : ActualDecisionRun Input State}
    (S : DynamicPositiveSPDP R) {first second : Nat} (h : first ≤ second)
    (x : Input) :
    S.prefixRank first x ≤ S.prefixRank second x := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
  intro i hi hnot
  omega

end DynamicPositiveSPDP

/-- A real dynamic boundary observer that accounts for every positive SPDP prefix.

Unlike an appended clause sheet, both `stateAt` and the event stream are indexed by the
same actual run.  `prefix_le_boundary` is the load-bearing operational transport: all
causally accumulated SPDP rank is visible at the corresponding boundary slice. -/
structure DynamicBoundarySPDPObserver (R : ActualDecisionRun Input State) where
  spdp : DynamicPositiveSPDP R
  boundaryRank : Nat → Input → Nat
  prefix_le_boundary : ∀ time, time ≤ R.steps → ∀ x,
    spdp.prefixRank time x ≤ boundaryRank time x

namespace DynamicBoundarySPDPObserver

/-- The complete global God Move fits in the final dynamic boundary. -/
theorem globalGodMove_le_finalBoundary
    {R : ActualDecisionRun Input State}
    (O : DynamicBoundarySPDPObserver R) (x : Input) :
    O.spdp.globalGodMoveRank x ≤ O.boundaryRank R.steps x := by
  exact O.prefix_le_boundary R.steps le_rfl x

/-- An exponential global identity minor forces an exponential final boundary. -/
theorem two_pow_le_finalBoundary_of_globalGodMove
    {R : ActualDecisionRun Input State}
    (O : DynamicBoundarySPDPObserver R) (n : Nat) (x : Input)
    (hminor : 2 ^ n ≤ O.spdp.globalGodMoveRank x) :
    2 ^ n ≤ O.boundaryRank R.steps x :=
  le_trans hminor (O.globalGodMove_le_finalBoundary x)

end DynamicBoundarySPDPObserver

/-! ## Bounded-local-access contradiction -/

/-- The same dynamic observer is bounded by one concrete local-access profile at input
size `n`. -/
structure ProfileBoundedDynamicGodMove
    (P : BoundedLocalAccessProfile) (n : Nat)
    (R : ActualDecisionRun Input State) where
  observer : DynamicBoundarySPDPObserver R
  finalBoundary_le : ∀ x,
    observer.boundaryRank R.steps x ≤ P.exposedRank n

namespace ProfileBoundedDynamicGodMove

/-- The positive global God Move must fit inside the profile's exposed rank. -/
theorem globalGodMove_le_exposedRank
    {P : BoundedLocalAccessProfile} {n : Nat}
    {R : ActualDecisionRun Input State}
    (G : ProfileBoundedDynamicGodMove P n R) (x : Input) :
    G.observer.spdp.globalGodMoveRank x ≤ P.exposedRank n :=
  le_trans (G.observer.globalGodMove_le_finalBoundary x)
    (G.finalBoundary_le x)

/-- Restricted contradiction: an exponential positive dynamic-SPDP God Move cannot fit
inside the polynomial local-access boundary ceiling. -/
theorem no_exponential_globalGodMove_above_ceiling
    {P : BoundedLocalAccessProfile} {n : Nat}
    {R : ActualDecisionRun Input State}
    (G : ProfileBoundedDynamicGodMove P n R)
    (hn : 1 ≤ n) (hgap : n ^ P.toMERA.polyExponent < 2 ^ n) :
    ¬ ∃ x : Input, 2 ^ n ≤ G.observer.spdp.globalGodMoveRank x := by
  rintro ⟨x, hminor⟩
  have hfit : 2 ^ n ≤ P.exposedRank n :=
    le_trans hminor (G.globalGodMove_le_exposedRank x)
  have hpoly : P.exposedRank n ≤ n ^ P.toMERA.polyExponent :=
    P.exposedRank_le_poly n hn
  exact (not_lt_of_ge (le_trans hfit hpoly)) hgap

end ProfileBoundedDynamicGodMove

/-! ## Exact SAT bridge, deliberately not smuggled in -/

/-- The missing semantic/operational theorem for a SAT machine: correctness must make
its actual dynamic boundary emit positive SPDP events whose global accumulation contains
the exponential God-Move minor, while remaining bounded by the same operational profile.

This proposition is named so downstream restricted cash-outs cannot confuse it with a
consequence already proved from SAT correctness. -/
def SATCorrectnessFormsGlobalGodMove
    (U : SATDepthMachine.MachineModel)
    (D : SATDepthMachine.DecisionMachine U)
    (P : BoundedLocalAccessProfile) : Prop :=
  SATDepthMachine.DecidesSAT U D →
    ∀ n, ∃ (Input State : Type)
      (R : ActualDecisionRun Input State)
      (G : ProfileBoundedDynamicGodMove P n R)
      (x : Input),
      2 ^ n ≤ G.observer.spdp.globalGodMoveRank x

/-!
## Honest endpoint

The full restricted combination is now present: dynamic observer, positive dynamic
SPDP, no-cancellation accumulation, global God Move, and the polynomial boundary
contradiction.  What is not proved is `SATCorrectnessFormsGlobalGodMove`: deriving its
positive event stream and exponential minor from every SAT-correct machine is the
solver-specific breakthrough, not a consequence of the abstract decision bit.
-/

end PallLean.Paper93.DeepMath.PathB.PvsNPDynamicSPDPGlobalGodMove

#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicSPDPGlobalGodMove.DynamicPositiveSPDP.prefixRank_succ
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicSPDPGlobalGodMove.DynamicPositiveSPDP.prefixRank_mono
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicSPDPGlobalGodMove.DynamicBoundarySPDPObserver.globalGodMove_le_finalBoundary
#print axioms PallLean.Paper93.DeepMath.PathB.PvsNPDynamicSPDPGlobalGodMove.ProfileBoundedDynamicGodMove.no_exponential_globalGodMove_above_ceiling
