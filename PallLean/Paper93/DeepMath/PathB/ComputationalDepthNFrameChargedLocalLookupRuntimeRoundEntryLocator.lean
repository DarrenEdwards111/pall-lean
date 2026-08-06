import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimePhysicalUnaryRebase

/-!
# Fixed next-round entry delimiter locator

The reachable doubled grammars use `01` only as an isolated boundary token:
data are `00`/`11`, headers are `10`, and every ordinary `01` boundary is
followed by a non-`01` token.  Two consecutive `01` pairs can therefore serve
as a fixed operational delimiter before the rebased next-round selector.

This file defines the finite controller and proves its exact generic parser
theorem.  No length, schedule index, or semantic offset occurs in its state.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryLocator

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect

inductive RuntimeRoundEntryState
  | lo (previousSep : Bool)
  | hi (previousSep loBit : Bool)
  | done
  deriving DecidableEq, Fintype

open RuntimeRoundEntryState

def runtimePairIsSep (p : Bool × Bool) : Bool := !p.1 && p.2

def runtimeEntryPrev : Bool → List (Bool × Bool) → Bool
  | previous, [] => previous
  | _, p :: ps => runtimeEntryPrev (runtimePairIsSep p) ps

def RuntimeNoDoubleSepFrom : Bool → List (Bool × Bool) → Prop
  | _, [] => True
  | previous, p :: ps =>
      ¬ (previous = true ∧ runtimePairIsSep p = true) ∧
        RuntimeNoDoubleSepFrom (runtimePairIsSep p) ps

/-- Scan aligned doubled pairs and halt immediately after the first `01 01`.
The remembered Boolean says whether the preceding complete pair was `01`. -/
def runtimeRoundEntryLocatorMachine : Machine where
  State := RuntimeRoundEntryState
  fin := inferInstance
  dec := inferInstance
  start := .lo false
  halt := fun s => decide (s = .done)
  δ := fun s b =>
    match s with
    | .lo previous => (.hi previous b, none, 1)
    | .hi previous loBit =>
        let sep := !loBit && b
        if previous && sep then (.done, none, 1)
        else (.lo sep, none, 1)
    | .done => (.done, none, 2)
  accept := fun _ => false

theorem runtimeRoundEntry_run_pair (T : List Bool) (q : Nat)
    (previous loBit hiBit : Bool)
    (hlo : T.getD q false = loBit)
    (hhi : T.getD (q + 1) false = hiBit)
    (hsafe : ¬ (previous = true ∧
      runtimePairIsSep (loBit, hiBit) = true)) :
    run runtimeRoundEntryLocatorMachine 2 ⟨lo previous, q, T⟩ =
      ⟨lo (runtimePairIsSep (loBit, hiBit)), q + 2, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at hlo hhi
  cases previous <;> cases loBit <;> cases hiBit <;>
    simp_all [run_succ, step, runtimeRoundEntryLocatorMachine, moveHead,
      runtimePairIsSep]

theorem runtimeRoundEntry_run_marker (T : List Bool) (q : Nat)
    (h0 : T.getD q false = false)
    (h1 : T.getD (q + 1) false = true)
    (h2 : T.getD (q + 2) false = false)
    (h3 : T.getD (q + 3) false = true) :
    run runtimeRoundEntryLocatorMachine 4 ⟨lo false, q, T⟩ =
      ⟨done, q + 4, T⟩ := by
  have hfirst := runtimeRoundEntry_run_pair T q false false true h0 h1 (by
    simp [runtimePairIsSep])
  rw [show 4 = 2 + 2 by omega, run_add, hfirst]
  rw [List.getD_eq_getElem?_getD] at h2 h3
  simp [run_succ, step, runtimeRoundEntryLocatorMachine, moveHead,
    runtimePairIsSep, h2, h3]

theorem runtimeRoundEntry_run_pairs
    (pre : List Bool) (pairs : List (Bool × Bool)) (tail : List Bool)
    (previous : Bool) (hsafe : RuntimeNoDoubleSepFrom previous pairs) :
    run runtimeRoundEntryLocatorMachine (2 * pairs.length)
        ⟨lo previous, pre.length,
          pre ++ flattenPairs pairs ++ tail⟩ =
      ⟨lo (runtimeEntryPrev previous pairs),
        pre.length + 2 * pairs.length,
        pre ++ flattenPairs pairs ++ tail⟩ := by
  induction pairs generalizing pre previous with
  | nil => rfl
  | cons p ps ih =>
      rcases p with ⟨loBit, hiBit⟩
      have hsafeHead := hsafe.1
      have hsafeTail := hsafe.2
      have hlo : (pre ++ flattenPairs ((loBit, hiBit) :: ps) ++ tail).getD
          pre.length false = loBit := by
        simp [flattenPairs]
      have hhi : (pre ++ flattenPairs ((loBit, hiBit) :: ps) ++ tail).getD
          (pre.length + 1) false = hiBit := by
        simp [flattenPairs]
      have hpair := runtimeRoundEntry_run_pair
        (pre ++ flattenPairs ((loBit, hiBit) :: ps) ++ tail)
        pre.length previous loBit hiBit hlo hhi hsafeHead
      rw [show 2 * (((loBit, hiBit) :: ps).length) = 2 + 2 * ps.length by
        simp; omega, run_add, hpair]
      have htail := ih (pre := pre ++ [loBit, hiBit])
        (previous := runtimePairIsSep (loBit, hiBit)) hsafeTail
      simpa [flattenPairs, runtimeEntryPrev, List.append_assoc,
        Nat.add_assoc] using htail

/-- Exact complete scan of an arbitrary aligned prefix with isolated `01`
tokens, followed by the reserved doubled delimiter `01 01`. -/
theorem runtimeRoundEntryLocator_run
    (pairs : List (Bool × Bool)) (tail : List Bool)
    (hsafe : RuntimeNoDoubleSepFrom false pairs)
    (hend : runtimeEntryPrev false pairs = false) :
    let marker := flattenPairs [(false, true), (false, true)]
    let T := flattenPairs pairs ++ marker ++ tail
    run runtimeRoundEntryLocatorMachine (2 * pairs.length + 4)
        (init runtimeRoundEntryLocatorMachine T) =
      ⟨done, 2 * pairs.length + 4, T⟩ := by
  dsimp only
  let marker := flattenPairs [(false, true), (false, true)]
  let T := flattenPairs pairs ++ marker ++ tail
  have hp := runtimeRoundEntry_run_pairs [] pairs (marker ++ tail) false hsafe
  have hm : run runtimeRoundEntryLocatorMachine 4
      ⟨lo false, 2 * pairs.length, T⟩ =
      ⟨done, 2 * pairs.length + 4, T⟩ := by
    apply runtimeRoundEntry_run_marker
    all_goals simp [T, marker, flattenPairs]
  have hp' : run runtimeRoundEntryLocatorMachine (2 * pairs.length)
      (init runtimeRoundEntryLocatorMachine T) =
      ⟨lo false, 2 * pairs.length, T⟩ := by
    simpa [T, marker, hend, List.append_assoc] using hp
  rw [run_add, hp']
  exact hm

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryLocator

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryLocator.runtimeRoundEntry_run_pairs
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryLocator.runtimeRoundEntryLocator_run
