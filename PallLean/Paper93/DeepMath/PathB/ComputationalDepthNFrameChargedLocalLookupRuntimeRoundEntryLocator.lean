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
  | markerLo
  | markerHi (loBit : Bool)
  | markerBack
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

/-- Scan aligned doubled pairs.  After seeing at least two consecutive `01`
pairs, consume the first following nonseparator pair and back up to its first
cell.  Delaying acceptance in this way makes the delimiter robust when the
reachable prefix itself ends in an ordinary isolated `01`. -/
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
        if previous && sep then (.markerLo, none, 1)
        else (.lo sep, none, 1)
    | .markerLo => (.markerHi b, none, 1)
    | .markerHi loBit =>
        let sep := !loBit && b
        if sep then (.markerLo, none, 1)
        else (.markerBack, none, 0)
    | .markerBack => (.done, none, 2)
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

theorem runtimeRoundEntry_run_marker_toSelector (T : List Bool) (q : Nat)
    (h0 : T.getD q false = false)
    (h1 : T.getD (q + 1) false = true)
    (h2 : T.getD (q + 2) false = false)
    (h3 : T.getD (q + 3) false = true)
    (hs0 hs1 : Bool)
    (h4 : T.getD (q + 4) false = hs0)
    (h5 : T.getD (q + 5) false = hs1)
    (hnonsep : runtimePairIsSep (hs0, hs1) = false) :
    run runtimeRoundEntryLocatorMachine 7 ⟨lo false, q, T⟩ =
      ⟨done, q + 4, T⟩ := by
  have hfirst := runtimeRoundEntry_run_pair T q false false true h0 h1 (by
    simp [runtimePairIsSep])
  rw [show 7 = 2 + 5 by omega, run_add, hfirst]
  rw [List.getD_eq_getElem?_getD] at h2 h3 h4 h5
  cases hs0 <;> cases hs1 <;>
    simp_all [run_succ, step, runtimeRoundEntryLocatorMachine, moveHead,
      runtimePairIsSep]

theorem runtimeRoundEntry_run_marker_toSelector_afterSep
    (T : List Bool) (q : Nat)
    (h0 : T.getD q false = false)
    (h1 : T.getD (q + 1) false = true)
    (h2 : T.getD (q + 2) false = false)
    (h3 : T.getD (q + 3) false = true)
    (hs0 hs1 : Bool)
    (h4 : T.getD (q + 4) false = hs0)
    (h5 : T.getD (q + 5) false = hs1)
    (hnonsep : runtimePairIsSep (hs0, hs1) = false) :
    run runtimeRoundEntryLocatorMachine 7 ⟨lo true, q, T⟩ =
      ⟨done, q + 4, T⟩ := by
  rw [List.getD_eq_getElem?_getD] at h0 h1 h2 h3 h4 h5
  cases hs0 <;> cases hs1 <;>
    simp_all [run_succ, step, runtimeRoundEntryLocatorMachine, moveHead,
      runtimePairIsSep]

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
tokens, followed by the reserved doubled delimiter `01 01` and a nonseparator
first selector pair. -/
theorem runtimeRoundEntryLocator_run
    (pairs : List (Bool × Bool)) (tail : List Bool)
    (tailLo tailHi : Bool)
    (hsafe : RuntimeNoDoubleSepFrom false pairs)
    (htail : tail = tailLo :: tailHi :: tail.drop 2)
    (hnonsep : runtimePairIsSep (tailLo, tailHi) = false) :
    let marker := flattenPairs [(false, true), (false, true)]
    let T := flattenPairs pairs ++ marker ++ tail
    run runtimeRoundEntryLocatorMachine (2 * pairs.length + 7)
        (init runtimeRoundEntryLocatorMachine T) =
      ⟨done, 2 * pairs.length + 4, T⟩ := by
  dsimp only
  let marker := flattenPairs [(false, true), (false, true)]
  let T := flattenPairs pairs ++ marker ++ tail
  have hp := runtimeRoundEntry_run_pairs [] pairs (marker ++ tail) false hsafe
  have hmFalse : run runtimeRoundEntryLocatorMachine 7
      ⟨lo false, 2 * pairs.length, T⟩ =
      ⟨done, 2 * pairs.length + 4, T⟩ := by
    refine runtimeRoundEntry_run_marker_toSelector T (2 * pairs.length)
      ?_ ?_ ?_ ?_ tailLo tailHi ?_ ?_ hnonsep
    · simp [T, marker, flattenPairs]
    · simp [T, marker, flattenPairs]
    · simp [T, marker, flattenPairs]
    · simp [T, marker, flattenPairs]
    · dsimp [T]; rw [htail]; simp [marker, flattenPairs]
    · dsimp [T]; rw [htail]; simp [marker, flattenPairs]
  have hmTrue : run runtimeRoundEntryLocatorMachine 7
      ⟨lo true, 2 * pairs.length, T⟩ =
      ⟨done, 2 * pairs.length + 4, T⟩ := by
    refine runtimeRoundEntry_run_marker_toSelector_afterSep T
      (2 * pairs.length) ?_ ?_ ?_ ?_ tailLo tailHi ?_ ?_ hnonsep
    · simp [T, marker, flattenPairs]
    · simp [T, marker, flattenPairs]
    · simp [T, marker, flattenPairs]
    · simp [T, marker, flattenPairs]
    · dsimp [T]; rw [htail]; simp [marker, flattenPairs]
    · dsimp [T]; rw [htail]; simp [marker, flattenPairs]
  have hp' : run runtimeRoundEntryLocatorMachine (2 * pairs.length)
      (init runtimeRoundEntryLocatorMachine T) =
      ⟨lo (runtimeEntryPrev false pairs), 2 * pairs.length, T⟩ := by
    simpa [T, marker, List.append_assoc] using hp
  rw [run_add]
  rw [hp']
  simpa [T, marker, List.append_assoc] using
    (show run runtimeRoundEntryLocatorMachine 7
        ⟨lo (runtimeEntryPrev false pairs), 2 * pairs.length, T⟩ =
          ⟨done, 2 * pairs.length + 4, T⟩ by
      cases hprev : runtimeEntryPrev false pairs
      · simpa [hprev] using hmFalse
      · simpa [hprev] using hmTrue)

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryLocator

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryLocator.runtimeRoundEntry_run_pairs
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRoundEntryLocator.runtimeRoundEntryLocator_run
