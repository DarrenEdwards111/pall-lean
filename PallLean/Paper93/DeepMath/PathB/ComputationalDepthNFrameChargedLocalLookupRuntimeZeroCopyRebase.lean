import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeTailPreservation

/-!
# Zero-copy runtime source rebasing

The future source archive already survives a completed lookup/cashout round at
an exact boundary.  Round progression therefore needs no payload copy: it can
replace only a suffix of the consumed workspace by a fresh selector countdown
and boundary, immediately before the preserved archive.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeZeroCopyRebase

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceCompact
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRelativeOutput
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeTailPreservation

/-- The minimal canonical selector prefix for a fresh archive of `d` blocks. -/
def zeroCopyRebasePrefix (d : Nat) : List Bool :=
  flattenPairs (List.replicate d (true, true) ++ [(false, true)])

theorem zeroCopyRebasePrefix_length (d : Nat) :
    (zeroCopyRebasePrefix d).length = 2 * d + 2 := by
  simp [zeroCopyRebasePrefix, flattenPairs_length]

/-- A fresh countdown/boundary followed by the untouched archive is exactly
the canonical round-zero selector input for that remaining schedule. -/
theorem zeroCopyRebasePrefix_archive (rest : List (List Bool)) :
    zeroCopyRebasePrefix rest.length ++ selectedTail rest =
      sourceSelectorInput rest.length 0 rest := by
  simp [zeroCopyRebasePrefix, selectedTail, sourceSelectorInput,
    sourceArchive, flattenPairs_append, flattenPairs, List.append_assoc]

/-- Pure tape endpoint of the rearm operation.  It overwrites only the last
`|zeroCopyRebasePrefix d|` cells before boundary `R`. -/
def installZeroCopyRebase (T : List Bool) (R d : Nat) : List Bool :=
  T.take (R - (zeroCopyRebasePrefix d).length) ++
    zeroCopyRebasePrefix d ++ T.drop R

theorem installZeroCopyRebase_drop (T : List Bool) (R d : Nat)
    (hfit : (zeroCopyRebasePrefix d).length ≤ R)
    (hR : R ≤ T.length) :
    (installZeroCopyRebase T R d).drop
        (R - (zeroCopyRebasePrefix d).length) =
      zeroCopyRebasePrefix d ++ T.drop R := by
  rw [installZeroCopyRebase]
  have htake : (T.take (R - (zeroCopyRebasePrefix d).length)).length =
      R - (zeroCopyRebasePrefix d).length := by
    rw [List.length_take, Nat.min_eq_left]
    omega
  rw [List.drop_append]
  simp [htake]

theorem installZeroCopyRebase_future (T : List Bool) (R d : Nat)
    (hfit : (zeroCopyRebasePrefix d).length ≤ R)
    (hR : R ≤ T.length) :
    (installZeroCopyRebase T R d).drop R = T.drop R := by
  have hdrop := installZeroCopyRebase_drop T R d hfit hR
  calc
    (installZeroCopyRebase T R d).drop R =
        ((installZeroCopyRebase T R d).drop
          (R - (zeroCopyRebasePrefix d).length)).drop
            (zeroCopyRebasePrefix d).length := by
              rw [List.drop_drop]
              congr 2
              omega
    _ = T.drop R := by rw [hdrop, List.drop_left]

/-- The fresh remaining selector prefix always fits before the future archive
boundary produced by a live round.  In particular, it uses only consumed
source workspace, never output capacity or future payload cells. -/
theorem scheduled_zeroCopyRebase_fits
    (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    let preBlocks := schedule.take t
    let bits := literalLookupTape w (scheduledLiteral x t)
    let rest := schedule.drop (t + 1)
    let pre := selectedPrefix (B - t) preBlocks
    (zeroCopyRebasePrefix rest.length).length ≤
      pre.length + 2 * bits.length + 4 := by
  dsimp only
  let B := (decodedLiterals x).length
  let schedule := literalTapeSchedule x w
  let preBlocks := schedule.take t
  let rest := schedule.drop (t + 1)
  have hslen : schedule.length = B := by
    simp [schedule, B, literalTapeSchedule]
  have hrest : rest.length = B - (t + 1) := by
    simp [rest, hslen]
  rw [zeroCopyRebasePrefix_length, hrest]
  simp [selectedPrefix, selectedPrefixPairs]
  omega

/-- Exact zero-copy next-state endpoint after a complete physical round.
The rearmed suffix is definitionally a canonical selector input for precisely
the unprocessed schedule, while the archive itself remains byte-for-byte the
same list already present after cashout. -/
theorem scheduledRuntimeRelativeOutput_zeroCopyRebase
    (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length)
    (htnext : t + 1 < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    let preBlocks := schedule.take t
    let l := scheduledLiteral x t
    let bits := literalLookupTape w l
    let rest := schedule.drop (t + 1)
    let pre := selectedPrefix (B - t) preBlocks
    let out := (scheduledTruths x w).take t
    let T := sourceSelectorInput B t schedule
    let n := sourceRuntimeLookupClock (B - t) preBlocks w l
    let M := runtimeRelativeOutputSourceMachine B
    let clock := runtimeRelativeOutputRouteClock B out T n
    let rcf := run (acceptRouteMachine M) clock
      (init (acceptRouteMachine M) (outputCap B out ++ T))
    let R := 2 * B + 2 + pre.length + 2 * bits.length + 4
    (installZeroCopyRebase rcf.tp R rest.length).drop
        (R - (zeroCopyRebasePrefix rest.length).length) =
      sourceSelectorInput rest.length 0 rest := by
  dsimp only
  let B := (decodedLiterals x).length
  let schedule := literalTapeSchedule x w
  let preBlocks := schedule.take t
  let l := scheduledLiteral x t
  let bits := literalLookupTape w l
  let rest := schedule.drop (t + 1)
  let pre := selectedPrefix (B - t) preBlocks
  let out := (scheduledTruths x w).take t
  let T := sourceSelectorInput B t schedule
  let n := sourceRuntimeLookupClock (B - t) preBlocks w l
  let M := runtimeRelativeOutputSourceMachine B
  let clock := runtimeRelativeOutputRouteClock B out T n
  let rcf := run (acceptRouteMachine M) clock
    (init (acceptRouteMachine M) (outputCap B out ++ T))
  let R := 2 * B + 2 + pre.length + 2 * bits.length + 4
  have hfuture : rcf.tp.drop R = selectedTail rest := by
    simpa [B, schedule, preBlocks, l, bits, rest, pre, out, T, n, M,
      clock, rcf, R] using
      scheduledRuntimeRelativeOutput_futureArchive x w ht
  have hfit : (zeroCopyRebasePrefix rest.length).length ≤ R := by
    have hs := scheduled_zeroCopyRebase_fits x w ht
    dsimp only at hs
    have hs' : (zeroCopyRebasePrefix rest.length).length ≤
        pre.length + 2 * bits.length + 4 := by
      simpa [B, schedule, preBlocks, l, bits, rest, pre] using hs
    dsimp [R]
    omega
  have hR : R ≤ rcf.tp.length := by
    have hrestpos : 0 < (selectedTail rest).length := by
      have hrs : rest ≠ [] := by
        apply List.ne_nil_of_length_pos
        simp [rest, schedule, literalTapeSchedule]
        omega
      obtain ⟨a, as, hr⟩ := List.exists_cons_of_ne_nil hrs
      rw [hr]
      simp [selectedTail, freshSourceBlock, flattenPairs_length]
    have hlen := congrArg List.length hfuture
    simp only [List.length_drop] at hlen
    omega
  rw [installZeroCopyRebase_drop rcf.tp R rest.length hfit hR,
    hfuture, zeroCopyRebasePrefix_archive]

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeZeroCopyRebase

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeZeroCopyRebase.zeroCopyRebasePrefix_archive
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeZeroCopyRebase.scheduled_zeroCopyRebase_fits
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeZeroCopyRebase.scheduledRuntimeRelativeOutput_zeroCopyRebase
