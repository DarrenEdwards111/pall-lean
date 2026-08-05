import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeSourceLookup

/-!
# Charged local lookup: runtime source behind reserved output

This file gives the fixed runtime source/lookup core the physical layout
required by the verified dynamic output router:

    outputCap B out ++ runtimeSourceArchive.

Because `outputCap` has exact length `2B+2`, a length-directed prefix adapter
crosses it without confusing its live `01` terminator for a source delimiter.
The theorems below transport a complete prefix-safe runtime lookup, expose its
real accept bit, and complete either verified append branch while preserving
the evolved source archive byte-for-byte.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeOutputLayout

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupSuffixRun
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputRouter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLayoutBridge
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect

/-- The source core lifted behind the exact fixed-capacity output footprint. -/
def runtimeOutputSourceMachine (B : Nat) : Machine :=
  fixedPrefixAdapter (2 * B + 2) sourceRuntimeLookupCore

def runtimeOutputSourceClock (B n : Nat) : Nat :=
  2 * B + 2 + 1 + n

def runtimeOutputRouteClock (B : Nat) (out : List Bool) (n : Nat) : Nat :=
  runtimeOutputSourceClock B n + 1 + outputRouteClock out

/-- Exact physical transport behind `outputCap`.  The output region is
preserved byte-for-byte and the body accept bit is exposed by the adapter. -/
theorem runtimeOutputSource_run (B : Nat) (out T : List Bool) (n : Nat)
    (hout : out.length ≤ B)
    (hsafe : PrefixSafeRun sourceRuntimeLookupCore
      (init sourceRuntimeLookupCore T) n) :
    let cf := run sourceRuntimeLookupCore n
      (init sourceRuntimeLookupCore T)
    run (runtimeOutputSourceMachine B) (runtimeOutputSourceClock B n)
        (init (runtimeOutputSourceMachine B) (outputCap B out ++ T)) =
      embedFixedBody (2 * B + 2) sourceRuntimeLookupCore
        (outputCap B out) cf := by
  dsimp only
  have hlen : (outputCap B out).length = 2 * B + 2 :=
    outputCap_length B out hout
  exact fixedPrefix_run (2 * B + 2) sourceRuntimeLookupCore
    (outputCap B out) T n hlen hsafe

/-- Rejecting runtime lookup followed by the existing verified output router.
Only one reserved pair changes; the evolved source tape is untouched. -/
theorem runtimeOutputSource_route_false (B : Nat) (out T : List Bool)
    (n : Nat) (hout : out.length < B)
    (hsafe : PrefixSafeRun sourceRuntimeLookupCore
      (init sourceRuntimeLookupCore T) n)
    (hh : sourceRuntimeLookupCore.halt
      (run sourceRuntimeLookupCore n (init sourceRuntimeLookupCore T)).st = true)
    (ha : sourceRuntimeLookupCore.accept
      (run sourceRuntimeLookupCore n (init sourceRuntimeLookupCore T)).st = false) :
    let M := runtimeOutputSourceMachine B
    let cf := run sourceRuntimeLookupCore n (init sourceRuntimeLookupCore T)
    run (acceptRouteMachine M)
        (runtimeOutputSourceClock B n + 1 + outputRouteClock out)
        (init (acceptRouteMachine M) (outputCap B out ++ T)) =
      embedFalseRouter M
        ⟨(6, ⟨0, by omega⟩, false), 2 * out.length + 3,
          outputCap B (out ++ [false]) ++ cf.tp⟩ := by
  dsimp only
  let cf := run sourceRuntimeLookupCore n (init sourceRuntimeLookupCore T)
  have hbody0 := runtimeOutputSource_run B out T n hout.le hsafe
  have hbody : run (runtimeOutputSourceMachine B)
      (runtimeOutputSourceClock B n)
      (init (runtimeOutputSourceMachine B) (outputCap B out ++ T)) =
      ⟨Sum.inr cf.st, (outputCap B out).length + cf.hd,
        outputCap B out ++ cf.tp⟩ := by
    simpa [embedFixedBody, cf] using hbody0
  exact acceptRoute_output_false (runtimeOutputSourceMachine B)
    (outputCap B out ++ T) (runtimeOutputSourceClock B n) B out cf.tp
    (Sum.inr cf.st) ((outputCap B out).length + cf.hd)
    hbody (by simpa [runtimeOutputSourceMachine, fixedPrefixAdapter, cf] using hh)
    (by simpa [runtimeOutputSourceMachine, fixedPrefixAdapter, cf] using ha) hout

/-- Accepting branch of the same physical layout theorem. -/
theorem runtimeOutputSource_route_true (B : Nat) (out T : List Bool)
    (n : Nat) (hout : out.length < B)
    (hsafe : PrefixSafeRun sourceRuntimeLookupCore
      (init sourceRuntimeLookupCore T) n)
    (hh : sourceRuntimeLookupCore.halt
      (run sourceRuntimeLookupCore n (init sourceRuntimeLookupCore T)).st = true)
    (ha : sourceRuntimeLookupCore.accept
      (run sourceRuntimeLookupCore n (init sourceRuntimeLookupCore T)).st = true) :
    let M := runtimeOutputSourceMachine B
    let cf := run sourceRuntimeLookupCore n (init sourceRuntimeLookupCore T)
    run (acceptRouteMachine M)
        (runtimeOutputSourceClock B n + 1 + outputRouteClock out)
        (init (acceptRouteMachine M) (outputCap B out ++ T)) =
      embedTrueRouter M
        ⟨(6, ⟨0, by omega⟩, false), 2 * out.length + 3,
          outputCap B (out ++ [true]) ++ cf.tp⟩ := by
  dsimp only
  let cf := run sourceRuntimeLookupCore n (init sourceRuntimeLookupCore T)
  have hbody0 := runtimeOutputSource_run B out T n hout.le hsafe
  have hbody : run (runtimeOutputSourceMachine B)
      (runtimeOutputSourceClock B n)
      (init (runtimeOutputSourceMachine B) (outputCap B out ++ T)) =
      ⟨Sum.inr cf.st, (outputCap B out).length + cf.hd,
        outputCap B out ++ cf.tp⟩ := by
    simpa [embedFixedBody, cf] using hbody0
  exact acceptRoute_output_true (runtimeOutputSourceMachine B)
    (outputCap B out ++ T) (runtimeOutputSourceClock B n) B out cf.tp
    (Sum.inr cf.st) ((outputCap B out).length + cf.hd)
    hbody (by simpa [runtimeOutputSourceMachine, fixedPrefixAdapter, cf] using hh)
    (by simpa [runtimeOutputSourceMachine, fixedPrefixAdapter, cf] using ha) hout

/-- Scheduled branch-independent cashout.  Once the source core's exact
prefix-safety path is supplied, the physical joined machine appends precisely
the next scheduled truth bit and preserves the evolved archive suffix. -/
theorem scheduledRuntimeOutputSourceRoute (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length)
    (hsafe :
      let B := (decodedLiterals x).length
      let schedule := literalTapeSchedule x w
      let preBlocks := schedule.take t
      let l := scheduledLiteral x t
      PrefixSafeRun sourceRuntimeLookupCore
        (init sourceRuntimeLookupCore (sourceSelectorInput B t schedule))
        (sourceRuntimeLookupClock (B - t) preBlocks w l)) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    let preBlocks := schedule.take t
    let l := scheduledLiteral x t
    let out := (scheduledTruths x w).take t
    let T := sourceSelectorInput B t schedule
    let n := sourceRuntimeLookupClock (B - t) preBlocks w l
    let cf := run sourceRuntimeLookupCore n (init sourceRuntimeLookupCore T)
    let M := runtimeOutputSourceMachine B
    let clock := runtimeOutputRouteClock B out n
    let bv := evalLit (fun k => w.getD k false) l
    HaltsBy (acceptRouteMachine M) (outputCap B out ++ T) clock ∧
      (run (acceptRouteMachine M) clock
        (init (acceptRouteMachine M) (outputCap B out ++ T))).tp =
        outputCap B (out ++ [bv]) ++ cf.tp := by
  dsimp only at hsafe ⊢
  let B := (decodedLiterals x).length
  let schedule := literalTapeSchedule x w
  let preBlocks := schedule.take t
  let l := scheduledLiteral x t
  let out := (scheduledTruths x w).take t
  let T := sourceSelectorInput B t schedule
  let n := sourceRuntimeLookupClock (B - t) preBlocks w l
  let cf := run sourceRuntimeLookupCore n (init sourceRuntimeLookupCore T)
  have houtlen : out.length = t := by
    dsimp only [out]
    rw [List.length_take, scheduledTruths_length,
      Nat.min_eq_left (by simpa [B] using ht.le)]
  have hout : out.length < B := by simpa [houtlen, B] using ht
  have hs := sourceRuntimeLookup_accept_scheduled x w ht
  have hh : sourceRuntimeLookupCore.halt cf.st = true := by
    simpa [B, schedule, preBlocks, l, T, n, cf] using hs.1
  have ha : sourceRuntimeLookupCore.accept cf.st =
      evalLit (fun k => w.getD k false) l := by
    simpa [B, schedule, preBlocks, l, T, n, cf] using hs.2.1
  by_cases hb : evalLit (fun k => w.getD k false) l = true
  · have hr := runtimeOutputSource_route_true B out T n hout hsafe hh
      (by rw [ha, hb])
    constructor
    · change (acceptRouteMachine (runtimeOutputSourceMachine B)).halt
        (run (acceptRouteMachine (runtimeOutputSourceMachine B))
          (runtimeOutputRouteClock B out n)
          (init (acceptRouteMachine (runtimeOutputSourceMachine B))
            (outputCap B out ++ T))).st = true
      rw [runtimeOutputRouteClock, hr]
      rfl
    · rw [runtimeOutputRouteClock, hr, hb]
      rfl
  · have hb0 : evalLit (fun k => w.getD k false) l = false := by
      simpa using hb
    have hr := runtimeOutputSource_route_false B out T n hout hsafe hh
      (by rw [ha, hb0])
    constructor
    · change (acceptRouteMachine (runtimeOutputSourceMachine B)).halt
        (run (acceptRouteMachine (runtimeOutputSourceMachine B))
          (runtimeOutputRouteClock B out n)
          (init (acceptRouteMachine (runtimeOutputSourceMachine B))
            (outputCap B out ++ T))).st = true
      rw [runtimeOutputRouteClock, hr]
      rfl
    · rw [runtimeOutputRouteClock, hr, hb0]
      rfl

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeOutputLayout

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeOutputLayout.runtimeOutputSource_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeOutputLayout.runtimeOutputSource_route_false
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeOutputLayout.runtimeOutputSource_route_true
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeOutputLayout.scheduledRuntimeOutputSourceRoute
