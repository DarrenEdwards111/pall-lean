import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeLeftSafety

/-!
# Unconditional reset-aware runtime output cashout

The runtime source archive intentionally resets to its own origin.  This file
places it behind the fixed-capacity truth output with `relativePrefixAdapter`,
then discharges the adapter's sole left-safety premise from the complete
scheduled runtime safety theorem.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRelativeOutput

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputCapacity
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupOutputRouter
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupDynamicRoute
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeStage
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceLookup
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeSourceSelect
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRelativePrefix
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeLeftSafety

def runtimeRelativeOutputSourceMachine (B : Nat) : Machine :=
  relativePrefixAdapter (2 * B + 2) sourceRuntimeLookupCore

def runtimeRelativeOutputSourceClock (B : Nat) (T : List Bool)
    (n : Nat) : Nat :=
  2 * B + 2 + 1 + relativeRunClock (2 * B + 2)
    sourceRuntimeLookupCore (init sourceRuntimeLookupCore T) n

def runtimeRelativeOutputRouteClock (B : Nat) (out T : List Bool)
    (n : Nat) : Nat :=
  runtimeRelativeOutputSourceClock B T n + 1 + outputRouteClock out

theorem runtimeRelativeOutputSource_run (B : Nat) (out T : List Bool)
    (n : Nat) (hout : out.length ≤ B)
    (hleft : LeftSafeRun sourceRuntimeLookupCore
      (init sourceRuntimeLookupCore T) n) :
    let cf := run sourceRuntimeLookupCore n (init sourceRuntimeLookupCore T)
    run (runtimeRelativeOutputSourceMachine B)
        (runtimeRelativeOutputSourceClock B T n)
        (init (runtimeRelativeOutputSourceMachine B) (outputCap B out ++ T)) =
      embedRelativeBody (2 * B + 2) sourceRuntimeLookupCore
        (outputCap B out) cf := by
  dsimp only
  have hlen : (outputCap B out).length = 2 * B + 2 :=
    outputCap_length B out hout
  exact relativePrefix_run (2 * B + 2) sourceRuntimeLookupCore
    (outputCap B out) T n hlen hleft

theorem runtimeRelativeOutputSource_route_false (B : Nat)
    (out T : List Bool) (n : Nat) (hout : out.length < B)
    (hleft : LeftSafeRun sourceRuntimeLookupCore
      (init sourceRuntimeLookupCore T) n)
    (hh : sourceRuntimeLookupCore.halt
      (run sourceRuntimeLookupCore n (init sourceRuntimeLookupCore T)).st = true)
    (ha : sourceRuntimeLookupCore.accept
      (run sourceRuntimeLookupCore n (init sourceRuntimeLookupCore T)).st = false) :
    let M := runtimeRelativeOutputSourceMachine B
    let cf := run sourceRuntimeLookupCore n (init sourceRuntimeLookupCore T)
    run (acceptRouteMachine M)
        (runtimeRelativeOutputRouteClock B out T n)
        (init (acceptRouteMachine M) (outputCap B out ++ T)) =
      embedFalseRouter M
        ⟨(6, ⟨0, by omega⟩, false), 2 * out.length + 3,
          outputCap B (out ++ [false]) ++ cf.tp⟩ := by
  dsimp only
  let cf := run sourceRuntimeLookupCore n (init sourceRuntimeLookupCore T)
  have hbody0 := runtimeRelativeOutputSource_run B out T n hout.le hleft
  have hbody : run (runtimeRelativeOutputSourceMachine B)
      (runtimeRelativeOutputSourceClock B T n)
      (init (runtimeRelativeOutputSourceMachine B) (outputCap B out ++ T)) =
      ⟨Sum.inr cf.st, (outputCap B out).length + cf.hd,
        outputCap B out ++ cf.tp⟩ := by
    simpa [embedRelativeBody, cf] using hbody0
  exact acceptRoute_output_false (runtimeRelativeOutputSourceMachine B)
    (outputCap B out ++ T) (runtimeRelativeOutputSourceClock B T n)
    B out cf.tp (Sum.inr cf.st) ((outputCap B out).length + cf.hd)
    hbody
    (by simpa [runtimeRelativeOutputSourceMachine, relativePrefixAdapter, cf]
      using hh)
    (by simpa [runtimeRelativeOutputSourceMachine, relativePrefixAdapter, cf]
      using ha) hout

theorem runtimeRelativeOutputSource_route_true (B : Nat)
    (out T : List Bool) (n : Nat) (hout : out.length < B)
    (hleft : LeftSafeRun sourceRuntimeLookupCore
      (init sourceRuntimeLookupCore T) n)
    (hh : sourceRuntimeLookupCore.halt
      (run sourceRuntimeLookupCore n (init sourceRuntimeLookupCore T)).st = true)
    (ha : sourceRuntimeLookupCore.accept
      (run sourceRuntimeLookupCore n (init sourceRuntimeLookupCore T)).st = true) :
    let M := runtimeRelativeOutputSourceMachine B
    let cf := run sourceRuntimeLookupCore n (init sourceRuntimeLookupCore T)
    run (acceptRouteMachine M)
        (runtimeRelativeOutputRouteClock B out T n)
        (init (acceptRouteMachine M) (outputCap B out ++ T)) =
      embedTrueRouter M
        ⟨(6, ⟨0, by omega⟩, false), 2 * out.length + 3,
          outputCap B (out ++ [true]) ++ cf.tp⟩ := by
  dsimp only
  let cf := run sourceRuntimeLookupCore n (init sourceRuntimeLookupCore T)
  have hbody0 := runtimeRelativeOutputSource_run B out T n hout.le hleft
  have hbody : run (runtimeRelativeOutputSourceMachine B)
      (runtimeRelativeOutputSourceClock B T n)
      (init (runtimeRelativeOutputSourceMachine B) (outputCap B out ++ T)) =
      ⟨Sum.inr cf.st, (outputCap B out).length + cf.hd,
        outputCap B out ++ cf.tp⟩ := by
    simpa [embedRelativeBody, cf] using hbody0
  exact acceptRoute_output_true (runtimeRelativeOutputSourceMachine B)
    (outputCap B out ++ T) (runtimeRelativeOutputSourceClock B T n)
    B out cf.tp (Sum.inr cf.st) ((outputCap B out).length + cf.hd)
    hbody
    (by simpa [runtimeRelativeOutputSourceMachine, relativePrefixAdapter, cf]
      using hh)
    (by simpa [runtimeRelativeOutputSourceMachine, relativePrefixAdapter, cf]
      using ha) hout

/-- The physical joined round is unconditional: it computes the live
scheduled literal from tape-resident source data, dynamically routes its real
accept bit, appends exactly that truth value, and preserves the evolved source
archive. -/
theorem scheduledRuntimeRelativeOutputSourceRoute (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length) :
    let B := (decodedLiterals x).length
    let schedule := literalTapeSchedule x w
    let preBlocks := schedule.take t
    let l := scheduledLiteral x t
    let out := (scheduledTruths x w).take t
    let T := sourceSelectorInput B t schedule
    let n := sourceRuntimeLookupClock (B - t) preBlocks w l
    let cf := run sourceRuntimeLookupCore n (init sourceRuntimeLookupCore T)
    let M := runtimeRelativeOutputSourceMachine B
    let clock := runtimeRelativeOutputRouteClock B out T n
    let bv := evalLit (fun k => w.getD k false) l
    HaltsBy (acceptRouteMachine M) (outputCap B out ++ T) clock ∧
      (run (acceptRouteMachine M) clock
        (init (acceptRouteMachine M) (outputCap B out ++ T))).tp =
        outputCap B (out ++ [bv]) ++ cf.tp := by
  dsimp only
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
  have hleft : LeftSafeRun sourceRuntimeLookupCore
      (init sourceRuntimeLookupCore T) n := by
    simpa [B, schedule, preBlocks, l, T, n] using
      sourceRuntimeLookup_leftSafe_scheduled x w ht
  by_cases hb : evalLit (fun k => w.getD k false) l = true
  · have hr := runtimeRelativeOutputSource_route_true B out T n hout hleft hh
      (by rw [ha, hb])
    constructor
    · change (acceptRouteMachine (runtimeRelativeOutputSourceMachine B)).halt
        (run (acceptRouteMachine (runtimeRelativeOutputSourceMachine B))
          (runtimeRelativeOutputRouteClock B out T n)
          (init (acceptRouteMachine (runtimeRelativeOutputSourceMachine B))
            (outputCap B out ++ T))).st = true
      rw [hr]
      rfl
    · rw [hr, hb]
      rfl
  · have hb0 : evalLit (fun k => w.getD k false) l = false := by
      simpa using hb
    have hr := runtimeRelativeOutputSource_route_false B out T n hout hleft hh
      (by rw [ha, hb0])
    constructor
    · change (acceptRouteMachine (runtimeRelativeOutputSourceMachine B)).halt
        (run (acceptRouteMachine (runtimeRelativeOutputSourceMachine B))
          (runtimeRelativeOutputRouteClock B out T n)
          (init (acceptRouteMachine (runtimeRelativeOutputSourceMachine B))
            (outputCap B out ++ T))).st = true
      rw [hr]
      rfl
    · rw [hr, hb0]
      rfl

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRelativeOutput

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRelativeOutput.runtimeRelativeOutputSource_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRelativeOutput.scheduledRuntimeRelativeOutputSourceRoute
