import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupRuntimeRelativePrefix
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitRep

/-!
# Charged local lookup: reset-aware ownership under `repMachine`

The physical runtime round owns an output-first tape.  The verified
`repMachine`, however, owns a marked countdown at the true tape origin and
starts its body there.  This file closes that generic ownership mismatch.

`runtimeCountdownBody B M` is a reset-aware lift of an arbitrary output-first
body `M` behind the fixed `cntT B j` region.  Every reset requested by `M` is
translated into a real reset, an exact rescan of the countdown, and resumption
at the output-first origin.  The outer `repMachine` therefore remains the sole
owner of the countdown, while `M` sees exactly its original tape and head
coordinates.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRepeatAdapter

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr (unaryD)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice (cntT cntT_length)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRep
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupLeftBoundaryTerminal
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRelativePrefix

/-- Run an output-first body behind the countdown owned by `repMachine`.
Unlike `fixedPrefixAdapter`, this lift relocates every body reset back to the
first cell after the countdown. -/
def runtimeCountdownBody (B : Nat) (M : Machine) : Machine :=
  relativePrefixAdapter (2 * B + 2) M

/-- Exact physical clock for one countdown-protected body execution. -/
def runtimeCountdownBodyClock (B : Nat) (M : Machine)
    (tail : List Bool) (bodyClock : Nat) : Nat :=
  2 * B + 3 +
    relativeRunClock (2 * B + 2) M (init M tail) bodyClock

/-- Exact one-round transport.  The marked countdown is preserved byte for
byte; the final head is shifted by precisely its physical width. -/
theorem runtimeCountdownBody_run (B j : Nat) (hj : j ≤ B)
    (M : Machine) (tail tail' : List Bool) (bodyClock : Nat)
    (sf : M.State) (pf : Nat)
    (hrun : run M bodyClock (init M tail) = ⟨sf, pf, tail'⟩)
    (hleft : LeftSafeRun M (init M tail) bodyClock) :
    run (runtimeCountdownBody B M)
        (runtimeCountdownBodyClock B M tail bodyClock)
        (init (runtimeCountdownBody B M) (cntT B j ++ tail)) =
      ⟨Sum.inr sf, 2 * B + 2 + pf, cntT B j ++ tail'⟩ := by
  have hcnt : (cntT B j).length = 2 * B + 2 := by
    simpa using cntT_length B j hj
  have h := relativePrefix_run (2 * B + 2) M
    (cntT B j) tail bodyClock hcnt hleft
  rw [hrun] at h
  simpa [runtimeCountdownBody, runtimeCountdownBodyClock,
    embedRelativeBody, hcnt, Nat.add_assoc] using h

theorem runtimeCountdownBody_halt (B : Nat) (M : Machine)
    (sf : M.State) (hh : M.halt sf = true) :
    (runtimeCountdownBody B M).halt (Sum.inr sf) = true := by
  simpa [runtimeCountdownBody, relativePrefixAdapter] using hh

/--
`repMachine` driven by a genuinely output-first physical round.

The premise speaks only about the body's native tape.  The theorem inserts
the live marked countdown, translates all body resets, shifts the physical
head, supplies the exact per-round premise required by `rep_run`, and then
uses the verified controller's own heal/terminal exit.  In particular, the
final `unaryD B` prefix is produced by `repMachine`; it is not postulated in
the output-first invariant.
-/
theorem runtimeRep_run (M : Machine) (B : Nat)
    (tail : Nat → List Bool) (bodyClock : Nat → Nat)
    (sf : Nat → M.State) (pf : Nat → Nat)
    (hrun : ∀ t, t < B →
      run M (bodyClock t) (init M (tail t)) =
        ⟨sf t, pf t, tail (t + 1)⟩)
    (hhalt : ∀ t, t < B → M.halt (sf t) = true)
    (hleft : ∀ t, t < B →
      LeftSafeRun M (init M (tail t)) (bodyClock t)) :
    let protectedClock := fun t =>
      runtimeCountdownBodyClock B M (tail t) (bodyClock t)
    run (repMachine (runtimeCountdownBody B M))
        (repRounds protectedClock B + (4 * B + 4))
        (init (repMachine (runtimeCountdownBody B M))
          (cntT B 0 ++ tail 0)) =
      ⟨Sum.inl (4, false), 2 * B + 1, unaryD B ++ tail B⟩ := by
  dsimp only
  apply rep_run (runtimeCountdownBody B M) B tail
    (fun t => runtimeCountdownBodyClock B M (tail t) (bodyClock t))
    (fun t => Sum.inr (sf t)) (fun t => 2 * B + 2 + pf t)
  intro t ht
  constructor
  · exact runtimeCountdownBody_run B (t + 1) (by omega) M
      (tail t) (tail (t + 1)) (bodyClock t) (sf t) (pf t)
      (hrun t ht) (hleft t ht)
  · exact runtimeCountdownBody_halt B M (sf t) (hhalt t ht)

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRepeatAdapter

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRepeatAdapter.runtimeCountdownBody_run
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRuntimeRepeatAdapter.runtimeRep_run
