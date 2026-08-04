import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNFrameChargedLocalLookupScheduleBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitRep

/-!
# Charged local verifier: runtime lookup-repeat controller

The repository already contains a verified finite-control `repMachine`
combinator.  It marks a runtime countdown cell, resets into a body machine,
waits for that body to halt, resets back to the loop, and finally heals its
countdown tape.  This file instantiates the combinator's variable round clock
with the decoded SAT literal schedule.

The result is both operational and quantitative.  The actual controller's
scan/mark/return/heal clock is polynomial, not merely the sum of idealized
body calls, and `rep_run` gives the exact tape evolution under one explicit
per-literal body invariant.  That invariant now isolates the final wiring
task: adapt the prefixed loop tape to `masterM`'s canonical lookup tape and
write the returned truth bit before resuming.
-/

namespace PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController

open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster (masterM)
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr (unaryD)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice (cntT)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRep
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLiteralWeld
open PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupScheduleBound

/-! ## The runtime-indexed body clock -/

/-- The `t`th decoded literal, with an irrelevant default beyond the schedule. -/
def scheduledLiteral (x : List Bool) (t : Nat) : Lit :=
  (decodedLiterals x).getD t (0, false)

theorem scheduledLiteral_mem (x : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length) :
    scheduledLiteral x t ∈ decodedLiterals x := by
  rw [scheduledLiteral, List.getD_eq_getElem _ _ ht]
  exact List.getElem_mem ht

/-- Exact proved `masterM` clock assigned to round `t`. -/
def lookupRoundClock (x w : List Bool) (t : Nat) : Nat :=
  literalLookupCost w (scheduledLiteral x t)

theorem lookupRoundClock_le (x w : List Bool) {t : Nat}
    (ht : t < (decodedLiterals x).length) :
    lookupRoundClock x w t ≤ 200 * (x.length + 1) ^ 2 := by
  exact le_trans
    (literalLookupCost_le x w (scheduledLiteral_mem x ht))
    (literalLookupEnvelope_le x.length)

/-! ## The verified controller overhead -/

theorem repRounds_prefix_le (clk : Nat → Nat) (rounds cap k : Nat)
    (hk : k ≤ rounds) (hclk : ∀ t, t < rounds → clk t ≤ cap) :
    repRounds clk k ≤ k * (2 * rounds + 3 + cap) := by
  induction k with
  | zero => simp [repRounds]
  | succ k ih =>
      have hklt : k < rounds := by omega
      have hstep : 2 * k + 2 + (clk k + 1) ≤ 2 * rounds + 3 + cap := by
        have hc := hclk k hklt
        omega
      rw [repRounds]
      calc
        repRounds clk k + (2 * k + 2 + (clk k + 1))
            ≤ k * (2 * rounds + 3 + cap) +
                (2 * k + 2 + (clk k + 1)) :=
          Nat.add_le_add_right (ih (by omega)) _
        _ ≤ k * (2 * rounds + 3 + cap) +
                (2 * rounds + 3 + cap) :=
          Nat.add_le_add_left hstep _
        _ = (k + 1) * (2 * rounds + 3 + cap) := by ring

/-- A quartic envelope including every repeat-controller transition. -/
def lookupRepeatBound (n : Nat) : Nat :=
  213 * (n + 1) ^ 4

theorem lookupRepeatBound_poly : PolyBounded lookupRepeatBound :=
  ⟨213, 4, fun _ => le_rfl⟩

theorem lookupRepeatClock_le (x w : List Bool) :
    repRounds (lookupRoundClock x w) (decodedLiterals x).length +
        (4 * (decodedLiterals x).length + 4)
      ≤ lookupRepeatBound x.length := by
  let B := (decodedLiterals x).length
  let A := (x.length + 1) ^ 2
  have hB0 : B ≤ x.length * x.length := decodedLiterals_length_le x
  have hn2 : x.length * x.length ≤ A := by
    dsimp [A]
    nlinarith [Nat.zero_le x.length]
  have hB : B ≤ A := le_trans hB0 hn2
  have hA : 1 ≤ A := by
    dsimp [A]
    exact Nat.one_le_pow _ _ (by omega)
  have hround := repRounds_prefix_le (lookupRoundClock x w) B (200 * A) B
    (le_refl B) (fun t ht => by
      dsimp [A]
      exact lookupRoundClock_le x w ht)
  have hbracket : 2 * B + 3 + 200 * A ≤ 205 * A := by
    nlinarith
  have hmain : B * (2 * B + 3 + 200 * A) ≤ 205 * A * A := by
    calc
      B * (2 * B + 3 + 200 * A) ≤ A * (205 * A) :=
        Nat.mul_le_mul hB hbracket
      _ = 205 * A * A := by ring
  have htail : 4 * B + 4 ≤ 8 * A * A := by
    have hsmall : 4 * B + 4 ≤ 8 * A := by nlinarith
    exact le_trans hsmall (by nlinarith)
  calc
    repRounds (lookupRoundClock x w) B + (4 * B + 4)
        ≤ B * (2 * B + 3 + 200 * A) + (4 * B + 4) :=
      Nat.add_le_add_right hround _
    _ ≤ 205 * A * A + 8 * A * A := Nat.add_le_add hmain htail
    _ = lookupRepeatBound x.length := by
      simp only [lookupRepeatBound]
      dsimp [A]
      ring

/-! ## Exact reset/resume tape invariant -/

/--
The existing runtime controller performs the complete lookup schedule once a
body theorem supplies the one-round tape evolution.  The hypothesis is now
the sole operational seam: on the marked countdown prefix, stage the `t`th
canonical lookup, run `masterM`, preserve the prefix, append its truth bit to
the evolving output region, and halt so the controller can resume.
-/
theorem lookupRepeatController_run (x w : List Bool)
    (rest : Nat → List Bool)
    (sf : Nat → masterM.State) (pf : Nat → Nat)
    (hbody : ∀ t, t < (decodedLiterals x).length →
      run masterM (lookupRoundClock x w t)
          (init masterM
            (cntT (decodedLiterals x).length (t + 1) ++ rest t))
        = ⟨sf t, pf t,
            cntT (decodedLiterals x).length (t + 1) ++ rest (t + 1)⟩ ∧
          masterM.halt (sf t) = true) :
    run (repMachine masterM)
        (repRounds (lookupRoundClock x w) (decodedLiterals x).length +
          (4 * (decodedLiterals x).length + 4))
        (init (repMachine masterM)
          (cntT (decodedLiterals x).length 0 ++ rest 0))
      = ⟨Sum.inl (4, false), 2 * (decodedLiterals x).length + 1,
          unaryD (decodedLiterals x).length ++
            rest (decodedLiterals x).length⟩ :=
  rep_run masterM (decodedLiterals x).length rest
    (lookupRoundClock x w) sf pf hbody

end PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController

#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController.scheduledLiteral_mem
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController.repRounds_prefix_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController.lookupRepeatBound_poly
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController.lookupRepeatClock_le
#print axioms PallLean.Paper93.DeepMath.PathB.NFrameChargedLocalLookupRepeatController.lookupRepeatController_run
