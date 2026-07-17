import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitMorphChain
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitFence

/-!
# Cook–Levin M2 emitter — THE FENCE AT THE SUPPLIED-BOUND CONVENTION

The capstone of the arming-morph arc.  The morph chain composed with the closed emitter
core gives ONE machine that carries the supplied-bound input encoding — counters and
the raw input transcription, with NO computed content — through the armed six-region
layout to the emitted Cook–Levin reduction, within a `PolyBounded` clock:

  `PolyComputableVia (encTape0 clock) decodeTape
     (fun x => emittedReduction M x (clock |x|))`.

This strengthens `emitsTableauT` (the preloaded-cells convention) to the sanctioned
supplied-bound convention: every computed bit of the emitter's working tape is now
machine-computed.  The `PolyBounded` majorant for the morph's clock comes from the
per-pass round bounds and the `ilpClock_le` polynomial cap.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphFence

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitClockBounds3
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInitLoop
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInitLoopP
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPipeline (encTape coreClock pipeline_decodes)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitTapeCodec (decodeTape)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCore (emitterCoreMachine)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPackage2 (emittedReduction)
open PallLean.Paper93.DeepMath.PathB.CookLevinInitAccept (acceptStates)
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction (Satisfiable)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitFinale
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitFence
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorph
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphSub
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT1
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphFill
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT2
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT3
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT4
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT5
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT6
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphChain

/-! ## Round-sum bounds -/

theorem subRounds_le (B P : ℕ) : ∀ k, subRounds B P k ≤ k * (8 * B + 2 * P + 4 * k + 26)
  | 0 => by simp [subRounds]
  | k + 1 => by
    have ih := subRounds_le B P k
    have h1 : (k + 1) * (8 * B + 2 * P + 4 * k + 26)
        = k * (8 * B + 2 * P + 4 * k + 26) + (8 * B + 2 * P + 4 * k + 26) := by ring
    have h2 : (k + 1) * (8 * B + 2 * P + 4 * k + 26)
        ≤ (k + 1) * (8 * B + 2 * P + 4 * (k + 1) + 26) :=
      Nat.mul_le_mul_left _ (by omega)
    simp only [subRounds]
    omega

theorem t1Rounds_le (B n : ℕ) : ∀ k, t1Rounds B n k ≤ k * (8 * B + 2 * n + 4 * k + 24)
  | 0 => by simp [t1Rounds]
  | k + 1 => by
    have ih := t1Rounds_le B n k
    have h1 : (k + 1) * (8 * B + 2 * n + 4 * k + 24)
        = k * (8 * B + 2 * n + 4 * k + 24) + (8 * B + 2 * n + 4 * k + 24) := by ring
    have h2 : (k + 1) * (8 * B + 2 * n + 4 * k + 24)
        ≤ (k + 1) * (8 * B + 2 * n + 4 * (k + 1) + 24) :=
      Nat.mul_le_mul_left _ (by omega)
    simp only [t1Rounds]
    omega

theorem t2Rounds_le (B P n : ℕ) :
    ∀ k, t2Rounds B P n k ≤ k * (10 * B + 2 * P + 4 * n + 4 * k + 30)
  | 0 => by simp [t2Rounds]
  | k + 1 => by
    have ih := t2Rounds_le B P n k
    have h1 : (k + 1) * (10 * B + 2 * P + 4 * n + 4 * k + 30)
        = k * (10 * B + 2 * P + 4 * n + 4 * k + 30)
          + (10 * B + 2 * P + 4 * n + 4 * k + 30) := by ring
    have h2 : (k + 1) * (10 * B + 2 * P + 4 * n + 4 * k + 30)
        ≤ (k + 1) * (10 * B + 2 * P + 4 * n + 4 * (k + 1) + 30) :=
      Nat.mul_le_mul_left _ (by omega)
    simp only [t2Rounds]
    omega

theorem t3Rounds_le (B P : ℕ) : ∀ k, t3Rounds B P k ≤ k * (2 * B + 2 * P + 2 * k + 10)
  | 0 => by simp [t3Rounds]
  | k + 1 => by
    have ih := t3Rounds_le B P k
    have h1 : (k + 1) * (2 * B + 2 * P + 2 * k + 10)
        = k * (2 * B + 2 * P + 2 * k + 10) + (2 * B + 2 * P + 2 * k + 10) := by ring
    have h2 : (k + 1) * (2 * B + 2 * P + 2 * k + 10)
        ≤ (k + 1) * (2 * B + 2 * P + 2 * (k + 1) + 10) :=
      Nat.mul_le_mul_left _ (by omega)
    simp only [t3Rounds]
    omega

theorem t4Rounds_le (B P : ℕ) : ∀ k, t4Rounds B P k ≤ k * (2 * B + 4 * P + 2 * k + 16)
  | 0 => by simp [t4Rounds]
  | k + 1 => by
    have ih := t4Rounds_le B P k
    have h1 : (k + 1) * (2 * B + 4 * P + 2 * k + 16)
        = k * (2 * B + 4 * P + 2 * k + 16) + (2 * B + 4 * P + 2 * k + 16) := by ring
    have h2 : (k + 1) * (2 * B + 4 * P + 2 * k + 16)
        ≤ (k + 1) * (2 * B + 4 * P + 2 * (k + 1) + 16) :=
      Nat.mul_le_mul_left _ (by omega)
    simp only [t4Rounds]
    omega

theorem t5Rounds_le (B P : ℕ) : ∀ k, t5Rounds B P k ≤ k * (4 * B + 4 * P + 2 * k + 24)
  | 0 => by simp [t5Rounds]
  | k + 1 => by
    have ih := t5Rounds_le B P k
    have h1 : (k + 1) * (4 * B + 4 * P + 2 * k + 24)
        = k * (4 * B + 4 * P + 2 * k + 24) + (4 * B + 4 * P + 2 * k + 24) := by ring
    have h2 : (k + 1) * (4 * B + 4 * P + 2 * k + 24)
        ≤ (k + 1) * (4 * B + 4 * P + 2 * (k + 1) + 24) :=
      Nat.mul_le_mul_left _ (by omega)
    simp only [t5Rounds]
    omega

theorem t6Rounds_le (B P : ℕ) : ∀ k, t6Rounds B P k ≤ k * (4 * B + 6 * P + 2 * k + 28)
  | 0 => by simp [t6Rounds]
  | k + 1 => by
    have ih := t6Rounds_le B P k
    have h1 : (k + 1) * (4 * B + 6 * P + 2 * k + 28)
        = k * (4 * B + 6 * P + 2 * k + 28) + (4 * B + 6 * P + 2 * k + 28) := by ring
    have h2 : (k + 1) * (4 * B + 6 * P + 2 * k + 28)
        ≤ (k + 1) * (4 * B + 6 * P + 2 * (k + 1) + 28) :=
      Nat.mul_le_mul_left _ (by omega)
    simp only [t6Rounds]
    omega

/-! ## The chain-clock majorant -/

/-- An explicit polynomial majorant for the morph chain's clock. -/
def morphClockMaj (bl B P n : ℕ) : ℕ :=
  ((P + 1) * (bl * ilpCap (4 * B + 8) (P + 1) n
        (0 + (P + 1) * (bl * (P + 1 + 1) + 1) + bl * (P + 1 + 1))
      + (6 * (4 * B + 8) + 10 * (P + 1) + 8 * n
        + 2 * (0 + (P + 1) * (bl * (P + 1 + 1) + 1) + bl * (P + 1 + 1)) + 29))
    + (4 * (4 * B + 8) + 4 * (P + 1) + 4 * n + 10)) + 1
  + ((n * (8 * B + 2 * P + 4 * n + 26) + (8 * B + 2 * P + 4 * n + 24)) + 1
  + ((B * (8 * B + 2 * n + 4 * B + 24) + (12 * B + 2 * P + 26)) + 1
  + ((8 * B + 2 * P + 21) + 1
  + (((P + 1) * (10 * B + 2 * P + 4 * n + 4 * (P + 1) + 30)
      + ((8 * B + 4 * P + 4 * n + 28) + ((2 * B + 2 * P + 9)
        + (8 * B + 4 * P + 4 * n + 27)))) + 1
  + (((2 * B + 2 * P + 6) + (P * (2 * B + 2 * P + 2 * P + 10)
      + ((2 * B + 4 * P + 14) + (2 * B + 2 * P + 3)))) + 1
  + (((2 * B + 4 * P + 14) + (B * (2 * B + 4 * P + 2 * B + 16)
      + ((4 * B + 4 * P + 20) + (2 * B + 1)))) + 1
  + (((4 * B + 4 * P + 22) + (P * (4 * B + 4 * P + 2 * P + 24)
      + ((4 * B + 6 * P + 24) + (2 * B + 2 * P + 3)))) + 1
  + ((4 * B + 6 * P + 26) + (P * (4 * B + 6 * P + 2 * P + 28)
      + ((4 * B + 8 * P + 28) + (2 * B + 2 * P + 3)))))))))))

/-- The chain's clock is under the majorant. -/
theorem morphChainClock_le (clock : ℕ → ℕ) (n : ℕ) :
    morphChainClock clock n
      ≤ morphClockMaj initCellBody.length (clock n) (n + clock n) n := by
  have h1 := ilpClock_le initCellBody (4 * clock n + 8) (n + clock n + 1) n 0
  have h2 := subRounds_le (clock n) (n + clock n) n
  have h3 := t1Rounds_le (clock n) n (clock n)
  have h4 := t2Rounds_le (clock n) (n + clock n) n (n + clock n + 1)
  have h5 := t3Rounds_le (clock n) (n + clock n) (n + clock n)
  have h6 := t4Rounds_le (clock n) (n + clock n) (clock n)
  have h7 := t5Rounds_le (clock n) (n + clock n) (n + clock n)
  have h8 := t6Rounds_le (clock n) (n + clock n) (n + clock n)
  rw [morphChainClock, morphClockMaj, subClock, t1Clock, fillClock, t2Clock, t3Clock,
    t4Clock, t5Clock, t6Clock]
  omega

/-! ## The composed transducer -/

/-- **The full emitter**: the arming morph followed by the emitter core. -/
noncomputable def fullEmitter (M : Machine) : Machine := seqMachine morphChain (emitterCoreMachine M)

/-- Its polynomial clock. -/
def fullClock (M : Machine) (clock : ℕ → ℕ) (n : ℕ) : ℕ :=
  morphChainClock clock n + 1 + ECB (Fintype.card M.State) (clock n) (n + clock n)

set_option maxHeartbeats 3200000 in
/-- **THE FULL EMITTER RUNS**: from the supplied-bound encoding to the raw final
pipeline tape. -/
theorem fullEmitter_run (M : Machine) (clock : ℕ → ℕ) (x : List Bool)
    (hclk : 0 < clock x.length) :
    run (fullEmitter M) (fullClock M clock x.length)
      (init (fullEmitter M) (encTape0 clock x))
      = ⟨Sum.inr (run (emitterCoreMachine M)
            (ECB (Fintype.card M.State) (clock x.length) (x.length + clock x.length))
            (init (emitterCoreMachine M) (encTape clock x))).st,
          (run (emitterCoreMachine M)
            (ECB (Fintype.card M.State) (clock x.length) (x.length + clock x.length))
            (init (emitterCoreMachine M) (encTape clock x))).hd,
          (run (emitterCoreMachine M)
            (ECB (Fintype.card M.State) (clock x.length) (x.length + clock x.length))
            (init (emitterCoreMachine M) (encTape clock x))).tp⟩ := by
  have h1 := morphChain_run clock x
  have hpa := pipeline_at M clock x
    (ECB (Fintype.card M.State) (clock x.length) (x.length + clock x.length)) hclk
    (coreClock_le M clock x)
  exact seq_run morphChain (emitterCoreMachine M) _ _ _ _ _ _ _ _ _ h1
    morphChain_halt rfl hpa.1

/-! ## THE FENCE AT THE SUPPLIED-BOUND CONVENTION -/

/-- **The fence**: the emitted reduction is poly-computable from the supplied-bound
encoding — counters and the raw input transcription only, no computed content. -/
def EmitsTableau0 (M : Machine) (clock : ℕ → ℕ) : Prop :=
  PolyComputableVia (encTape0 clock) decodeTape
    (fun x => emittedReduction M x (clock x.length))

set_option maxHeartbeats 3200000 in
/-- **THE FENCE, DISCHARGED AT THE SUPPLIED-BOUND CONVENTION.** -/
theorem emitsTableau0 (M : Machine) (clock : ℕ → ℕ) (hAcc : acceptStates M ≠ [])
    (hclk : ∀ n, 0 < clock n) (hpoly : PolyBounded clock) :
    EmitsTableau0 M clock := by
  have hP : PolyBounded (fun n => n + clock n) := PB_add PB_id hpoly
  have hN : PolyBounded (fun n => n + clock n + 1) := PB_add hP (PB_const 1)
  have hG : PolyBounded (fun n => 4 * clock n + 8) :=
    PB_add (PB_mul (PB_const 4) hpoly) (PB_const 8)
  have hLM : PolyBounded (fun n => 0 + (n + clock n + 1)
      * (initCellBody.length * (n + clock n + 1 + 1) + 1)
      + initCellBody.length * (n + clock n + 1 + 1)) :=
    PB_add (PB_add (PB_const 0) (PB_mul hN (PB_add (PB_mul
        (PB_const initCellBody.length) (PB_add hN (PB_const 1))) (PB_const 1))))
      (PB_mul (PB_const initCellBody.length) (PB_add hN (PB_const 1)))
  have hCap : PolyBounded (fun n => ilpCap (4 * clock n + 8) (n + clock n + 1) n
      (0 + (n + clock n + 1) * (initCellBody.length * (n + clock n + 1 + 1) + 1)
        + initCellBody.length * (n + clock n + 1 + 1))) :=
    PB_add (PB_add (PB_add
      (PB_mul hN (PB_add (PB_add (PB_add (PB_add (PB_add
        (PB_mul (PB_const 2) hG) (PB_mul (PB_const 4) hN))
        (PB_mul (PB_const 4) PB_id)) (PB_mul (PB_const 2) hLM)) (PB_const 14))
        (PB_mul (PB_const 2) hN)))
      (PB_add (PB_add (PB_add (PB_add (PB_add
        (PB_mul (PB_const 2) hG) (PB_mul (PB_const 4) hN))
        (PB_mul (PB_const 4) PB_id)) (PB_mul (PB_const 2) hLM))
        (PB_mul (PB_const 2) hN)) (PB_const 14)))
      (PB_add (PB_add (PB_add (PB_add (PB_mul (PB_const 2) hG)
        (PB_mul (PB_const 2) hN)) (PB_mul (PB_const 4) PB_id))
        (PB_mul (PB_const 2) hN)) (PB_const 8)))
      (PB_add (PB_add (PB_add (PB_add (PB_mul (PB_const 2) hG)
        (PB_mul (PB_const 4) hN)) (PB_mul (PB_const 4) PB_id))
        (PB_mul (PB_const 2) hLM)) (PB_const 15))
  -- The nine pass-majorant pieces.
  have hp1 : PolyBounded (fun n => (n + clock n + 1)
      * (initCellBody.length * ilpCap (4 * clock n + 8) (n + clock n + 1) n
          (0 + (n + clock n + 1) * (initCellBody.length * (n + clock n + 1 + 1) + 1)
            + initCellBody.length * (n + clock n + 1 + 1))
        + (6 * (4 * clock n + 8) + 10 * (n + clock n + 1) + 8 * n
          + 2 * (0 + (n + clock n + 1)
              * (initCellBody.length * (n + clock n + 1 + 1) + 1)
            + initCellBody.length * (n + clock n + 1 + 1)) + 29))
      + (4 * (4 * clock n + 8) + 4 * (n + clock n + 1) + 4 * n + 10)) :=
    PB_add (PB_mul hN (PB_add (PB_mul (PB_const initCellBody.length) hCap)
      (PB_add (PB_add (PB_add (PB_add (PB_mul (PB_const 6) hG)
        (PB_mul (PB_const 10) hN)) (PB_mul (PB_const 8) PB_id))
        (PB_mul (PB_const 2) hLM)) (PB_const 29))))
      (PB_add (PB_add (PB_add (PB_mul (PB_const 4) hG) (PB_mul (PB_const 4) hN))
        (PB_mul (PB_const 4) PB_id)) (PB_const 10))
  have hp2 : PolyBounded (fun n => n * (8 * clock n + 2 * (n + clock n) + 4 * n + 26)
      + (8 * clock n + 2 * (n + clock n) + 4 * n + 24)) :=
    PB_add (PB_mul PB_id (PB_add (PB_add (PB_add (PB_mul (PB_const 8) hpoly)
      (PB_mul (PB_const 2) hP)) (PB_mul (PB_const 4) PB_id)) (PB_const 26)))
      (PB_add (PB_add (PB_add (PB_mul (PB_const 8) hpoly) (PB_mul (PB_const 2) hP))
        (PB_mul (PB_const 4) PB_id)) (PB_const 24))
  have hp3 : PolyBounded (fun n => clock n
      * (8 * clock n + 2 * n + 4 * clock n + 24)
      + (12 * clock n + 2 * (n + clock n) + 26)) :=
    PB_add (PB_mul hpoly (PB_add (PB_add (PB_add (PB_mul (PB_const 8) hpoly)
      (PB_mul (PB_const 2) PB_id)) (PB_mul (PB_const 4) hpoly)) (PB_const 24)))
      (PB_add (PB_add (PB_mul (PB_const 12) hpoly) (PB_mul (PB_const 2) hP))
        (PB_const 26))
  have hp4 : PolyBounded (fun n => 8 * clock n + 2 * (n + clock n) + 21) :=
    PB_add (PB_add (PB_mul (PB_const 8) hpoly) (PB_mul (PB_const 2) hP)) (PB_const 21)
  have hp5 : PolyBounded (fun n => (n + clock n + 1)
      * (10 * clock n + 2 * (n + clock n) + 4 * n + 4 * (n + clock n + 1) + 30)
      + ((8 * clock n + 4 * (n + clock n) + 4 * n + 28)
        + ((2 * clock n + 2 * (n + clock n) + 9)
        + (8 * clock n + 4 * (n + clock n) + 4 * n + 27)))) :=
    PB_add (PB_mul hN (PB_add (PB_add (PB_add (PB_add (PB_mul (PB_const 10) hpoly)
      (PB_mul (PB_const 2) hP)) (PB_mul (PB_const 4) PB_id))
      (PB_mul (PB_const 4) hN)) (PB_const 30)))
      (PB_add (PB_add (PB_add (PB_add (PB_mul (PB_const 8) hpoly)
        (PB_mul (PB_const 4) hP)) (PB_mul (PB_const 4) PB_id)) (PB_const 28))
        (PB_add (PB_add (PB_add (PB_mul (PB_const 2) hpoly) (PB_mul (PB_const 2) hP))
          (PB_const 9))
          (PB_add (PB_add (PB_add (PB_mul (PB_const 8) hpoly)
            (PB_mul (PB_const 4) hP)) (PB_mul (PB_const 4) PB_id)) (PB_const 27))))
  have hlinBP : ∀ (a b c : ℕ), PolyBounded (fun n => a * clock n + b * (n + clock n)
      + c) := fun a b c =>
    PB_add (PB_add (PB_mul (PB_const a) hpoly) (PB_mul (PB_const b) hP)) (PB_const c)
  have hp6 : PolyBounded (fun n => (2 * clock n + 2 * (n + clock n) + 6)
      + ((n + clock n) * (2 * clock n + 2 * (n + clock n) + 2 * (n + clock n) + 10)
      + ((2 * clock n + 4 * (n + clock n) + 14)
        + (2 * clock n + 2 * (n + clock n) + 3)))) :=
    PB_add (hlinBP 2 2 6)
      (PB_add (PB_mul hP (PB_add (PB_add (PB_add (PB_mul (PB_const 2) hpoly)
        (PB_mul (PB_const 2) hP)) (PB_mul (PB_const 2) hP)) (PB_const 10)))
        (PB_add (hlinBP 2 4 14) (hlinBP 2 2 3)))
  have hp7 : PolyBounded (fun n => (2 * clock n + 4 * (n + clock n) + 14)
      + (clock n * (2 * clock n + 4 * (n + clock n) + 2 * clock n + 16)
      + ((4 * clock n + 4 * (n + clock n) + 20) + (2 * clock n + 1)))) :=
    PB_add (hlinBP 2 4 14)
      (PB_add (PB_mul hpoly (PB_add (PB_add (PB_add (PB_mul (PB_const 2) hpoly)
        (PB_mul (PB_const 4) hP)) (PB_mul (PB_const 2) hpoly)) (PB_const 16)))
        (PB_add (hlinBP 4 4 20) (PB_add (PB_mul (PB_const 2) hpoly) (PB_const 1))))
  have hp8 : PolyBounded (fun n => (4 * clock n + 4 * (n + clock n) + 22)
      + ((n + clock n) * (4 * clock n + 4 * (n + clock n) + 2 * (n + clock n) + 24)
      + ((4 * clock n + 6 * (n + clock n) + 24)
        + (2 * clock n + 2 * (n + clock n) + 3)))) :=
    PB_add (hlinBP 4 4 22)
      (PB_add (PB_mul hP (PB_add (PB_add (PB_add (PB_mul (PB_const 4) hpoly)
        (PB_mul (PB_const 4) hP)) (PB_mul (PB_const 2) hP)) (PB_const 24)))
        (PB_add (hlinBP 4 6 24) (hlinBP 2 2 3)))
  have hp9 : PolyBounded (fun n => (4 * clock n + 6 * (n + clock n) + 26)
      + ((n + clock n) * (4 * clock n + 6 * (n + clock n) + 2 * (n + clock n) + 28)
      + ((4 * clock n + 8 * (n + clock n) + 28)
        + (2 * clock n + 2 * (n + clock n) + 3)))) :=
    PB_add (hlinBP 4 6 26)
      (PB_add (PB_mul hP (PB_add (PB_add (PB_add (PB_mul (PB_const 4) hpoly)
        (PB_mul (PB_const 6) hP)) (PB_mul (PB_const 2) hP)) (PB_const 28)))
        (PB_add (hlinBP 4 8 28) (hlinBP 2 2 3)))
  have hMaj : PolyBounded (fun n =>
      morphClockMaj initCellBody.length (clock n) (n + clock n) n) :=
    PB_add (PB_add hp1 (PB_const 1))
      (PB_add (PB_add hp2 (PB_const 1))
        (PB_add (PB_add hp3 (PB_const 1))
          (PB_add (PB_add hp4 (PB_const 1))
            (PB_add (PB_add hp5 (PB_const 1))
              (PB_add (PB_add hp6 (PB_const 1))
                (PB_add (PB_add hp7 (PB_const 1))
                  (PB_add (PB_add hp8 (PB_const 1)) hp9)))))))
  have hmc : PolyBounded (fun n => morphChainClock clock n) :=
    PB_le (fun n => morphChainClock_le clock n) hMaj
  have hT : PolyBounded (fun n => fullClock M clock n) :=
    PB_add (PB_add hmc (PB_const 1)) (PB_ECB (Fintype.card M.State) hpoly hP)
  refine ⟨fullEmitter M, fun n => fullClock M clock n, hT, fun x => ?_⟩
  have hfr := fullEmitter_run M clock x (hclk _)
  have hpa := pipeline_at M clock x
    (ECB (Fintype.card M.State) (clock x.length) (x.length + clock x.length))
    (hclk _) (coreClock_le M clock x)
  constructor
  · show (fullEmitter M).halt
      (run (fullEmitter M) (fullClock M clock x.length)
        (init (fullEmitter M) (encTape0 clock x))).st = true
    rw [hfr]
    exact hpa.1
  · show decodeTape (run (fullEmitter M) (fullClock M clock x.length)
        (init (fullEmitter M) (encTape0 clock x))).tp
      = emittedReduction M x (clock x.length)
    rw [hfr]
    have h2 := hpa.2
    show decodeTape (run (emitterCoreMachine M) _ (init (emitterCoreMachine M)
      (encTape clock x))).tp = _
    rw [show (run (emitterCoreMachine M)
          (ECB (Fintype.card M.State) (clock x.length) (x.length + clock x.length))
          (init (emitterCoreMachine M) (encTape clock x))).tp
        = transOut (emitterCoreMachine M) (encTape clock x)
            (ECB (Fintype.card M.State) (clock x.length) (x.length + clock x.length))
        from rfl, h2]
    exact pipeline_decodes M clock x (hclk _) hAcc

/-! ## The bridge to the tableau target -/

set_option maxHeartbeats 1600000 in
/-- **The supplied-bound fence hits the original target's question.** -/
theorem emitsTableau0_tableau (M : Machine) (clock : ℕ → ℕ)
    (hAcc : acceptStates M ≠ []) (hclk : ∀ n, 0 < clock n)
    (hpoly : PolyBounded clock) :
    ∃ (E : Machine) (T : ℕ → ℕ), PolyBounded T ∧ ∀ x : List Bool,
      HaltsBy E (encTape0 clock x) (T x.length)
      ∧ (Satisfiable (decodeTape (transOut E (encTape0 clock x) (T x.length)))
          ↔ Satisfiable (PallLean.Paper93.DeepMath.PathB.CookLevinReduce.tableauReduction
              M x (clock x.length))) := by
  obtain ⟨E, T, hT, h⟩ := emitsTableau0 M clock hAcc hclk hpoly
  refine ⟨E, T, hT, fun x => ⟨(h x).1, ?_⟩⟩
  rw [show decodeTape (transOut E (encTape0 clock x) (T x.length))
      = emittedReduction M x (clock x.length) from (h x).2]
  exact PallLean.Paper93.DeepMath.PathB.CookLevinEmitPackage2.emittedReduction_equisat
    M x (clock x.length)

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphFence
