import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitMorphT6

/-!
# Cook–Levin M2 emitter — arming morph brick M10: THE CHAIN — THE MORPH CLOSES

The nine proven machines composed: the init-cell family loop (phase 1), the subtract
pass, the `T1` write, the uniformizer, and the five moving-frontier passes.  One
machine, `morphChain`, carries the supplied-bound input encoding `encTape0` — counters
and the raw input transcription only — to `encTape`, the armed six-region entry of the
closed emitter pipeline.  The drops telescope exactly: the passes consume the dead
suffix to the bit, ending flush at the output region (`2B + 6P + 24` cells, the length
audit is `omega` from `P = |x| + B`).
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphChain

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitReadX
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInitLoop
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInitLoopP
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPipeline (cellStream encTape)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorph
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphSub
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT1
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphFill
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT2
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT3
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT4
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT5
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphT6

/-! ## The chain -/

/-- **The arming morph**: nine machines in sequence. -/
def morphChain : Machine :=
  seqMachine (initLoopPMachine initCellBody)
    (seqMachine subMachine
      (seqMachine t1Machine
        (seqMachine fillMachine
          (seqMachine t2Machine
            (seqMachine t3Machine
              (seqMachine t4Machine
                (seqMachine t5Machine t6Machine)))))))

/-- The chain's exact clock. -/
def morphChainClock (clock : ℕ → ℕ) (n : ℕ) : ℕ :=
  ilpClock initCellBody (4 * clock n + 8) (n + clock n + 1) n 0 + 1
    + (subClock (clock n) (n + clock n) n + 1
    + (t1Clock (clock n) (n + clock n) n + 1
    + (fillClock (clock n) (n + clock n) + 1
    + (t2Clock (clock n) (n + clock n) n + 1
    + (t3Clock (clock n) (n + clock n) + 1
    + (t4Clock (clock n) (n + clock n) + 1
    + (t5Clock (clock n) (n + clock n) + 1
    + t6Clock (clock n) (n + clock n))))))))

/-- The chain's final state. -/
def morphFinal : morphChain.State :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
    ((72 : Fin 74), false))))))))

theorem morphChain_halt : morphChain.halt morphFinal = true := rfl

set_option maxHeartbeats 1600000 in
/-- **THE ARMING MORPH RUNS** — the supplied-bound encoding to the armed six-region
entry, one machine, exact clock. -/
theorem morphChain_run (clock : ℕ → ℕ) (x : List Bool) :
    run morphChain (morphChainClock clock x.length)
      (init morphChain (encTape0 clock x))
      = ⟨morphFinal,
          2 * clock x.length + 2 + 2 * (x.length + clock x.length),
          encTape clock x⟩ := by
  -- Phase 1.
  have h1 := phase1_run clock x
  have hh1 := initLoopP_halted initCellBody (4 * clock x.length + 8) 0
    (Nat.zero_le _) (x.length + clock x.length + 1) x []
  rw [show ([] : List Bool).length = 0 from rfl] at hh1
  rw [show (cntT (4 * clock x.length + 8) 0
      ++ (unaryD (x.length + clock x.length + 1) ++ (xVis x 0
      ++ (jT (x.length + clock x.length + 1) 0 ++ encodeD []))) : List Bool)
    = encTape0 clock x from rfl] at hh1
  rw [h1] at hh1
  -- The subtract pass.
  have h2 := subMachine_run_morphIn (clock x.length) (x.length + clock x.length) x
    (cellStream x (x.length + clock x.length)) (by omega)
  -- The T1 write.
  have h3 := t1Machine_run (clock x.length) (x.length + clock x.length) x
    (unaryD (x.length + clock x.length + 1)
      ++ encodeD (cellStream x (x.length + clock x.length))) (by omega)
  -- The uniformizer.
  have h4 := fillMachine_run (clock x.length) (x.length + clock x.length) x
    (unaryD (x.length + clock x.length + 1)
      ++ encodeD (cellStream x (x.length + clock x.length)))
  -- The T2 write.
  have h5 := t2Machine_run (clock x.length) (x.length + clock x.length) x
    (encodeD (cellStream x (x.length + clock x.length)))
  rw [t2Out_t3In] at h5
  -- The tail and its lengths.
  have hTlen : (List.replicate (6 * clock x.length + 16) true ++ ([false, true]
      ++ (xVis x x.length ++ (unaryD (x.length + clock x.length + 1)
      ++ encodeD (cellStream x (x.length + clock x.length)))))).length
      = 6 * clock x.length + 4 * x.length + 2 * (x.length + clock x.length) + 26
        + 2 * (cellStream x (x.length + clock x.length)).length := by
    simp only [List.length_append, List.length_replicate, List.length_cons,
      List.length_nil, xVis_length, unaryD_length, encodeD_length]
    omega
  -- The T3 write.
  have h6 := t3Machine_run (clock x.length) (x.length + clock x.length)
    (List.replicate (6 * clock x.length + 16) true ++ ([false, true]
      ++ (xVis x x.length ++ (unaryD (x.length + clock x.length + 1)
      ++ encodeD (cellStream x (x.length + clock x.length)))))) (by rw [hTlen]; omega)
  -- The T4 fill.
  have h7 := t4Machine_run (clock x.length) (x.length + clock x.length)
    ((List.replicate (6 * clock x.length + 16) true ++ ([false, true]
      ++ (xVis x x.length ++ (unaryD (x.length + clock x.length + 1)
      ++ encodeD (cellStream x (x.length + clock x.length)))))).drop
        (2 * (x.length + clock x.length) + 8))
    (by rw [List.length_drop, hTlen]; omega)
  -- The T5 fill.
  have h8 := t5Machine_run (clock x.length) (x.length + clock x.length)
    (((List.replicate (6 * clock x.length + 16) true ++ ([false, true]
      ++ (xVis x x.length ++ (unaryD (x.length + clock x.length + 1)
      ++ encodeD (cellStream x (x.length + clock x.length)))))).drop
        (2 * (x.length + clock x.length) + 8)).drop (2 * clock x.length + 8))
    (by rw [List.length_drop, List.length_drop, hTlen]; omega)
  -- The T6 fill.
  have h9 := t6Machine_run (clock x.length) (x.length + clock x.length)
    ((((List.replicate (6 * clock x.length + 16) true ++ ([false, true]
      ++ (xVis x x.length ++ (unaryD (x.length + clock x.length + 1)
      ++ encodeD (cellStream x (x.length + clock x.length)))))).drop
        (2 * (x.length + clock x.length) + 8)).drop (2 * clock x.length + 8)).drop
        (2 * (x.length + clock x.length) + 4))
    (by rw [List.length_drop, List.length_drop, List.length_drop, hTlen]; omega)
  -- Telescope the drops uniformly at every junction.
  simp only [List.drop_drop] at h7 h8 h9
  -- Assemble the sequence, inside out.
  have s89 := seq_run t5Machine t6Machine _ _ _ _ _ _ _ _ _ h8 t5Machine_halt66 h9
    t6Machine_halt72
  have s789 := seq_run t4Machine (seqMachine t5Machine t6Machine) _ _ _ _ _ _ _ _ _
    h7 t4Machine_halt55 s89 (seq_halt_final _ _ _ t6Machine_halt72)
  have s6789 := seq_run t3Machine _ _ _ _ _ _ _ _ _ _ h6 t3Machine_halt41 s789
    (seq_halt_final _ _ _ (seq_halt_final _ _ _ t6Machine_halt72))
  have s56789 := seq_run t2Machine _ _ _ _ _ _ _ _ _ _ h5 t2Machine_halt44 s6789
    (seq_halt_final _ _ _ (seq_halt_final _ _ _
      (seq_halt_final _ _ _ t6Machine_halt72)))
  have s456789 := seq_run fillMachine _ _ _ _ _ _ _ _ _ _ h4 fillMachine_halt8 s56789
    (seq_halt_final _ _ _ (seq_halt_final _ _ _ (seq_halt_final _ _ _
      (seq_halt_final _ _ _ t6Machine_halt72))))
  have s3456789 := seq_run t1Machine _ _ _ _ _ _ _ _ _ _ h3 t1Machine_halt11 s456789
    (seq_halt_final _ _ _ (seq_halt_final _ _ _ (seq_halt_final _ _ _
      (seq_halt_final _ _ _ (seq_halt_final _ _ _ t6Machine_halt72)))))
  have s23456789 := seq_run subMachine _ _ _ _ _ _ _ _ _ _ h2 subMachine_halt10
    s3456789
    (seq_halt_final _ _ _ (seq_halt_final _ _ _ (seq_halt_final _ _ _
      (seq_halt_final _ _ _ (seq_halt_final _ _ _
        (seq_halt_final _ _ _ t6Machine_halt72))))))
  have sAll := seq_run (initLoopPMachine initCellBody) _ _ _ _ _ _ _ _ _ _ h1 hh1
    s23456789
    (seq_halt_final _ _ _ (seq_halt_final _ _ _ (seq_halt_final _ _ _
      (seq_halt_final _ _ _ (seq_halt_final _ _ _ (seq_halt_final _ _ _
        (seq_halt_final _ _ _ t6Machine_halt72)))))))
  rw [show morphChainClock clock x.length
      = ilpClock initCellBody (4 * clock x.length + 8) (x.length + clock x.length + 1)
          x.length 0 + 1
        + (subClock (clock x.length) (x.length + clock x.length) x.length + 1
        + (t1Clock (clock x.length) (x.length + clock x.length) x.length + 1
        + (fillClock (clock x.length) (x.length + clock x.length) + 1
        + (t2Clock (clock x.length) (x.length + clock x.length) x.length + 1
        + (t3Clock (clock x.length) (x.length + clock x.length) + 1
        + (t4Clock (clock x.length) (x.length + clock x.length) + 1
        + (t5Clock (clock x.length) (x.length + clock x.length) + 1
        + t6Clock (clock x.length) (x.length + clock x.length)))))))) from rfl]
  have hsplit : (List.replicate (6 * clock x.length + 16) true ++ ([false, true]
      ++ (xVis x x.length ++ (unaryD (x.length + clock x.length + 1)
      ++ encodeD (cellStream x (x.length + clock x.length))))))
      = (List.replicate (6 * clock x.length + 16) true ++ ([false, true]
        ++ (xVis x x.length ++ unaryD (x.length + clock x.length + 1))))
        ++ encodeD (cellStream x (x.length + clock x.length)) := by
    simp [List.append_assoc]
  have hPRE : (List.replicate (6 * clock x.length + 16) true ++ ([false, true]
      ++ (xVis x x.length ++ unaryD (x.length + clock x.length + 1)))).length
      = 2 * (x.length + clock x.length) + 8 + (2 * clock x.length + 8)
        + (2 * (x.length + clock x.length) + 4)
        + (2 * (x.length + clock x.length) + 4) := by
    simp only [List.length_append, List.length_replicate, List.length_cons,
      List.length_nil, xVis_length, unaryD_length]
    omega
  rw [hsplit, ← hPRE, List.drop_left, t6Out_morphOut, morphOut_encTape] at sAll
  exact sAll

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorphChain
