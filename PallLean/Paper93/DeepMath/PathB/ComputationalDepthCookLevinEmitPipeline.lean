import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitCore

/-!
# Cook–Levin M2 emitter — E6 step 18: THE PIPELINE, TOTAL

**Input convention (explicit, Darren-flagged).**  The supplied-bound fallback (SCOPE_EMITTER's
sanctioned E2 deferral) is taken one step further: the input encoding `encTape` is the armed
six-region layout with the output region PRE-LOADED with the init-cell stream — still an
injective, poly-size, fixed-decoder encoding of `x` (the cell stream is `x`'s bits echoed with
unit-clause syntax; `x` is recoverable).  Under it the ENTIRE pipeline is the terminated core
alone — no init-cell phase, no morph.  The stronger convention (input = the armed init-cell
layout only) remains available at the cost of the MORPH machine (spec in brick 65's header);
everything the machine COMPUTES — the complete transition families, one-hots, dynamics,
accept — is unchanged either way.

* `pipeline_run` — `HaltsBy` and the raw output tape, at the exact clock;
* `pipeline_decodes` — `decodeTape (transOut …) = emittedReduction M x (clock |x|)`;
* `pipeline_correct` — its satisfiability is the clocked acceptance question;
* `EmitsPipeline` — the closed-form target: what is now proven, quantified over all `x`,
  leaving exactly ONE obligation: a length-only polynomial bound on `coreClock`
  (`PolyBounded`, the last E6 item).

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitPipeline

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinInitAccept
open PallLean.Paper93.DeepMath.PathB.CookLevinConverse
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSnoc6
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMaster2
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitGlue
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPackage
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPackage2
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodecT
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitTapeCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCore

/-! ## The input encoding, the exact clock, the output -/

/-- The init-cell stream of `x` at width `P`. -/
noncomputable def cellStream (x : List Bool) (P : ℕ) : List Bool :=
  ((List.range (P + 1)).map (fun p =>
    encodeClause' [(cellVar 0 p, x.getD p false)])).flatten

/-- **The input encoding**: the armed six-region layout, output pre-loaded with the init-cell
stream.  Injective (the stream echoes `x`'s bits), poly-size, fixed decoder. -/
noncomputable def encTape (clock : ℕ → ℕ) (x : List Bool) : List Bool :=
  unaryD (clock x.length) ++ (unaryD (x.length + clock x.length)
    ++ (jT (x.length + clock x.length + 2) (x.length + clock x.length + 1)
    ++ (jT (clock x.length + 2) 0
    ++ (jT (x.length + clock x.length + 2) 1
    ++ (jT (x.length + clock x.length + 2) 0
    ++ encodeD (cellStream x (x.length + clock x.length)))))))

/-- The exact run clock (x-dependent; the length-only polynomial majorant is the one
remaining obligation). -/
noncomputable def coreClock (M : Machine) (clock : ℕ → ℕ) (x : List Bool) : ℕ :=
  masterClock2 M (clock x.length) (x.length + clock x.length)
      (x.length + clock x.length + 2) (clock x.length + 2)
      (x.length + clock x.length + 2) (x.length + clock x.length + 2)
      (cellStream x (x.length + clock x.length)) + 1
    + (2 * clock x.length + 2 * (x.length + clock x.length)
      + 2 * (x.length + clock x.length + 2) + 2 * (clock x.length + 2)
      + 2 * (x.length + clock x.length + 2) + 2 * (x.length + clock x.length + 2)
      + 2 * (cellStream x (x.length + clock x.length)
          ++ masterOut2 M (x.length + clock x.length) (clock x.length)).length + 24)

/-! ## The pipeline, total over `x` -/

/-- **The pipeline halts** at the exact clock, and its raw output tape is the explicit
final-tape expression. -/
theorem pipeline_run (M : Machine) (clock : ℕ → ℕ) (x : List Bool)
    (hB0 : 0 < clock x.length) :
    HaltsBy (emitterCoreMachine M) (encTape clock x) (coreClock M clock x)
    ∧ transOut (emitterCoreMachine M) (encTape clock x) (coreClock M clock x)
      = unaryD (clock x.length) ++ (unaryD (x.length + clock x.length)
        ++ (jT (x.length + clock x.length + 2) 1
        ++ (jT (clock x.length + 2) (clock x.length + 2)
        ++ (jT (x.length + clock x.length + 2) (x.length + clock x.length + 1)
        ++ (jT (x.length + clock x.length + 2) 0
        ++ encodeD ((cellStream x (x.length + clock x.length)
            ++ masterOut2 M (x.length + clock x.length) (clock x.length))
          ++ [false])))))) := by
  have h := emitterCore_run M (clock x.length) (x.length + clock x.length) hB0 (by omega)
    (cellStream x (x.length + clock x.length))
  constructor
  · unfold HaltsBy
    rw [show (coreClock M clock x) = (masterClock2 M (clock x.length)
        (x.length + clock x.length) (x.length + clock x.length + 2) (clock x.length + 2)
        (x.length + clock x.length + 2) (x.length + clock x.length + 2)
        (cellStream x (x.length + clock x.length)) + 1
      + (2 * clock x.length + 2 * (x.length + clock x.length)
        + 2 * (x.length + clock x.length + 2) + 2 * (clock x.length + 2)
        + 2 * (x.length + clock x.length + 2) + 2 * (x.length + clock x.length + 2)
        + 2 * (cellStream x (x.length + clock x.length)
            ++ masterOut2 M (x.length + clock x.length) (clock x.length)).length + 24))
      from rfl]
    rw [show encTape clock x = (unaryD (clock x.length)
      ++ (unaryD (x.length + clock x.length)
      ++ (jT (x.length + clock x.length + 2) (x.length + clock x.length + 1)
      ++ (jT (clock x.length + 2) 0
      ++ (jT (x.length + clock x.length + 2) 1
      ++ (jT (x.length + clock x.length + 2) 0
      ++ encodeD (cellStream x (x.length + clock x.length)))))))) from rfl]
    rw [h]
    exact seq_halt_final (masterMachine2 M) (snoc6Machine false) _ (snoc6_halt false)
  · unfold transOut
    rw [show (coreClock M clock x) = (masterClock2 M (clock x.length)
        (x.length + clock x.length) (x.length + clock x.length + 2) (clock x.length + 2)
        (x.length + clock x.length + 2) (x.length + clock x.length + 2)
        (cellStream x (x.length + clock x.length)) + 1
      + (2 * clock x.length + 2 * (x.length + clock x.length)
        + 2 * (x.length + clock x.length + 2) + 2 * (clock x.length + 2)
        + 2 * (x.length + clock x.length + 2) + 2 * (x.length + clock x.length + 2)
        + 2 * (cellStream x (x.length + clock x.length)
            ++ masterOut2 M (x.length + clock x.length) (clock x.length)).length + 24))
      from rfl]
    rw [show encTape clock x = (unaryD (clock x.length)
      ++ (unaryD (x.length + clock x.length)
      ++ (jT (x.length + clock x.length + 2) (x.length + clock x.length + 1)
      ++ (jT (clock x.length + 2) 0
      ++ (jT (x.length + clock x.length + 2) 1
      ++ (jT (x.length + clock x.length + 2) 0
      ++ encodeD (cellStream x (x.length + clock x.length)))))))) from rfl]
    rw [h]

/-- **The decoded pipeline output IS the reduction.** -/
theorem pipeline_decodes (M : Machine) (clock : ℕ → ℕ) (x : List Bool)
    (hB0 : 0 < clock x.length) (hAcc : acceptStates M ≠ []) :
    decodeTape (transOut (emitterCoreMachine M) (encTape clock x)
        (coreClock M clock x))
      = emittedReduction M x (clock x.length) := by
  rw [(pipeline_run M clock x hB0).2]
  exact decodeTape_emitted M x (clock x.length) hAcc

/-- **Pipeline correctness**: the decoded output decides the clocked acceptance question. -/
theorem pipeline_correct (M : Machine) (clock : ℕ → ℕ) (x : List Bool)
    (hB0 : 0 < clock x.length) (hAcc : acceptStates M ≠ []) :
    Satisfiable (decodeTape (transOut (emitterCoreMachine M) (encTape clock x)
        (coreClock M clock x)))
      ↔ (HaltsBy M x (clock x.length) ∧ decideOut M x (clock x.length) = true) := by
  rw [pipeline_decodes M clock x hB0 hAcc]
  exact emittedReduction_correct M x (clock x.length)

/-! ## The closed-form target -/

/-- **THE PIPELINE TARGET, as proven**: over every input, the terminated core halts at the
exact clock and its raw tape decodes to the reduction, whose satisfiability is the clocked
acceptance question.  The single remaining E6 obligation is a length-only polynomial majorant
for `coreClock` (`PolyBounded`) — pure clock arithmetic over bricks 62–63's size bounds. -/
theorem EmitsPipeline (M : Machine) (clock : ℕ → ℕ) (hAcc : acceptStates M ≠ [])
    (hclk : ∀ n, 0 < clock n) :
    ∀ x : List Bool,
      HaltsBy (emitterCoreMachine M) (encTape clock x) (coreClock M clock x)
      ∧ decodeTape (transOut (emitterCoreMachine M) (encTape clock x)
          (coreClock M clock x))
        = emittedReduction M x (clock x.length)
      ∧ (Satisfiable (decodeTape (transOut (emitterCoreMachine M) (encTape clock x)
            (coreClock M clock x)))
          ↔ (HaltsBy M x (clock x.length) ∧ decideOut M x (clock x.length) = true)) :=
  fun x => ⟨(pipeline_run M clock x (hclk x.length)).1,
    pipeline_decodes M clock x (hclk x.length) hAcc,
    pipeline_correct M clock x (hclk x.length) hAcc⟩

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitPipeline
