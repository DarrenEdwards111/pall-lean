import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitFinale

/-!
# Cook–Levin M2 emitter — the arming morph, brick M1: SPEC + PHASE 1

Input-convention decision taken: the supplied-bound armed-init layout (SCOPE_EMITTER's
sanctioned E2 fallback) replaces the preloaded-cells `encTape`.  The new input encoding
`encTape0` carries only counters and the raw 4:1 input transcription (`xVis`) — no
computed content:

  `cntT (4B+8) 0 ++ unaryD (P+1) ++ xVis x 0 ++ jT (P+1) 0 ++ encodeD []`,
  `B := clock |x|`, `P := |x| + B`.

The pipeline is `initCellP ⨟ morph ⨟ emitterCore`:

1. **phase 1** (`phase1_run`, PROVEN here): brick 27's `initCellP_family_run` at
   `G := 4B+8`, `N := P+1` — emits the init-cell stream (`cellStream x P`) into the
   output region, leaving the working prefix `morphIn`;
2. **the morph** (bricks M2+): the equal-length prefix rewrite `morphInPre → morphOutPre`
   (`morph_length_eq`, the load-bearing arithmetic: `G := 4B+8` makes the prefixes equal
   given `P = |x| + B`);
3. **phase 3**: `emitterCoreMachine` on `morphOut … (cellStream x P) = encTape clock x`
   (`morphOut_encTape`, definitional) — the closed pipeline (`EmitsEmittedT`) verbatim.

**The morph's quantity sources (design, for bricks M2+).**  The rewrite needs `B` and
`P`; neither requires division: `B+1` is region 2's unmarked remainder after 1:1
`markedD`-marking against region 3's `n = |x|` units (`P+1−n = B+1`), and `P+1` is
region 4, pristine.  All counts are `markedD`-walk transcriptions — the `cntT`/`jsT`
discipline of the splice engines.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorph

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitReadX
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInitLoop
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInitLoopP
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPipeline (cellStream encTape)

/-! ## The supplied-bound input encoding -/

/-- **The armed-init input encoding** — counters and the raw input transcription only:
the grand counter at capacity `4B+8` (the length equalizer), the cell bound `P+1`, the
cursored input `xVis x 0`, the live cell counter at `0`, and the empty output. -/
noncomputable def encTape0 (clock : ℕ → ℕ) (x : List Bool) : List Bool :=
  cntT (4 * clock x.length + 8) 0
    ++ (unaryD (x.length + clock x.length + 1)
    ++ (xVis x 0
    ++ (jT (x.length + clock x.length + 1) 0
    ++ encodeD [])))

/-! ## The morph's endpoints -/

/-- The morph's input prefix: phase 1's exit working regions (grand untouched, cell
bound, healed input, live counter saturated). -/
noncomputable def morphInPre (B P : ℕ) (x : List Bool) : List Bool :=
  cntT (4 * B + 8) 0 ++ (unaryD (P + 1) ++ (xVis x 0 ++ unaryD (P + 1)))

/-- The morph's output prefix: the six-region armed entry of the emitter core. -/
noncomputable def morphOutPre (B P : ℕ) : List Bool :=
  unaryD B ++ (unaryD P ++ (jT (P + 2) (P + 1)
    ++ (jT (B + 2) 0 ++ (jT (P + 2) 1 ++ jT (P + 2) 0))))

/-- The morph's full input tape. -/
noncomputable def morphIn (B P : ℕ) (x s : List Bool) : List Bool :=
  cntT (4 * B + 8) 0 ++ (unaryD (P + 1) ++ (xVis x 0 ++ (unaryD (P + 1) ++ encodeD s)))

/-- The morph's full output tape. -/
noncomputable def morphOut (B P : ℕ) (s : List Bool) : List Bool :=
  unaryD B ++ (unaryD P ++ (jT (P + 2) (P + 1)
    ++ (jT (B + 2) 0 ++ (jT (P + 2) 1 ++ (jT (P + 2) 0 ++ encodeD s)))))

theorem morphIn_pre (B P : ℕ) (x s : List Bool) :
    morphIn B P x s = morphInPre B P x ++ encodeD s := by
  rw [morphIn, morphInPre]
  simp [List.append_assoc]

theorem morphOut_pre (B P s) :
    morphOut B P s = morphOutPre B P ++ encodeD s := by
  rw [morphOut, morphOutPre]
  simp [List.append_assoc]

/-! ## The load-bearing length equation -/

theorem morphInPre_length (B P : ℕ) (x : List Bool) :
    (morphInPre B P x).length = 8 * B + 4 * P + 4 * x.length + 28 := by
  rw [morphInPre]
  simp only [List.length_append, cntT_length _ _ (Nat.zero_le _), unaryD_length,
    xVis_length]
  omega

theorem morphOutPre_length (B P : ℕ) :
    (morphOutPre B P).length = 4 * B + 8 * P + 28 := by
  rw [morphOutPre]
  have h1 := jT_length (P + 2) (P + 1) (by omega)
  have h2 := jT_length (B + 2) 0 (by omega)
  have h3 := jT_length (P + 2) 1 (by omega)
  have h4 := jT_length (P + 2) 0 (by omega)
  simp only [List.length_append, unaryD_length, h1, h2, h3, h4]
  omega

/-- **The equal-length equation**: with `G := 4B+8` and `P = |x| + B`, the morph is an
in-place prefix rewrite. -/
theorem morph_length_eq (B P : ℕ) (x : List Bool) (hP : P = x.length + B) :
    (morphInPre B P x).length = (morphOutPre B P).length := by
  rw [morphInPre_length, morphOutPre_length]
  omega

/-! ## Phase 3's entry is the closed pipeline's -/

/-- The morph's exit at the reduction parameters IS `encTape` — phase 3 is the closed
pipeline verbatim. -/
theorem morphOut_encTape (clock : ℕ → ℕ) (x : List Bool) :
    morphOut (clock x.length) (x.length + clock x.length)
        (cellStream x (x.length + clock x.length))
      = encTape clock x := rfl

/-! ## Phase 1, proven -/

/-- **PHASE 1 RUNS**: brick 27's init-cell family loop, instantiated at the supplied-bound
input encoding, emits the full init-cell stream and leaves exactly the morph's input
tape. -/
theorem phase1_run (clock : ℕ → ℕ) (x : List Bool) :
    run (initLoopPMachine initCellBody)
      (ilpClock initCellBody (4 * clock x.length + 8)
        (x.length + clock x.length + 1) x.length 0)
      (init (initLoopPMachine initCellBody) (encTape0 clock x))
      = ⟨(96, ⟨0, Nat.succ_pos _⟩, false),
          2 * (4 * clock x.length + 8) + 2 + 2 * (x.length + clock x.length + 1) + 2
            + 4 * x.length + 1,
          morphIn (clock x.length) (x.length + clock x.length) x
            (cellStream x (x.length + clock x.length))⟩ := by
  have h := initCellP_family_run (4 * clock x.length + 8) 0 (Nat.zero_le _)
    (x.length + clock x.length + 1) x []
  rw [show ([] : List Bool).length = 0 from rfl] at h
  rw [encTape0]
  rw [h]
  congr 1

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitMorph
