import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitTapeCodec

/-!
# Cook–Levin M2 emitter — E6 step 17: THE TERMINATED CORE

The eighteen-piece machine `master2 ⨟ snoc6 false`, instantiated at the tape codec's concrete
sizes (`CB = C2 = NV := P + 2`, `C1 := B + 2`): one run theorem, and — the headline — its RAW
EXIT TAPE (`Cfg.tp`, the `transOut` form) decodes to `emittedReduction M x clock` exactly.

Input-phase resolution (recorded): under the supplied-bound convention (SCOPE_EMITTER's own
E2 fallback — the input encoding is the armed init-cell layout, injective, poly-size, fixed
decoder), phase 1 is brick 27's proven `initCellP_family_run` verbatim, and exactly ONE new
machine remains between it and this core: the MORPH, rewriting the equal-length prefix
`cntT (4B + 8) (P + 1) ++ unaryD (P + 1) ++ xVis x 0 ++ unaryD (P + 1)` into
`unaryD B ++ unaryD P ++ jT (P + 2) (P + 1) ++ jT (B + 2) 0 ++ jT (P + 2) 1 ++ jT (P + 2) 0`
(the free grand size `G := 4B + 8` solves the length equation).
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitCore

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinInitAccept
open PallLean.Paper93.DeepMath.PathB.CookLevinConverse
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSnoc6
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMaster2
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitGlue
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPackage
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPackage2
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodecT
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitTapeCodec

/-- The terminated core: the seventeen-piece master chain plus the terminator snoc. -/
noncomputable def emitterCoreMachine (M : Machine) : Machine :=
  seqMachine (masterMachine2 M) (snoc6Machine false)

set_option maxHeartbeats 1600000 in
/-- **The terminated core runs** at the tape codec's concrete sizes. -/
theorem emitterCore_run (M : Machine) (B P : ℕ) (hB0 : 0 < B) (hP : 0 < P)
    (out : List Bool) :
    run (emitterCoreMachine M)
      (masterClock2 M B P (P + 2) (B + 2) (P + 2) (P + 2) out + 1
        + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (P + 2)
          + 2 * (out ++ masterOut2 M P B).length + 24))
      (init (emitterCoreMachine M) (unaryD B ++ (unaryD P ++ (jT (P + 2) (P + 1)
        ++ (jT (B + 2) 0 ++ (jT (P + 2) 1 ++ (jT (P + 2) 0 ++ encodeD out)))))))
      = ⟨Sum.inr ((28 : Fin 29), false),
          2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (P + 2)
            + 2 * (out ++ masterOut2 M P B).length + 15,
          unaryD B ++ (unaryD P ++ (jT (P + 2) 1 ++ (jT (B + 2) (B + 2)
            ++ (jT (P + 2) (P + 1) ++ (jT (P + 2) 0
            ++ encodeD ((out ++ masterOut2 M P B) ++ [false]))))))⟩ := by
  have h1 := master2_run M B P (P + 2) (B + 2) (P + 2) (P + 2) hB0 hP
    (by omega) (by omega) (by omega) (by omega) out
  have h2 := snoc6_run false B 0 (by omega) P 0 (by omega) (P + 2) (B + 2) (P + 2)
    (P + 2) 1 (B + 2) (P + 1) 0 (by omega) (by omega) (by omega) (by omega)
    (out ++ masterOut2 M P B)
  rw [cntT_zero B, cntT_zero P] at h2
  exact seq_run (masterMachine2 M) (snoc6Machine false) _ _ _ _ _ _ _ _ _
    h1 (masterFinal2_halt M) h2 (snoc6_halt false)

/-- **THE RAW EXIT TAPE DECODES TO THE REDUCTION** — the `transOut`-form headline: run the
terminated core from the armed six-region entry (payload region holding the init-cell stream),
project the final tape, decode: `emittedReduction M x clock`, exactly. -/
theorem emitterCore_decodes (M : Machine) (x : List Bool) (clock : ℕ)
    (hB0 : 0 < clock) (hAcc : acceptStates M ≠ []) :
    decodeTape
      (run (emitterCoreMachine M)
        (masterClock2 M clock (x.length + clock) (x.length + clock + 2) (clock + 2)
            (x.length + clock + 2) (x.length + clock + 2)
            (((List.range (x.length + clock + 1)).map (fun p =>
              encodeClause' [(cellVar 0 p, x.getD p false)])).flatten) + 1
          + (2 * clock + 2 * (x.length + clock) + 2 * (x.length + clock + 2)
            + 2 * (clock + 2) + 2 * (x.length + clock + 2) + 2 * (x.length + clock + 2)
            + 2 * ((((List.range (x.length + clock + 1)).map (fun p =>
                encodeClause' [(cellVar 0 p, x.getD p false)])).flatten
              ++ masterOut2 M (x.length + clock) clock)).length + 24))
        (init (emitterCoreMachine M) (unaryD clock ++ (unaryD (x.length + clock)
          ++ (jT (x.length + clock + 2) (x.length + clock + 1) ++ (jT (clock + 2) 0
          ++ (jT (x.length + clock + 2) 1 ++ (jT (x.length + clock + 2) 0
          ++ encodeD (((List.range (x.length + clock + 1)).map (fun p =>
              encodeClause' [(cellVar 0 p, x.getD p false)])).flatten))))))))).tp
      = emittedReduction M x clock := by
  rw [emitterCore_run M clock (x.length + clock) hB0 (by omega)]
  exact decodeTape_emitted M x clock hAcc

/-- The decoded core output decides the clocked acceptance question. -/
theorem emitterCore_correct (M : Machine) (x : List Bool) (clock : ℕ)
    (hB0 : 0 < clock) (hAcc : acceptStates M ≠ []) :
    Satisfiable (decodeTape
      (run (emitterCoreMachine M)
        (masterClock2 M clock (x.length + clock) (x.length + clock + 2) (clock + 2)
            (x.length + clock + 2) (x.length + clock + 2)
            (((List.range (x.length + clock + 1)).map (fun p =>
              encodeClause' [(cellVar 0 p, x.getD p false)])).flatten) + 1
          + (2 * clock + 2 * (x.length + clock) + 2 * (x.length + clock + 2)
            + 2 * (clock + 2) + 2 * (x.length + clock + 2) + 2 * (x.length + clock + 2)
            + 2 * ((((List.range (x.length + clock + 1)).map (fun p =>
                encodeClause' [(cellVar 0 p, x.getD p false)])).flatten
              ++ masterOut2 M (x.length + clock) clock)).length + 24))
        (init (emitterCoreMachine M) (unaryD clock ++ (unaryD (x.length + clock)
          ++ (jT (x.length + clock + 2) (x.length + clock + 1) ++ (jT (clock + 2) 0
          ++ (jT (x.length + clock + 2) 1 ++ (jT (x.length + clock + 2) 0
          ++ encodeD (((List.range (x.length + clock + 1)).map (fun p =>
              encodeClause' [(cellVar 0 p, x.getD p false)])).flatten))))))))).tp)
      ↔ (HaltsBy M x clock ∧ decideOut M x clock = true) := by
  rw [emitterCore_decodes M x clock hB0 hAcc]
  exact emittedReduction_correct M x clock

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitCore
