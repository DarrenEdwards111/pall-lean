import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitHeadTop

/-!
# Cook–Levin M2 emitter — E6 step 7: THE FULL MASTER CHAIN

Seventeen pieces:

```
rep(cell) ⨟ rst4 ⨟ rep(write) ⨟ rst4 ⨟ rep(dynA) ⨟ rst4 ⨟ one3
  ⨟ rep(head) ⨟ rst4 ⨟ rep(stateChain) ⨟ rst4 ⨟ rep(dynB)
  ⨟ stateTop ⨟ headTop ⨟ one3 ⨟ acceptV ⨟ initConstV
```

— the `P+1`-bound loops, the bound reset, the `1`-bound loops (now including the state
one-hot constant chain), the two no-bump `t = B` top blocks, the second bound reset (the head
top block re-grows the mirrors), and the one-shots at source `P + 1`.  `master2_run` composes
the seventeen proven runs; `masterOut2` is the total stream: ALL FOUR complete families
(tape, write, dynamics-A, state — the one-hots now with their `t = B` blocks), the head
one-hot family with its top block, dynB, accept, and the constant init clauses.
Still outside (glue-level, own arming): the init-cell `xVis` loop and the majorant.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitMaster2

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinOneHotWindow
open PallLean.Paper93.DeepMath.PathB.CookLevinDynamics
open PallLean.Paper93.DeepMath.PathB.CookLevinInitAccept
open PallLean.Paper93.DeepMath.PathB.CookLevinAssembly
open PallLean.Paper93.DeepMath.PathB.CookLevinEmit (encodeNat)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCounterIncr
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSplice
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRange
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitTemplates
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitNestVar
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitFamilyBodies
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSeq
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRep
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRepP
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPairT
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInterRow
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInterGrand
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitTriangleHead
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSnoc6
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitHeadFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCellFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitWriteFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitDynFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAcceptInit
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitQcPass
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRst4
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitOne3
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitStateChain
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitHeadTop

/-! ## The machine, the stream, the final state -/

/-- The full master chain: seventeen proven parts, right-nested. -/
noncomputable def masterMachine2 (M : Machine) : Machine :=
  seqMachine (repMachine cellRoundMachine)
    (seqMachine rst4Machine
      (seqMachine (repMachine (qcMachine (writeBodies M) 0 (Fintype.card M.State)))
        (seqMachine rst4Machine
          (seqMachine (repMachine (qcMachine (dynBodies M) 0 (Fintype.card M.State)))
            (seqMachine rst4Machine
              (seqMachine one3Machine
                (seqMachine (repMachine headRoundMachine)
                  (seqMachine rst4Machine
                    (seqMachine (repMachine (qcMachine (stBodies M) 0
                        (Fintype.card M.State + 1)))
                      (seqMachine rst4Machine
                        (seqMachine (repMachine (qcMachine (leftBodies M) 0
                            (Fintype.card M.State)))
                          (seqMachine (qcnMachine (stBodies M) 0
                              (Fintype.card M.State + 1))
                            (seqMachine headTopMachine
                              (seqMachine one3Machine
                                (seqMachine (qcMachine (fun _ => acceptBody M) 0 1)
                                  (qcMachine (fun _ => initConstBody M) 0 1))))))))))))))))

/-- The total stream: the four complete families, the head family + top, dynB, accept, the
constant init clauses. -/
noncomputable def masterOut2 (M : Machine) (P B : ℕ) : List Bool :=
  cellEmitOut P B
    ++ (qcEmitOut (writeBodies M) P (Fintype.card M.State) B
    ++ (qcEmitOut (dynBodies M) P (Fintype.card M.State) B
    ++ (headEmitOut P B
    ++ (qcEmitOut (stBodies M) 0 (Fintype.card M.State + 1) B
    ++ (qcEmitOut (leftBodies M) 0 (Fintype.card M.State) B
    ++ (((stateOneHot M B).map encodeClause').flatten
    ++ ((triRowOut amoPairRowHeadBody B P ++ (List.replicate (P + 1) true
        ++ ([false] ++ loop3Out aloRowHeadBody B (P + 1) (P + 1))))
    ++ (((acceptFormula M B).map encodeClause').flatten
    ++ (encodeClause' [(stateVar 0 (Fintype.equivFin M.State M.start).val, true)]
      ++ encodeClause' [(headVar 0 0, true)])))))))))

/-- The chain's final state. -/
noncomputable def masterFinal2 (M : Machine) : (masterMachine2 M).State :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
    (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
      (qcFinal (fun _ => initConstBody M) 0 1))))))))))))))))

/-- The full master clock: the seventeen stated clocks, `seq`-composed. -/
noncomputable def masterClock2 (M : Machine) (B P CB C1 C2 NV : ℕ) (out : List Bool) : ℕ :=
  let O1 := out ++ cellEmitOut P B
  let O2 := O1 ++ qcEmitOut (writeBodies M) P (Fintype.card M.State) B
  let O3 := O2 ++ qcEmitOut (dynBodies M) P (Fintype.card M.State) B
  let O4 := O3 ++ headEmitOut P B
  let O5 := O4 ++ qcEmitOut (stBodies M) 0 (Fintype.card M.State + 1) B
  let O6 := O5 ++ qcEmitOut (leftBodies M) 0 (Fintype.card M.State) B
  let O7 := O6 ++ ((stateOneHot M B).map encodeClause').flatten
  let O8 := O7 ++ (triRowOut amoPairRowHeadBody B P ++ (List.replicate (P + 1) true
      ++ ([false] ++ loop3Out aloRowHeadBody B (P + 1) (P + 1))))
  let O9 := O8 ++ ((acceptFormula M B).map encodeClause').flatten
  let rc := 2 * B + 2 * P + 2 * CB + 2 * B + 10
  let cCell := repRounds (fun t =>
      ((pairTClock cellCopyRowBody B P CB C1 C2 NV t 1 (P + 1)
          (out ++ cellEmitOut P t).length + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 18)) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * t + 12))) B + (4 * B + 4)
  let cWrite := repRounds (fun t =>
      qcClock (writeBodies M) B P CB C1 C2 NV t 0 (Fintype.card M.State)
        (O1 ++ qcEmitOut (writeBodies M) P (Fintype.card M.State) t).length) B
    + (4 * B + 4)
  let cDynA := repRounds (fun t =>
      qcClock (dynBodies M) B P CB C1 C2 NV t 0 (Fintype.card M.State)
        (O2 ++ qcEmitOut (dynBodies M) P (Fintype.card M.State) t).length) B
    + (4 * B + 4)
  let cOne := 2 * B + 2 * P + 2 * (P + 1) + 6
  let cHead := repRounds (fun t =>
      (((((((repPRounds B (fun r =>
            pairTClock amoPairRowHeadBody B P CB C1 C2 NV t (r + 1) (r + 1)
                ((O3 ++ headEmitOut P t) ++ triRowOut amoPairRowHeadBody t r).length + 1
              + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (r + 1) + 18)) P
          + (4 * B + 4 * P + 8)) + 1
        + pairTClock cntTrueBody B P CB C1 C2 NV t (P + 1) (P + 1)
            ((O3 ++ headEmitOut P t) ++ triRowOut amoPairRowHeadBody t P).length) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 18)) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV
          + 2 * (((O3 ++ headEmitOut P t) ++ triRowOut amoPairRowHeadBody t P)
              ++ List.replicate (P + 1) true).length + 24)) + 1
        + pairTClock aloRowHeadBody B P CB C1 C2 NV t (P + 1) (P + 1)
            ((((O3 ++ headEmitOut P t) ++ triRowOut amoPairRowHeadBody t P)
              ++ List.replicate (P + 1) true) ++ [false]).length) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 18)) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 16))) B + (4 * B + 4)
  let cState := repRounds (fun t =>
      qcClockD (stBodies M) B P 0 CB C1 C2 NV t 0 (Fintype.card M.State + 1)
        (O4 ++ qcEmitOut (stBodies M) 0 (Fintype.card M.State + 1) t).length) B
    + (4 * B + 4)
  let cDynB := repRounds (fun t =>
      qcClockD (leftBodies M) B P 0 CB C1 C2 NV t 0 (Fintype.card M.State)
        (O5 ++ qcEmitOut (leftBodies M) 0 (Fintype.card M.State) t).length) B
    + (4 * B + 4)
  let cStTop := qcnClockD (stBodies M) B P 0 CB C1 C2 NV B 0
    (Fintype.card M.State + 1) O6.length
  let cHdTop :=
      (((((repPRounds B (fun r =>
            pairTClock amoPairRowHeadBody B P CB C1 C2 NV B (r + 1) (r + 1)
                (O7 ++ triRowOut amoPairRowHeadBody B r).length + 1
              + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (r + 1) + 18)) P
          + (4 * B + 4 * P + 8)) + 1
        + pairTClock cntTrueBody B P CB C1 C2 NV B (P + 1) (P + 1)
            (O7 ++ triRowOut amoPairRowHeadBody B P).length) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 18)) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV
          + 2 * ((O7 ++ triRowOut amoPairRowHeadBody B P)
              ++ List.replicate (P + 1) true).length + 24)) + 1
        + pairTClock aloRowHeadBody B P CB C1 C2 NV B (P + 1) (P + 1)
            (((O7 ++ triRowOut amoPairRowHeadBody B P)
              ++ List.replicate (P + 1) true) ++ [false]).length) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 18)
  let cAcc := (pairTClock (acceptBody M) B P CB C1 C2 NV B (P + 1) 1 O8.length + 1
    + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * 1 + 18)) + 1
    + (2 * B + 2 * P + 2 * CB + 2 * B + 12)
  let cIC := (pairTClock (initConstBody M) B P CB C1 C2 NV (B + 1) (P + 1) 1
      O9.length + 1
    + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * 1 + 18)) + 1
    + (2 * B + 2 * P + 2 * CB + 2 * (B + 1) + 12)
  cCell + 1 + (rc + 1 + (cWrite + 1 + (rc + 1 + (cDynA + 1 + (rc + 1 + (cOne + 1
    + (cHead + 1 + (rc + 1 + (cState + 1 + (rc + 1 + (cDynB + 1 + (cStTop + 1
    + (cHdTop + 1 + (cOne + 1 + (cAcc + 1 + cIC)))))))))))))))

/-! ## THE FULL MASTER RUN -/

set_option maxHeartbeats 8000000 in
/-- **THE FULL MASTER CHAIN RUNS**: one machine emits `masterOut2` — every family the
six-region layout can carry, including both `t = B` one-hot top blocks — with all mirrors in
known final positions. -/
theorem master2_run (M : Machine) (B P CB C1 C2 NV : ℕ)
    (hB0 : 0 < B) (hP : 0 < P) (hCB : P < CB) (hC2 : P < C2) (hNV : P < NV)
    (hC1 : B + 1 < C1) (out : List Bool) :
    run (masterMachine2 M) (masterClock2 M B P CB C1 C2 NV out)
      (init (masterMachine2 M) (unaryD B ++ (unaryD P ++ (jT CB (P + 1) ++ (jT C1 0
        ++ (jT C2 1 ++ (jT NV 0 ++ encodeD out)))))))
      = ⟨masterFinal2 M, 2 * B + 2 * P + 2 * CB + 2 * (B + 1) + 9,
          unaryD B ++ (unaryD P ++ (jT CB 1 ++ (jT C1 (B + 2) ++ (jT C2 (P + 1)
            ++ (jT NV 0 ++ encodeD (out ++ masterOut2 M P B))))))⟩ := by
  have h1 := rep_cellFamily_run B P CB C1 C2 NV hP hCB hC2 hNV (by omega) out
  rw [cntT_zero B] at h1
  have h2 := rst4_run B 0 (by omega) P 0 (by omega) CB (P + 1) C1 B (by omega) (by omega)
    hB0 (jT C2 1 ++ (jT NV 0 ++ encodeD (out ++ cellEmitOut P B)))
  rw [cntT_zero B, cntT_zero P] at h2
  have h3 := rep_qcFamily_run (writeBodies M) (Fintype.card M.State) B P CB C1 C2 NV
    hCB hC2 hNV (by omega) (out ++ cellEmitOut P B)
  rw [cntT_zero B] at h3
  have h4 := rst4_run B 0 (by omega) P 0 (by omega) CB (P + 1) C1 B (by omega) (by omega)
    hB0 (jT C2 1 ++ (jT NV 0 ++ encodeD ((out ++ cellEmitOut P B)
      ++ qcEmitOut (writeBodies M) P (Fintype.card M.State) B)))
  rw [cntT_zero B, cntT_zero P] at h4
  have h5 := rep_qcFamily_run (dynBodies M) (Fintype.card M.State) B P CB C1 C2 NV
    hCB hC2 hNV (by omega)
    ((out ++ cellEmitOut P B) ++ qcEmitOut (writeBodies M) P (Fintype.card M.State) B)
  rw [cntT_zero B] at h5
  have h6 := rst4_run B 0 (by omega) P 0 (by omega) CB (P + 1) C1 B (by omega) (by omega)
    hB0 (jT C2 1 ++ (jT NV 0 ++ encodeD (((out ++ cellEmitOut P B)
      ++ qcEmitOut (writeBodies M) P (Fintype.card M.State) B)
      ++ qcEmitOut (dynBodies M) P (Fintype.card M.State) B)))
  rw [cntT_zero B, cntT_zero P] at h6
  have h7 := one3_run B 0 (by omega) P 0 (by omega) CB (P + 1) (by omega) (by omega)
    (jT C1 0 ++ (jT C2 1 ++ (jT NV 0 ++ encodeD (((out ++ cellEmitOut P B)
      ++ qcEmitOut (writeBodies M) P (Fintype.card M.State) B)
      ++ qcEmitOut (dynBodies M) P (Fintype.card M.State) B))))
  rw [cntT_zero B, cntT_zero P] at h7
  have h8 := rep_headFamily_run B P CB C1 C2 NV hP hCB hC2 hNV (by omega)
    (((out ++ cellEmitOut P B)
      ++ qcEmitOut (writeBodies M) P (Fintype.card M.State) B)
      ++ qcEmitOut (dynBodies M) P (Fintype.card M.State) B)
  rw [cntT_zero B] at h8
  have h9 := rst4_run B 0 (by omega) P 0 (by omega) CB 1 C1 B (by omega) (by omega)
    hB0 (jT C2 1 ++ (jT NV 0 ++ encodeD ((((out ++ cellEmitOut P B)
      ++ qcEmitOut (writeBodies M) P (Fintype.card M.State) B)
      ++ qcEmitOut (dynBodies M) P (Fintype.card M.State) B)
      ++ headEmitOut P B)))
  rw [cntT_zero B, cntT_zero P] at h9
  have h10 := rep_stateChain_run M B P CB C1 C2 NV (by omega) (by omega) (by omega)
    (by omega) ((((out ++ cellEmitOut P B)
      ++ qcEmitOut (writeBodies M) P (Fintype.card M.State) B)
      ++ qcEmitOut (dynBodies M) P (Fintype.card M.State) B)
      ++ headEmitOut P B)
  rw [cntT_zero B] at h10
  have h11 := rst4_run B 0 (by omega) P 0 (by omega) CB 1 C1 B (by omega) (by omega)
    hB0 (jT C2 1 ++ (jT NV 0 ++ encodeD (((((out ++ cellEmitOut P B)
      ++ qcEmitOut (writeBodies M) P (Fintype.card M.State) B)
      ++ qcEmitOut (dynBodies M) P (Fintype.card M.State) B)
      ++ headEmitOut P B)
      ++ qcEmitOut (stBodies M) 0 (Fintype.card M.State + 1) B)))
  rw [cntT_zero B, cntT_zero P] at h11
  have h12 := rep_dynHead0D_run M B P CB C1 C2 NV (by omega) (by omega) (by omega)
    (by omega) (((((out ++ cellEmitOut P B)
      ++ qcEmitOut (writeBodies M) P (Fintype.card M.State) B)
      ++ qcEmitOut (dynBodies M) P (Fintype.card M.State) B)
      ++ headEmitOut P B)
      ++ qcEmitOut (stBodies M) 0 (Fintype.card M.State + 1) B)
  rw [cntT_zero B] at h12
  have h13 := stateTop_pass_run M B P CB C1 C2 NV (by omega) (by omega) (by omega)
    (by omega) ((((((out ++ cellEmitOut P B)
      ++ qcEmitOut (writeBodies M) P (Fintype.card M.State) B)
      ++ qcEmitOut (dynBodies M) P (Fintype.card M.State) B)
      ++ headEmitOut P B)
      ++ qcEmitOut (stBodies M) 0 (Fintype.card M.State + 1) B)
      ++ qcEmitOut (leftBodies M) 0 (Fintype.card M.State) B)
  have h14 := headTop_run B 0 (by omega) P CB C1 C2 NV B hP hCB hC2 hNV (by omega)
    (((((((out ++ cellEmitOut P B)
      ++ qcEmitOut (writeBodies M) P (Fintype.card M.State) B)
      ++ qcEmitOut (dynBodies M) P (Fintype.card M.State) B)
      ++ headEmitOut P B)
      ++ qcEmitOut (stBodies M) 0 (Fintype.card M.State + 1) B)
      ++ qcEmitOut (leftBodies M) 0 (Fintype.card M.State) B)
      ++ ((stateOneHot M B).map encodeClause').flatten)
  rw [cntT_zero B] at h14
  have h15 := one3_run B 0 (by omega) P 0 (by omega) CB (P + 1) (by omega) (by omega)
    (jT C1 B ++ (jT C2 (P + 1) ++ (jT NV 0 ++ encodeD ((((((((out ++ cellEmitOut P B)
      ++ qcEmitOut (writeBodies M) P (Fintype.card M.State) B)
      ++ qcEmitOut (dynBodies M) P (Fintype.card M.State) B)
      ++ headEmitOut P B)
      ++ qcEmitOut (stBodies M) 0 (Fintype.card M.State + 1) B)
      ++ qcEmitOut (leftBodies M) 0 (Fintype.card M.State) B)
      ++ ((stateOneHot M B).map encodeClause').flatten)
      ++ (triRowOut amoPairRowHeadBody B P ++ (List.replicate (P + 1) true
        ++ ([false] ++ loop3Out aloRowHeadBody B (P + 1) (P + 1))))))))
  rw [cntT_zero B, cntT_zero P] at h15
  have h16 := acceptV_run M B P CB C1 C2 NV (P + 1) (by omega) (by omega) (by omega)
    (by omega) ((((((((out ++ cellEmitOut P B)
      ++ qcEmitOut (writeBodies M) P (Fintype.card M.State) B)
      ++ qcEmitOut (dynBodies M) P (Fintype.card M.State) B)
      ++ headEmitOut P B)
      ++ qcEmitOut (stBodies M) 0 (Fintype.card M.State + 1) B)
      ++ qcEmitOut (leftBodies M) 0 (Fintype.card M.State) B)
      ++ ((stateOneHot M B).map encodeClause').flatten)
      ++ (triRowOut amoPairRowHeadBody B P ++ (List.replicate (P + 1) true
        ++ ([false] ++ loop3Out aloRowHeadBody B (P + 1) (P + 1)))))
  have h17 := initConstV_run M B P CB C1 C2 NV (P + 1) (by omega) (by omega) (by omega)
    hC1 (((((((((out ++ cellEmitOut P B)
      ++ qcEmitOut (writeBodies M) P (Fintype.card M.State) B)
      ++ qcEmitOut (dynBodies M) P (Fintype.card M.State) B)
      ++ headEmitOut P B)
      ++ qcEmitOut (stBodies M) 0 (Fintype.card M.State + 1) B)
      ++ qcEmitOut (leftBodies M) 0 (Fintype.card M.State) B)
      ++ ((stateOneHot M B).map encodeClause').flatten)
      ++ (triRowOut amoPairRowHeadBody B P ++ (List.replicate (P + 1) true
        ++ ([false] ++ loop3Out aloRowHeadBody B (P + 1) (P + 1)))))
      ++ ((acceptFormula M B).map encodeClause').flatten)
  -- the halt ladder
  have hh17 : (qcMachine (fun _ => initConstBody M) 0 1).halt
      (qcFinal (fun _ => initConstBody M) 0 1) = true := qcFinal_halt _ 0 1
  have hh16 := seq_halt_final (qcMachine (fun _ => acceptBody M) 0 1) _ _ hh17
  have hh15 := seq_halt_final one3Machine _ _ hh16
  have hh14 := seq_halt_final headTopMachine _ _ hh15
  have hh13 := seq_halt_final (qcnMachine (stBodies M) 0 (Fintype.card M.State + 1))
    _ _ hh14
  have hh12 := seq_halt_final (repMachine (qcMachine (leftBodies M) 0
    (Fintype.card M.State))) _ _ hh13
  have hh11 := seq_halt_final rst4Machine _ _ hh12
  have hh10 := seq_halt_final (repMachine (qcMachine (stBodies M) 0
    (Fintype.card M.State + 1))) _ _ hh11
  have hh9 := seq_halt_final rst4Machine _ _ hh10
  have hh8 := seq_halt_final (repMachine headRoundMachine) _ _ hh9
  have hh7 := seq_halt_final one3Machine _ _ hh8
  have hh6 := seq_halt_final rst4Machine _ _ hh7
  have hh5 := seq_halt_final (repMachine (qcMachine (dynBodies M) 0
    (Fintype.card M.State))) _ _ hh6
  have hh4 := seq_halt_final rst4Machine _ _ hh5
  have hh3 := seq_halt_final (repMachine (qcMachine (writeBodies M) 0
    (Fintype.card M.State))) _ _ hh4
  have hh2 := seq_halt_final rst4Machine _ _ hh3
  -- the fold
  have s16 := seq_run _ _ _ _ _ _ _ _ _ _ _ h16 (qcFinal_halt _ 0 1) h17 hh17
  have s15 := seq_run _ _ _ _ _ _ _ _ _ _ _ h15 one3_halt s16 hh16
  have s14 := seq_run _ _ _ _ _ _ _ _ _ _ _ h14 headTop_halt s15 hh15
  have s13 := seq_run _ _ _ _ _ _ _ _ _ _ _ h13
    (qcnFinal_halt (stBodies M) 0 (Fintype.card M.State + 1)) s14 hh14
  have s12 := seq_run _ _ _ _ _ _ _ _ _ _ _ h12 rfl s13 hh13
  have s11 := seq_run _ _ _ _ _ _ _ _ _ _ _ h11 rst4_halt s12 hh12
  have s10 := seq_run _ _ _ _ _ _ _ _ _ _ _ h10 rfl s11 hh11
  have s9 := seq_run _ _ _ _ _ _ _ _ _ _ _ h9 rst4_halt s10 hh10
  have s8 := seq_run _ _ _ _ _ _ _ _ _ _ _ h8 rfl s9 hh9
  have s7 := seq_run _ _ _ _ _ _ _ _ _ _ _ h7 one3_halt s8 hh8
  have s6 := seq_run _ _ _ _ _ _ _ _ _ _ _ h6 rst4_halt s7 hh7
  have s5 := seq_run _ _ _ _ _ _ _ _ _ _ _ h5 rfl s6 hh6
  have s4 := seq_run _ _ _ _ _ _ _ _ _ _ _ h4 rst4_halt s5 hh5
  have s3 := seq_run _ _ _ _ _ _ _ _ _ _ _ h3 rfl s4 hh4
  have s2 := seq_run _ _ _ _ _ _ _ _ _ _ _ h2 rst4_halt s3 hh3
  have s1 := seq_run _ _ _ _ _ _ _ _ _ _ _ h1 rfl s2 hh2
  rw [show (((((((((out ++ cellEmitOut P B)
        ++ qcEmitOut (writeBodies M) P (Fintype.card M.State) B)
        ++ qcEmitOut (dynBodies M) P (Fintype.card M.State) B)
        ++ headEmitOut P B)
        ++ qcEmitOut (stBodies M) 0 (Fintype.card M.State + 1) B)
        ++ qcEmitOut (leftBodies M) 0 (Fintype.card M.State) B)
        ++ ((stateOneHot M B).map encodeClause').flatten)
        ++ (triRowOut amoPairRowHeadBody B P ++ (List.replicate (P + 1) true
          ++ ([false] ++ loop3Out aloRowHeadBody B (P + 1) (P + 1)))))
        ++ ((acceptFormula M B).map encodeClause').flatten)
        ++ (encodeClause' [(stateVar 0 (Fintype.equivFin M.State M.start).val, true)]
          ++ encodeClause' [(headVar 0 0, true)])
      = out ++ masterOut2 M P B from by
    simp [masterOut2, List.append_assoc]] at s1
  exact s1

/-- The chain's final state halts. -/
theorem masterFinal2_halt (M : Machine) :
    (masterMachine2 M).halt (masterFinal2 M) = true :=
  seq_halt_final _ _ _ (seq_halt_final _ _ _ (seq_halt_final _ _ _ (seq_halt_final _ _ _
    (seq_halt_final _ _ _ (seq_halt_final _ _ _ (seq_halt_final _ _ _ (seq_halt_final _ _ _
      (seq_halt_final _ _ _ (seq_halt_final _ _ _ (seq_halt_final _ _ _
        (seq_halt_final _ _ _ (seq_halt_final _ _ _ (seq_halt_final _ _ _
          (seq_halt_final _ _ _ (seq_halt_final _ _ _
            (qcFinal_halt _ 0 1))))))))))))))))

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitMaster2
