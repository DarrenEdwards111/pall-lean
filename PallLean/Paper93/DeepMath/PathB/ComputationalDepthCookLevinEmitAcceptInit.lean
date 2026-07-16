import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitDynFamily
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitInitLoopP

/-!
# Cook–Levin M2 emitter — THE ACCEPT CLAUSE AND THE INIT PACKAGING

The two remaining clause groups of `fullTableau`:

* **accept** — ONE `atLeastOne` clause over the accepting-halting states at time `B`.  The time
  coordinate is `B`-SPLICED (the `t`-mirror holds `B` after the family grand loops), the state
  indices are machine constants — so the clause is emitted by a single one-shot `q`-chain pass
  (`P := 0`, bound armed at `1`, `n := 1`) with body `acceptBody M`: the literal count, then one
  `sA`-spliced literal block per accepting state.
* **init** — the two constant unit clauses (`state[0] = start`, `head[0] = 0`) as a one-shot
  constant body `initConstBody` in the same six-region layout, plus the input-spliced cell fixes
  already emitted by brick 27's `initCellP_family_run` (the `xVis` read-stage engine).
  `initFormula_streams` packages the whole `initFormula` encoding as those two streams.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitAcceptInit

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
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
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitSnoc6
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCellFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitWriteFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitDynFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInitLoop
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInitLoopP

/-! ## The accept body -/

/-- One `sA`-spliced positive state literal block per accepting-halting state. -/
noncomputable def acceptLitBlocks (M : Machine) : List L3Instr :=
  ((acceptStates M).map (fun q =>
    sA ++ (bitsI3 (encodeNat q.val) ++ bitsI3 [true, true, false, true]))).flatten

/-- The accept clause body: the literal count, then the literal blocks. -/
noncomputable def acceptBody (M : Machine) : List L3Instr :=
  bitsI3 (encodeNat (acceptStates M).length) ++ acceptLitBlocks M

theorem prog3Out_accept_blocks {n : ℕ} (l : List (Fin n)) (a c k : ℕ) :
    prog3Out ((l.map (fun q =>
        sA ++ (bitsI3 (encodeNat q.val) ++ bitsI3 [true, true, false, true]))).flatten) a c k
      = (l.map (fun q => encodeLit' (stateVar a q.val, true))).flatten := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    rw [List.map_cons, List.flatten_cons, prog3Out_append, List.map_cons, List.flatten_cons,
      ih, prog3Out_append, prog3Out_sA, prog3Out_append, prog3Out_bits, prog3Out_bits]
    simp [encodeLit'_stateVar, encodeNat, List.append_assoc]

/-- **The accept body emits the accept clause** — the `atLeastOne` over the accepting-halting
states, at the spliced time `a`. -/
theorem accept_prog3Out (M : Machine) (a c k : ℕ) :
    prog3Out (acceptBody M) a c k
      = encodeClause' (atLeastOne ((acceptStates M).map (fun q => stateVar a q.val))) := by
  rw [acceptBody, prog3Out_append, prog3Out_bits, acceptLitBlocks, prog3Out_accept_blocks,
    encodeClause', atLeastOne]
  simp [List.map_map, Function.comp_def]

/-! ## The accept pass

One one-shot `q`-chain pass at `t := B` — the `t`-mirror holds `B` after the family grand loops,
so `sA` splices the true final time into the clause. -/

set_option maxHeartbeats 800000 in
/-- **The accept clause is emitted, `B`-spliced.**  A single `q`-chain pass (`P := 0`, `n := 1`)
appends `encodeClause'` of the tableau's `acceptFormula M B`; the `t`-mirror advances to `B + 1`
(nothing after splices it). -/
theorem accept_pass_run (M : Machine) (B CB C1 C2 NV : ℕ)
    (hCB : 0 < CB) (hC2 : 0 < C2) (hNV : 0 < NV) (hBC1 : B < C1) (out : List Bool) :
    run (qcMachine (fun _ => acceptBody M) 0 1)
      (qcClock (fun _ => acceptBody M) (B + 1) 0 CB C1 C2 NV B 0 1 out.length)
      (init (qcMachine (fun _ => acceptBody M) 0 1)
        (cntT (B + 1) (B + 1) ++ (unaryD 0 ++ (jT CB 1 ++ (jT C1 B ++ (jT C2 1
          ++ (jT NV 0 ++ encodeD out)))))))
      = ⟨qcFinal (fun _ => acceptBody M) 0 1, 2 * (B + 1) + 2 * 0 + 2 * CB + 2 * B + 9,
          cntT (B + 1) (B + 1) ++ (unaryD 0 ++ (jT CB 1 ++ (jT C1 (B + 1) ++ (jT C2 1
            ++ (jT NV 0 ++ encodeD (out
              ++ ((acceptFormula M B).map encodeClause').flatten))))))⟩ := by
  have h := qc_run (fun _ => acceptBody M) (B + 1) 0 CB C1 C2 NV B hCB hC2 hNV
    (by omega) (by omega) 0 1 out
  rwa [show qcOut (fun _ => acceptBody M) B 0 0 1
      = ((acceptFormula M B).map encodeClause').flatten from by
    rw [show qcOut (fun _ => acceptBody M) B 0 0 1
        = loop3Out (acceptBody M) B 1 (0 + 1)
          ++ qcOut (fun _ => acceptBody M) B 0 1 0 from rfl,
      show qcOut (fun _ => acceptBody M) B 0 1 0 = [] from rfl,
      loop3Out_one, accept_prog3Out, acceptFormula]
    simp] at h

/-! ## The constant init clauses -/

/-- The two constant init unit clauses (`state[0] = start`, `head[0] = 0`) as one constant
body — no splices; emittable anywhere in the master chain. -/
noncomputable def initConstBody (M : Machine) : List L3Instr :=
  bitsI3 (encodeClause' [(stateVar 0 (Fintype.equivFin M.State M.start).val, true)]
    ++ encodeClause' [(headVar 0 0, true)])

theorem initConst_prog3Out (M : Machine) (a c k : ℕ) :
    prog3Out (initConstBody M) a c k
      = encodeClause' [(stateVar 0 (Fintype.equivFin M.State M.start).val, true)]
        ++ encodeClause' [(headVar 0 0, true)] := by
  rw [initConstBody, prog3Out_bits]

set_option maxHeartbeats 800000 in
/-- **The constant init clauses are emitted** by a one-shot pass at any grand time `t < B`. -/
theorem initConst_pass_run (M : Machine) (B CB C1 C2 NV t : ℕ)
    (hCB : 0 < CB) (hC2 : 0 < C2) (hNV : 0 < NV) (ht : t < B) (hBC1 : B ≤ C1)
    (out : List Bool) :
    run (qcMachine (fun _ => initConstBody M) 0 1)
      (qcClock (fun _ => initConstBody M) B 0 CB C1 C2 NV t 0 1 out.length)
      (init (qcMachine (fun _ => initConstBody M) 0 1)
        (cntT B (t + 1) ++ (unaryD 0 ++ (jT CB 1 ++ (jT C1 t ++ (jT C2 1
          ++ (jT NV 0 ++ encodeD out)))))))
      = ⟨qcFinal (fun _ => initConstBody M) 0 1, 2 * B + 2 * 0 + 2 * CB + 2 * t + 9,
          cntT B (t + 1) ++ (unaryD 0 ++ (jT CB 1 ++ (jT C1 (t + 1) ++ (jT C2 1
            ++ (jT NV 0 ++ encodeD (out
              ++ (encodeClause' [(stateVar 0 (Fintype.equivFin M.State M.start).val, true)]
                ++ encodeClause' [(headVar 0 0, true)])))))))⟩ := by
  have h := qc_run (fun _ => initConstBody M) B 0 CB C1 C2 NV t hCB hC2 hNV ht hBC1 0 1 out
  rwa [show qcOut (fun _ => initConstBody M) t 0 0 1
      = encodeClause' [(stateVar 0 (Fintype.equivFin M.State M.start).val, true)]
        ++ encodeClause' [(headVar 0 0, true)] from by
    rw [show qcOut (fun _ => initConstBody M) t 0 0 1
        = loop3Out (initConstBody M) t 1 (0 + 1)
          ++ qcOut (fun _ => initConstBody M) t 0 1 0 from rfl,
      show qcOut (fun _ => initConstBody M) t 0 1 0 = [] from rfl,
      loop3Out_one, initConst_prog3Out]
    simp] at h

/-! ## The init packaging -/

/-- **The `initFormula` encoding splits into the constant block and the cell stream.** -/
theorem initFormula_encode (M : Machine) (x : List Bool) (P : ℕ) :
    ((initFormula M x P).map encodeClause').flatten
      = encodeClause' [(stateVar 0 (Fintype.equivFin M.State M.start).val, true)]
        ++ (encodeClause' [(headVar 0 0, true)]
          ++ ((List.range (P + 1)).map (fun p =>
              encodeClause' [(cellVar 0 p, x.getD p false)])).flatten) := by
  rw [initFormula, fixBits]
  simp [List.map_map, Function.comp_def]

/-- **The `initFormula` encoding IS the two emitted streams**: the one-shot constant block
(`initConst_pass_run`) followed by brick 27's input-spliced cell stream
(`initCellP_family_run` at `N := P + 1`). -/
theorem initFormula_streams (M : Machine) (x : List Bool) (P a c k : ℕ) :
    ((initFormula M x P).map encodeClause').flatten
      = prog3Out (initConstBody M) a c k ++ initOut initCellBody x (P + 1) := by
  rw [initConst_prog3Out, initCell_split, initFormula_encode, List.append_assoc]

/-- The accept stream in the same idiom, for the E6 fold. -/
theorem acceptFormula_stream (M : Machine) (B a c k : ℕ) (hB : a = B) :
    ((acceptFormula M B).map encodeClause').flatten
      = prog3Out (acceptBody M) a c k := by
  subst hB
  rw [accept_prog3Out, acceptFormula]
  simp

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitAcceptInit
