import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitStateChain

/-!
# Cook–Levin M2 emitter — E6 step 6: THE HEAD TOP BLOCK AND THE `v2`-GENERIC PASS

The head family's `t = B` one-hot: the triangle round WITHOUT the `interGrand` closer
(`headTopMachine` — six pieces, closed by the second `rearm6`), stated at a GENERIC grand
`(G, g)` and any `t ≤ C1` — no bump, but the row loop parks the bound and source mirrors at
`P + 1`.  Downstream passes therefore need the source mirror value free: `onePassV_run` is the
single-body `q`-chain pass with `v2` generic, and `acceptV_run`/`initConstV_run` are its
master-chain instantiations (run after the head top block, `C2 = P + 1`).
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitHeadTop

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
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitStateChain

/-! ## The head top block -/

/-- The triangle round minus the `interGrand` closer: no `t`-bump. -/
def headTopMachine : Machine :=
  seqMachine (seqMachine (seqMachine (seqMachine (seqMachine
    (repPMachine (seqMachine (pairTMachine amoPairRowHeadBody) interRowMachine))
    (pairTMachine cntTrueBody)) rearm6Machine) (snoc6Machine false))
    (pairTMachine aloRowHeadBody)) rearm6Machine

theorem headTop_halt : headTopMachine.halt (Sum.inr ((24 : Fin 25), false)) = true :=
  seq_halt_final _ rearm6Machine _ rearm6_halt

set_option maxHeartbeats 3200000 in
/-- **The head one-hot block at a FIXED time**: from the re-armed layout, emit time-`t`'s
at-most-one pairs (triangle order) and its at-least-one clause — the `t`-mirror untouched,
the bound and source mirrors parked at `P + 1`. -/
theorem headTop_run (G g : ℕ) (hg : g ≤ G) (P CB C1 C2 NV t : ℕ) (hP : 0 < P)
    (hCB : P < CB) (hC2 : P < C2) (hNV : P < NV) (htC : t ≤ C1) (out : List Bool) :
    run headTopMachine
      ((((((repPRounds G (fun r =>
            pairTClock amoPairRowHeadBody G P CB C1 C2 NV t (r + 1) (r + 1)
                (out ++ triRowOut amoPairRowHeadBody t r).length + 1
              + (2 * G + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (r + 1) + 18)) P
          + (4 * G + 4 * P + 8)) + 1
        + pairTClock cntTrueBody G P CB C1 C2 NV t (P + 1) (P + 1)
            (out ++ triRowOut amoPairRowHeadBody t P).length) + 1
        + (2 * G + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 18)) + 1
        + (2 * G + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV
          + 2 * ((out ++ triRowOut amoPairRowHeadBody t P)
              ++ List.replicate (P + 1) true).length + 24)) + 1
        + pairTClock aloRowHeadBody G P CB C1 C2 NV t (P + 1) (P + 1)
            (((out ++ triRowOut amoPairRowHeadBody t P)
              ++ List.replicate (P + 1) true) ++ [false]).length) + 1
        + (2 * G + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 18))
      (init headTopMachine (cntT G g ++ (unaryD P ++ (jT CB 1 ++ (jT C1 t
        ++ (jT C2 1 ++ (jT NV 0 ++ encodeD out)))))))
      = ⟨Sum.inr ((24 : Fin 25), false),
          2 * G + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 11,
          cntT G g ++ (unaryD P ++ (jT CB (P + 1) ++ (jT C1 t ++ (jT C2 (P + 1)
            ++ (jT NV 0 ++ encodeD (out ++ (triRowOut amoPairRowHeadBody t P
              ++ (List.replicate (P + 1) true
                ++ ([false] ++ loop3Out aloRowHeadBody t (P + 1) (P + 1))))))))))⟩ := by
  have hRL := repP_pairRow_run amoPairRowHeadBody G g hg P t CB C1 C2 NV
    htC hCB hC2 (by omega) out
  rw [cntT_zero P] at hRL
  have hCNT := pairT_run cntTrueBody G g hg P 0 (by omega) CB C1 C2 NV
    (P + 1) t (P + 1) (by omega) (by omega) (by omega) (by omega)
    (out ++ triRowOut amoPairRowHeadBody t P)
  rw [cntT_zero P, cnt3_split] at hCNT
  have hR1 := rearm6_run G g hg P 0 (by omega) CB C1 C2 NV (P + 1) t
    (P + 1) (P + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
    (encodeD ((out ++ triRowOut amoPairRowHeadBody t P) ++ List.replicate (P + 1) true))
  rw [cntT_zero P] at hR1
  have hS6 := snoc6_run false G g hg P 0 (by omega) CB C1 C2 NV (P + 1) t
    (P + 1) 0 (by omega) (by omega) (by omega) (by omega)
    ((out ++ triRowOut amoPairRowHeadBody t P) ++ List.replicate (P + 1) true)
  rw [cntT_zero P] at hS6
  have hALO := pairT_run aloRowHeadBody G g hg P 0 (by omega) CB C1 C2 NV
    (P + 1) t (P + 1) (by omega) (by omega) (by omega) (by omega)
    (((out ++ triRowOut amoPairRowHeadBody t P) ++ List.replicate (P + 1) true)
      ++ [false])
  rw [cntT_zero P] at hALO
  have hR2 := rearm6_run G g hg P 0 (by omega) CB C1 C2 NV (P + 1) t
    (P + 1) (P + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
    (encodeD ((((out ++ triRowOut amoPairRowHeadBody t P)
      ++ List.replicate (P + 1) true) ++ [false])
        ++ loop3Out aloRowHeadBody t (P + 1) (P + 1)))
  rw [cntT_zero P] at hR2
  have h1 := seq_run
    (repPMachine (seqMachine (pairTMachine amoPairRowHeadBody) interRowMachine))
    (pairTMachine cntTrueBody) _ _ _ _ _ _ _ _ _ hRL
    (repP_halt_inl4 (seqMachine (pairTMachine amoPairRowHeadBody) interRowMachine))
    hCNT rfl
  have h2 := seq_run _ rearm6Machine _ _ _ _ _ _ _ _ _ h1
    (seq_halt_final _ (pairTMachine cntTrueBody) _ rfl) hR1 rearm6_halt
  have h3 := seq_run _ (snoc6Machine false) _ _ _ _ _ _ _ _ _ h2
    (seq_halt_final _ rearm6Machine _ rearm6_halt) hS6 (snoc6_halt false)
  have h4 := seq_run _ (pairTMachine aloRowHeadBody) _ _ _ _ _ _ _ _ _ h3
    (seq_halt_final _ (snoc6Machine false) _ (snoc6_halt false)) hALO rfl
  have h5 := seq_run _ rearm6Machine _ _ _ _ _ _ _ _ _ h4
    (seq_halt_final _ (pairTMachine aloRowHeadBody) _ rfl) hR2 rearm6_halt
  rw [show ((((out ++ triRowOut amoPairRowHeadBody t P) ++ List.replicate (P + 1) true)
        ++ [false]) ++ loop3Out aloRowHeadBody t (P + 1) (P + 1))
      = out ++ (triRowOut amoPairRowHeadBody t P ++ (List.replicate (P + 1) true
          ++ ([false] ++ loop3Out aloRowHeadBody t (P + 1) (P + 1))))
      from by simp [List.append_assoc]] at h5
  exact h5

/-! ## The `v2`-generic single-body pass -/

set_option maxHeartbeats 1600000 in
/-- **The one-body pass with the source mirror free**: `pairT ⨟ rearm6 ⨟ incT6` at any
`v2 ≤ C2` — the accept/init-const passes after the head top block (`C2 = P + 1`). -/
theorem onePassV_run (body : List L3Instr) (G g : ℕ) (hg : g ≤ G)
    (R Q CB C1 C2 NV t v2 : ℕ) (hCB : Q < CB) (hv2C : v2 ≤ C2)
    (hNV : Q < NV) (ht : t < C1) (out : List Bool) :
    run (qcMachine (fun _ => body) 0 1)
      ((pairTClock body G R CB C1 C2 NV t v2 (Q + 1) out.length + 1
        + (2 * G + 2 * R + 2 * CB + 2 * C1 + 2 * C2 + 2 * (Q + 1) + 18)) + 1
        + (2 * G + 2 * R + 2 * CB + 2 * t + 12))
      (init (qcMachine (fun _ => body) 0 1) (cntT G g ++ (unaryD R ++ (jT CB (Q + 1)
        ++ (jT C1 t ++ (jT C2 v2 ++ (jT NV 0 ++ encodeD out)))))))
      = ⟨qcFinal (fun _ => body) 0 1, 2 * G + 2 * R + 2 * CB + 2 * t + 9,
          cntT G g ++ (unaryD R ++ (jT CB (Q + 1) ++ (jT C1 (t + 1) ++ (jT C2 v2
            ++ (jT NV 0 ++ encodeD (out ++ loop3Out body t v2 (Q + 1)))))))⟩ := by
  have hPT := pairT_run body G g hg R 0 (by omega) CB C1 C2 NV
    (Q + 1) t v2 (by omega) (by omega) hv2C (by omega) out
  rw [cntT_zero R] at hPT
  have hR := rearm6_run G g hg R 0 (by omega) CB C1 C2 NV (Q + 1) t v2
    (Q + 1) (by omega) (by omega) hv2C (by omega) (by omega)
    (encodeD (out ++ loop3Out body t v2 (Q + 1)))
  rw [cntT_zero R] at hR
  have hI := incT6_run G g hg R 0 (by omega) CB C1 (Q + 1) t (by omega) ht
    (jT C2 v2 ++ (jT NV 0 ++ encodeD (out ++ loop3Out body t v2 (Q + 1))))
  rw [cntT_zero R] at hI
  have h1 := seq_run (pairTMachine body) rearm6Machine _ _ _ _ _ _ _ _ _
    hPT rfl hR rearm6_halt
  have h2 := seq_run _ incT6Machine _ _ _ _ _ _ _ _ _ h1
    (seq_halt_final _ rearm6Machine _ rearm6_halt) hI rfl
  exact h2

/-! ## The chain-form instantiations -/

set_option maxHeartbeats 800000 in
/-- **The accept clause at source `v2`** — placed after the head top block. -/
theorem acceptV_run (M : Machine) (B P CB C1 C2 NV v2 : ℕ)
    (hCB : 0 < CB) (hv2C : v2 ≤ C2) (hNV : 0 < NV) (hBC1 : B < C1)
    (out : List Bool) :
    run (qcMachine (fun _ => acceptBody M) 0 1)
      ((pairTClock (acceptBody M) B P CB C1 C2 NV B v2 1 out.length + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * 1 + 18)) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * B + 12))
      (init (qcMachine (fun _ => acceptBody M) 0 1)
        (unaryD B ++ (unaryD P ++ (jT CB 1 ++ (jT C1 B ++ (jT C2 v2 ++ (jT NV 0
          ++ encodeD out)))))))
      = ⟨qcFinal (fun _ => acceptBody M) 0 1, 2 * B + 2 * P + 2 * CB + 2 * B + 9,
          unaryD B ++ (unaryD P ++ (jT CB 1 ++ (jT C1 (B + 1) ++ (jT C2 v2 ++ (jT NV 0
            ++ encodeD (out ++ ((acceptFormula M B).map encodeClause').flatten))))))⟩ := by
  have h := onePassV_run (acceptBody M) B 0 (by omega) P 0 CB C1 C2 NV B v2
    hCB hv2C hNV hBC1 out
  rw [cntT_zero B,
    show loop3Out (acceptBody M) B v2 (0 + 1)
      = ((acceptFormula M B).map encodeClause').flatten from by
    rw [loop3Out_one, accept_prog3Out, acceptFormula]
    simp] at h
  exact h

set_option maxHeartbeats 800000 in
/-- **The constant init clauses at source `v2`** — placed after the accept pass. -/
theorem initConstV_run (M : Machine) (B P CB C1 C2 NV v2 : ℕ)
    (hCB : 0 < CB) (hv2C : v2 ≤ C2) (hNV : 0 < NV) (hBC1 : B + 1 < C1)
    (out : List Bool) :
    run (qcMachine (fun _ => initConstBody M) 0 1)
      ((pairTClock (initConstBody M) B P CB C1 C2 NV (B + 1) v2 1 out.length + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * 1 + 18)) + 1
        + (2 * B + 2 * P + 2 * CB + 2 * (B + 1) + 12))
      (init (qcMachine (fun _ => initConstBody M) 0 1)
        (unaryD B ++ (unaryD P ++ (jT CB 1 ++ (jT C1 (B + 1) ++ (jT C2 v2 ++ (jT NV 0
          ++ encodeD out)))))))
      = ⟨qcFinal (fun _ => initConstBody M) 0 1,
          2 * B + 2 * P + 2 * CB + 2 * (B + 1) + 9,
          unaryD B ++ (unaryD P ++ (jT CB 1 ++ (jT C1 (B + 2) ++ (jT C2 v2 ++ (jT NV 0
            ++ encodeD (out
              ++ (encodeClause' [(stateVar 0 (Fintype.equivFin M.State M.start).val, true)]
                ++ encodeClause' [(headVar 0 0, true)])))))))⟩ := by
  have h := onePassV_run (initConstBody M) B 0 (by omega) P 0 CB C1 C2 NV (B + 1) v2
    hCB hv2C hNV hBC1 out
  rw [cntT_zero B,
    show loop3Out (initConstBody M) (B + 1) v2 (0 + 1)
      = encodeClause' [(stateVar 0 (Fintype.equivFin M.State M.start).val, true)]
        ++ encodeClause' [(headVar 0 0, true)] from by
    rw [loop3Out_one, initConst_prog3Out]] at h
  exact h

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitHeadTop
