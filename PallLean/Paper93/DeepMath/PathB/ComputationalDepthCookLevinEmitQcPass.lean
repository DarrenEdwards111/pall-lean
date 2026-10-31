import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitAcceptInit

/-!
# Cook–Levin M2 emitter — E6 step 1: THE DECOUPLED UNIVERSAL PASS

`qc_run` coupled the grand counter (`B`, `t+1`), the row size, and the loop bound through one
parameter `P`.  The master chain needs them independent: the one-shot passes (accept at spliced
`t = B`, the constant init clauses) run at bound `1` with the row still sized `P` and the grand
counter wherever the chain left it; the `dynB` one-shot grand loop needs bound `1` at row `P`.
The inner lemmas (`pairT_run`, `rearm6_run`, `incT6_run`) were always fully generic — this brick
re-states the chain run with grand `(G, g)`, row size `R`, and bound `Q + 1` as free parameters
(`qcPass_run`), wraps it in the decoupled grand loop (`rep_qcFamilyD_run`), and lands the three
master-chain instantiations: `rep_dynHead0D_run` (dynB at row `P`), `accept_chain_run`
(the accept clause `B`-spliced from the chain's own `t`-mirror), and `initConst_chain_run`.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitQcPass

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
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAcceptInit

/-! ## The decoupled clock -/

/-- The chain clock with grand size `G`, row size `R`, and bound `Q + 1` independent. -/
def qcClockD (bodies : ℕ → List L3Instr) (G R Q CB C1 C2 NV t : ℕ) : ℕ → ℕ → ℕ → ℕ
  | _, 0, _ => 2 * G + 2 * R + 2 * CB + 2 * t + 12
  | q0, n + 1, L =>
      (pairTClock (bodies q0) G R CB C1 C2 NV t 1 (Q + 1) L + 1
        + (2 * G + 2 * R + 2 * CB + 2 * C1 + 2 * C2 + 2 * (Q + 1) + 18)) + 1
        + qcClockD bodies G R Q CB C1 C2 NV t (q0 + 1) n
            (L + (loop3Out (bodies q0) t 1 (Q + 1)).length)

set_option maxHeartbeats 1600000 in
/-- **THE UNIVERSAL PASS**: the `q`-chain runs with the grand counter `(G, g)`, the row size
`R`, the bound `Q + 1`, and the `t`-mirror value `t` all independent — every body's block
emitted in index order, the live re-armed between blocks, the `t`-mirror advanced once. -/
theorem qcPass_run (bodies : ℕ → List L3Instr) (G g : ℕ) (hg : g ≤ G) (R Q CB C1 C2 NV t : ℕ)
    (hCB : Q < CB) (hC2 : 0 < C2) (hNV : Q < NV) (ht : t < C1) :
    ∀ (q0 n : ℕ) (out : List Bool),
    run (qcMachine bodies q0 n)
      (qcClockD bodies G R Q CB C1 C2 NV t q0 n out.length)
      (init (qcMachine bodies q0 n) (cntT G g ++ (unaryD R ++ (jT CB (Q + 1)
        ++ (jT C1 t ++ (jT C2 1 ++ (jT NV 0 ++ encodeD out)))))))
      = ⟨qcFinal bodies q0 n, 2 * G + 2 * R + 2 * CB + 2 * t + 9,
          cntT G g ++ (unaryD R ++ (jT CB (Q + 1) ++ (jT C1 (t + 1) ++ (jT C2 1
            ++ (jT NV 0 ++ encodeD (out ++ qcOut bodies t Q q0 n))))))⟩
  | q0, 0, out => by
    have h := incT6_run G g hg R 0 (by omega) CB C1 (Q + 1) t (by omega) ht
      (jT C2 1 ++ (jT NV 0 ++ encodeD out))
    rw [cntT_zero R] at h
    simpa [show qcOut bodies t Q q0 0 = [] from rfl] using h
  | q0, n + 1, out => by
    have hPT := pairT_run (bodies q0) G g hg R 0 (by omega) CB C1 C2 NV
      (Q + 1) t 1 (by omega) (by omega) (by omega) (by omega) out
    rw [cntT_zero R] at hPT
    have hR := rearm6_run G g hg R 0 (by omega) CB C1 C2 NV (Q + 1) t 1
      (Q + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      (encodeD (out ++ loop3Out (bodies q0) t 1 (Q + 1)))
    rw [cntT_zero R] at hR
    have h1 := seq_run (pairTMachine (bodies q0)) rearm6Machine _ _ _ _ _ _ _ _ _
      hPT rfl hR rearm6_halt
    have hrec := qcPass_run bodies G g hg R Q CB C1 C2 NV t hCB hC2 hNV ht (q0 + 1) n
      (out ++ loop3Out (bodies q0) t 1 (Q + 1))
    have h2 := seq_run _ (qcMachine bodies (q0 + 1) n) _ _ _ _ _ _ _ _ _ h1
      (seq_halt_final _ rearm6Machine _ rearm6_halt) hrec
      (qcFinal_halt bodies (q0 + 1) n)
    rw [List.length_append,
      show (out ++ loop3Out (bodies q0) t 1 (Q + 1)) ++ qcOut bodies t Q (q0 + 1) n
        = out ++ qcOut bodies t Q q0 (n + 1) from by rw [List.append_assoc]; rfl] at h2
    exact h2

set_option maxHeartbeats 1600000 in
/-- **The decoupled grand loop**: `B` rounds of the chain at row size `R`, bound `Q + 1`. -/
theorem rep_qcFamilyD_run (bodies : ℕ → List L3Instr) (card B R Q CB C1 C2 NV : ℕ)
    (hCB : Q < CB) (hC2 : 0 < C2) (hNV : Q < NV) (hBC1 : B ≤ C1)
    (out : List Bool) :
    run (repMachine (qcMachine bodies 0 card))
      (repRounds (fun t =>
        qcClockD bodies B R Q CB C1 C2 NV t 0 card
          (out ++ qcEmitOut bodies Q card t).length) B + (4 * B + 4))
      (init (repMachine (qcMachine bodies 0 card))
        (cntT B 0 ++ (unaryD R ++ (jT CB (Q + 1) ++ (jT C1 0 ++ (jT C2 1 ++ (jT NV 0
          ++ encodeD out)))))))
      = ⟨Sum.inl (4, false), 2 * B + 1,
          unaryD B ++ (unaryD R ++ (jT CB (Q + 1) ++ (jT C1 B ++ (jT C2 1 ++ (jT NV 0
            ++ encodeD (out ++ qcEmitOut bodies Q card B))))))⟩ := by
  have h := rep_run (qcMachine bodies 0 card) B
    (fun t => unaryD R ++ (jT CB (Q + 1) ++ (jT C1 t ++ (jT C2 1 ++ (jT NV 0
      ++ encodeD (out ++ qcEmitOut bodies Q card t))))))
    (fun t => qcClockD bodies B R Q CB C1 C2 NV t 0 card
      (out ++ qcEmitOut bodies Q card t).length)
    (fun _ => qcFinal bodies 0 card)
    (fun t => 2 * B + 2 * R + 2 * CB + 2 * t + 9)
    (fun t ht => by
      constructor
      · have hrd := qcPass_run bodies B (t + 1) (by omega) R Q CB C1 C2 NV t hCB hC2 hNV
          (by omega) 0 card (out ++ qcEmitOut bodies Q card t)
        rw [show (out ++ qcEmitOut bodies Q card t) ++ qcOut bodies t Q 0 card
            = out ++ qcEmitOut bodies Q card (t + 1) from by
              rw [List.append_assoc]; rfl] at hrd
        exact hrd
      · exact qcFinal_halt bodies 0 card)
  simp only [show qcEmitOut bodies Q card 0 = [] from rfl, List.append_nil] at h
  exact h

/-! ## The master-chain instantiations -/

/-- **The dynB grand loop at row `P`** — the one-shot `p = 0` left-head chain, bound `1`,
row region untouched at size `P` (chain-compatible with the `P`-bound family loops). -/
theorem rep_dynHead0D_run (M : Machine) (B P CB C1 C2 NV : ℕ)
    (hCB : 0 < CB) (hC2 : 0 < C2) (hNV : 0 < NV) (hBC1 : B ≤ C1) (out : List Bool) :
    run (repMachine (qcMachine (leftBodies M) 0 (Fintype.card M.State)))
      (repRounds (fun t =>
        qcClockD (leftBodies M) B P 0 CB C1 C2 NV t 0 (Fintype.card M.State)
          (out ++ qcEmitOut (leftBodies M) 0 (Fintype.card M.State) t).length) B
        + (4 * B + 4))
      (init (repMachine (qcMachine (leftBodies M) 0 (Fintype.card M.State)))
        (cntT B 0 ++ (unaryD P ++ (jT CB 1 ++ (jT C1 0 ++ (jT C2 1 ++ (jT NV 0
          ++ encodeD out)))))))
      = ⟨Sum.inl (4, false), 2 * B + 1,
          unaryD B ++ (unaryD P ++ (jT CB 1 ++ (jT C1 B ++ (jT C2 1 ++ (jT NV 0
            ++ encodeD (out
              ++ qcEmitOut (leftBodies M) 0 (Fintype.card M.State) B))))))⟩ :=
  rep_qcFamilyD_run (leftBodies M) (Fintype.card M.State) B P 0 CB C1 C2 NV
    hCB hC2 hNV hBC1 out

set_option maxHeartbeats 800000 in
/-- **The accept clause from the chain's own mirrors**: after the last grand loop the tape is
exactly this form (`unaryD B` grand, `t`-mirror at `B`) — one universal pass emits
`encodeClause'` of `acceptFormula M B`, the true final time spliced. -/
theorem accept_chain_run (M : Machine) (B P CB C1 C2 NV : ℕ)
    (hCB : 0 < CB) (hC2 : 0 < C2) (hNV : 0 < NV) (hBC1 : B < C1) (out : List Bool) :
    run (qcMachine (fun _ => acceptBody M) 0 1)
      (qcClockD (fun _ => acceptBody M) B P 0 CB C1 C2 NV B 0 1 out.length)
      (init (qcMachine (fun _ => acceptBody M) 0 1)
        (unaryD B ++ (unaryD P ++ (jT CB 1 ++ (jT C1 B ++ (jT C2 1 ++ (jT NV 0
          ++ encodeD out)))))))
      = ⟨qcFinal (fun _ => acceptBody M) 0 1, 2 * B + 2 * P + 2 * CB + 2 * B + 9,
          unaryD B ++ (unaryD P ++ (jT CB 1 ++ (jT C1 (B + 1) ++ (jT C2 1 ++ (jT NV 0
            ++ encodeD (out ++ ((acceptFormula M B).map encodeClause').flatten))))))⟩ := by
  have h := qcPass_run (fun _ => acceptBody M) B 0 (by omega) P 0 CB C1 C2 NV B
    hCB hC2 hNV hBC1 0 1 out
  rw [cntT_zero B] at h
  rwa [show qcOut (fun _ => acceptBody M) B 0 0 1
      = ((acceptFormula M B).map encodeClause').flatten from by
    rw [show qcOut (fun _ => acceptBody M) B 0 0 1
        = loop3Out (acceptBody M) B 1 (0 + 1)
          ++ qcOut (fun _ => acceptBody M) B 0 1 0 from rfl,
      show qcOut (fun _ => acceptBody M) B 0 1 0 = [] from rfl,
      loop3Out_one, accept_prog3Out, acceptFormula]
    simp] at h

set_option maxHeartbeats 800000 in
/-- **The constant init clauses from the chain's mirrors** — run after the accept pass
(`t`-mirror at `B + 1`; the body has no splices, so the value is irrelevant). -/
theorem initConst_chain_run (M : Machine) (B P CB C1 C2 NV : ℕ)
    (hCB : 0 < CB) (hC2 : 0 < C2) (hNV : 0 < NV) (hBC1 : B + 1 < C1) (out : List Bool) :
    run (qcMachine (fun _ => initConstBody M) 0 1)
      (qcClockD (fun _ => initConstBody M) B P 0 CB C1 C2 NV (B + 1) 0 1 out.length)
      (init (qcMachine (fun _ => initConstBody M) 0 1)
        (unaryD B ++ (unaryD P ++ (jT CB 1 ++ (jT C1 (B + 1) ++ (jT C2 1 ++ (jT NV 0
          ++ encodeD out)))))))
      = ⟨qcFinal (fun _ => initConstBody M) 0 1,
          2 * B + 2 * P + 2 * CB + 2 * (B + 1) + 9,
          unaryD B ++ (unaryD P ++ (jT CB 1 ++ (jT C1 (B + 2) ++ (jT C2 1 ++ (jT NV 0
            ++ encodeD (out
              ++ (encodeClause' [(stateVar 0 (Fintype.equivFin M.State M.start).val, true)]
                ++ encodeClause' [(headVar 0 0, true)])))))))⟩ := by
  have h := qcPass_run (fun _ => initConstBody M) B 0 (by omega) P 0 CB C1 C2 NV (B + 1)
    hCB hC2 hNV hBC1 0 1 out
  rw [cntT_zero B] at h
  rwa [show qcOut (fun _ => initConstBody M) (B + 1) 0 0 1
      = encodeClause' [(stateVar 0 (Fintype.equivFin M.State M.start).val, true)]
        ++ encodeClause' [(headVar 0 0, true)] from by
    rw [show qcOut (fun _ => initConstBody M) (B + 1) 0 0 1
        = loop3Out (initConstBody M) (B + 1) 1 (0 + 1)
          ++ qcOut (fun _ => initConstBody M) (B + 1) 0 1 0 from rfl,
      show qcOut (fun _ => initConstBody M) (B + 1) 0 1 0 = [] from rfl,
      loop3Out_one, initConst_prog3Out]
    simp] at h

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitQcPass
