import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitCellFamily

/-!
# Cook–Levin M2 emitter — THE WRITE FAMILY, ALL TIMES, ONE MACHINE

The write family loops `t < B`, `q < card`, `p ≤ P`, `b ∈ {false, true}` — one implication
window per tuple.  The state index `q` and the written bit are MACHINE CONSTANTS, so the `q`
level unrolls into a `seq`-chain of stale-bound passes; the `b` level fuses into the per-`p`
body (`writePairBody`).  This file builds the **generic `q`-chain combinator**
(`qcMachine`/`qc_run`: a recursive chain of `[stale-bound pass ⨟ rearm6]` closed by `incT6`,
with its clock, output stream, and dependent final state) and its grand-loop wrap
(`rep_qcFamily_run`) — reusable for the dynamics family — then instantiates the write family:
`rep_writeFamily_run` + `writeEmitOut_writeFamily` read the stream as `encodeClause'` of the
tableau's `writeFamily M P B`, clause-for-clause, in order — no permutation.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitWriteFamily

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinDoubled
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinDynamics
open PallLean.Paper93.DeepMath.PathB.CookLevinWrite
open PallLean.Paper93.DeepMath.PathB.CookLevinConverse
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

/-! ## The three-source write bodies -/

/-- The shared implication-window guard prefix, three-source layout. -/
def winPre3 (qi : ℕ) (b : Bool) : List L3Instr :=
  bitsI3 [true, true, true, true, false] ++ (sA ++ (bitsI3 (encodeNat qi)
    ++ (bitsI3 [true, true, false, false] ++ (sA ++ (sJ
      ++ (bitsI3 [true, false, false] ++ (sA ++ (sJ ++ bitsI3 [false, !b]))))))))

theorem winPre3_prog3Out (qi : ℕ) (b : Bool) (t c k : ℕ) :
    prog3Out (winPre3 qi b) t c k
      = encodeNat 4 ++ (encodeNat t ++ (encodeNat qi ++ (encodeNat 2 ++ ([false]
          ++ (encodeNat t ++ (encodeNat k ++ (encodeNat 1 ++ ([false]
          ++ (encodeNat t ++ (encodeNat k ++ (encodeNat 0 ++ [!b]))))))))))) := by
  rw [winPre3]
  simp only [prog3Out_append, prog3Out_bits, prog3Out_sA, prog3Out_sJ]
  simp [encodeNat, List.append_assoc]

/-- The write window's body at guard `(q̂, b)`, written bit `wb`. -/
def writeRowBody (qi : ℕ) (b wb : Bool) : List L3Instr :=
  winPre3 qi b ++ (sA1 ++ (sJ ++ bitsI3 [false, wb]))

theorem writeRow_prog3Out (qi : ℕ) (b wb : Bool) (t c k : ℕ) :
    prog3Out (writeRowBody qi b wb) t c k
      = encodeClause' (implClause (stateVar t qi, true) (headVar t k, true)
          (cellVar t k, b) (cellVar (t + 1) k, wb)) := by
  rw [encodeClause'_implWindow, encodeLit'_cellVar, writeRowBody, sA1]
  simp only [prog3Out_append, winPre3_prog3Out, prog3Out_bits, prog3Out_sA, prog3Out_sJ]
  simp [encodeNat, List.replicate_succ, List.append_assoc]

/-- The fused per-`p` body: both `b` guards, one round. -/
def writePairBody (qi : ℕ) (wbF wbT : Bool) : List L3Instr :=
  writeRowBody qi false wbF ++ writeRowBody qi true wbT

theorem writePair_prog3Out (qi : ℕ) (wbF wbT : Bool) (t c k : ℕ) :
    prog3Out (writePairBody qi wbF wbT) t c k
      = encodeClause' (implClause (stateVar t qi, true) (headVar t k, true)
          (cellVar t k, false) (cellVar (t + 1) k, wbF))
        ++ encodeClause' (implClause (stateVar t qi, true) (headVar t k, true)
            (cellVar t k, true) (cellVar (t + 1) k, wbT)) := by
  rw [writePairBody, prog3Out_append, writeRow_prog3Out, writeRow_prog3Out]

/-! ## The generic `q`-chain

A recursive chain of `[stale-bound pass ⨟ rearm6]`, one per body index `q0, q0+1, …`, closed
by the `t`-mirror increment — the per-round machine for every family whose state level is a
finite unrolled constant. -/

def qcMachine (bodies : ℕ → List L3Instr) : ℕ → ℕ → Machine
  | _, 0 => incT6Machine
  | q0, n + 1 => seqMachine (seqMachine (pairTMachine (bodies q0)) rearm6Machine)
      (qcMachine bodies (q0 + 1) n)

def qcFinal (bodies : ℕ → List L3Instr) : (q0 n : ℕ) → (qcMachine bodies q0 n).State
  | _, 0 => (14, false)
  | q0, n + 1 => Sum.inr (qcFinal bodies (q0 + 1) n)

theorem qcFinal_halt (bodies : ℕ → List L3Instr) : ∀ q0 n,
    (qcMachine bodies q0 n).halt (qcFinal bodies q0 n) = true
  | _, 0 => rfl
  | q0, n + 1 => seq_halt_final _ _ _ (qcFinal_halt bodies (q0 + 1) n)

/-- The chain's output stream: one stale-bound block per body index. -/
def qcOut (bodies : ℕ → List L3Instr) (t P : ℕ) : ℕ → ℕ → List Bool
  | _, 0 => []
  | q0, n + 1 => loop3Out (bodies q0) t 1 (P + 1) ++ qcOut bodies t P (q0 + 1) n

def qcClock (bodies : ℕ → List L3Instr) (B P CB C1 C2 NV t : ℕ) : ℕ → ℕ → ℕ → ℕ
  | _, 0, _ => 2 * B + 2 * P + 2 * CB + 2 * t + 12
  | q0, n + 1, L =>
      (pairTClock (bodies q0) B P CB C1 C2 NV t 1 (P + 1) L + 1
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 18)) + 1
        + qcClock bodies B P CB C1 C2 NV t (q0 + 1) n
            (L + (loop3Out (bodies q0) t 1 (P + 1)).length)

set_option maxHeartbeats 1600000 in
/-- **The `q`-chain runs**: every body's stale-bound block emitted in index order, the live
re-armed between blocks, the `t`-mirror advanced once at the close. -/
theorem qc_run (bodies : ℕ → List L3Instr) (B P CB C1 C2 NV t : ℕ) (hP : 0 < P)
    (hCB : P < CB) (hC2 : P < C2) (hNV : P < NV) (ht : t < B) (hBC1 : B ≤ C1) :
    ∀ (q0 n : ℕ) (out : List Bool),
    run (qcMachine bodies q0 n)
      (qcClock bodies B P CB C1 C2 NV t q0 n out.length)
      (init (qcMachine bodies q0 n) (cntT B (t + 1) ++ (unaryD P ++ (jT CB (P + 1)
        ++ (jT C1 t ++ (jT C2 1 ++ (jT NV 0 ++ encodeD out)))))))
      = ⟨qcFinal bodies q0 n, 2 * B + 2 * P + 2 * CB + 2 * t + 9,
          cntT B (t + 1) ++ (unaryD P ++ (jT CB (P + 1) ++ (jT C1 (t + 1) ++ (jT C2 1
            ++ (jT NV 0 ++ encodeD (out ++ qcOut bodies t P q0 n))))))⟩
  | q0, 0, out => by
    have h := incT6_run B (t + 1) (by omega) P 0 (by omega) CB C1 (P + 1) t (by omega)
      (by omega) (jT C2 1 ++ (jT NV 0 ++ encodeD out))
    rw [cntT_zero P] at h
    simpa [show qcOut bodies t P q0 0 = [] from rfl] using h
  | q0, n + 1, out => by
    have hPT := pairT_run (bodies q0) B (t + 1) (by omega) P 0 (by omega) CB C1 C2 NV
      (P + 1) t 1 (by omega) (by omega) (by omega) (by omega) out
    rw [cntT_zero P] at hPT
    have hR := rearm6_run B (t + 1) (by omega) P 0 (by omega) CB C1 C2 NV (P + 1) t 1
      (P + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      (encodeD (out ++ loop3Out (bodies q0) t 1 (P + 1)))
    rw [cntT_zero P] at hR
    have h1 := seq_run (pairTMachine (bodies q0)) rearm6Machine _ _ _ _ _ _ _ _ _
      hPT rfl hR rearm6_halt
    have hrec := qc_run bodies B P CB C1 C2 NV t hP hCB hC2 hNV ht hBC1 (q0 + 1) n
      (out ++ loop3Out (bodies q0) t 1 (P + 1))
    have h2 := seq_run _ (qcMachine bodies (q0 + 1) n) _ _ _ _ _ _ _ _ _ h1
      (seq_halt_final _ rearm6Machine _ rearm6_halt) hrec
      (qcFinal_halt bodies (q0 + 1) n)
    rw [List.length_append,
      show (out ++ loop3Out (bodies q0) t 1 (P + 1)) ++ qcOut bodies t P (q0 + 1) n
        = out ++ qcOut bodies t P q0 (n + 1) from by rw [List.append_assoc]; rfl] at h2
    exact h2

/-! ## The generic grand loop over a `q`-chain family -/

/-- The accumulated family stream. -/
def qcEmitOut (bodies : ℕ → List L3Instr) (P card : ℕ) : ℕ → List Bool
  | 0 => []
  | t + 1 => qcEmitOut bodies P card t ++ qcOut bodies t P 0 card

set_option maxHeartbeats 1600000 in
/-- **The generic `q`-chain family stream**: `B` grand rounds of the chain. -/
theorem rep_qcFamily_run (bodies : ℕ → List L3Instr) (card B P CB C1 C2 NV : ℕ)
    (hP : 0 < P) (hCB : P < CB) (hC2 : P < C2) (hNV : P < NV) (hBC1 : B ≤ C1)
    (out : List Bool) :
    run (repMachine (qcMachine bodies 0 card))
      (repRounds (fun t =>
        qcClock bodies B P CB C1 C2 NV t 0 card
          (out ++ qcEmitOut bodies P card t).length) B + (4 * B + 4))
      (init (repMachine (qcMachine bodies 0 card))
        (cntT B 0 ++ (unaryD P ++ (jT CB (P + 1) ++ (jT C1 0 ++ (jT C2 1 ++ (jT NV 0
          ++ encodeD out)))))))
      = ⟨Sum.inl (4, false), 2 * B + 1,
          unaryD B ++ (unaryD P ++ (jT CB (P + 1) ++ (jT C1 B ++ (jT C2 1 ++ (jT NV 0
            ++ encodeD (out ++ qcEmitOut bodies P card B))))))⟩ := by
  have h := rep_run (qcMachine bodies 0 card) B
    (fun t => unaryD P ++ (jT CB (P + 1) ++ (jT C1 t ++ (jT C2 1 ++ (jT NV 0
      ++ encodeD (out ++ qcEmitOut bodies P card t))))))
    (fun t => qcClock bodies B P CB C1 C2 NV t 0 card
      (out ++ qcEmitOut bodies P card t).length)
    (fun _ => qcFinal bodies 0 card)
    (fun t => 2 * B + 2 * P + 2 * CB + 2 * t + 9)
    (fun t ht => by
      constructor
      · have hrd := qc_run bodies B P CB C1 C2 NV t hP hCB hC2 hNV ht hBC1 0 card
          (out ++ qcEmitOut bodies P card t)
        rw [show (out ++ qcEmitOut bodies P card t) ++ qcOut bodies t P 0 card
            = out ++ qcEmitOut bodies P card (t + 1) from by
              rw [List.append_assoc]; rfl] at hrd
        exact hrd
      · exact qcFinal_halt bodies 0 card)
  simp only [show qcEmitOut bodies P card 0 = [] from rfl, List.append_nil] at h
  exact h

/-! ## The write-family instantiation -/

/-- The written bit, ℕ-indexed (total; the chain only reads indices below `card`). -/
noncomputable def wbitN (M : Machine) (qi : ℕ) (b : Bool) : Bool :=
  if h : qi < Fintype.card M.State
  then writtenBit M ((Fintype.equivFin M.State).symm ⟨qi, h⟩) b else false

/-- The write family's `q`-chain bodies. -/
noncomputable def writeBodies (M : Machine) (qi : ℕ) : List L3Instr :=
  writePairBody qi (wbitN M qi false) (wbitN M qi true)

/-- The per-`(t, q)` block IS the `b`-unrolled write clauses' encodings. -/
theorem writeBlock_encode (M : Machine) (t P : ℕ) (q : Fin (Fintype.card M.State)) :
    loop3Out (writeBodies M q.val) t 1 (P + 1)
      = ((bigAnd ((List.range (P + 1)).map (fun p =>
          bigAnd ([false, true].map (fun b => writeClause M t q p b))))).map
            encodeClause').flatten := by
  rw [bigAnd, flatten_map_flatten, List.map_map, loop3Out_eq_flatten]
  congr 1
  apply List.map_congr_left
  intro p hp
  rw [Function.comp_def, writeBodies, writePair_prog3Out]
  have hF : wbitN M q.val false
      = writtenBit M ((Fintype.equivFin M.State).symm q) false := by
    rw [wbitN, dif_pos q.isLt]
  have hT : wbitN M q.val true
      = writtenBit M ((Fintype.equivFin M.State).symm q) true := by
    rw [wbitN, dif_pos q.isLt]
  simp [bigAnd, writeClause_members, hF, hT]

/-- The chain output at `(q0, n)` matches the `finRange` suffix — stated over `List.range`
shifts. -/
theorem qcOut_range (bodies : ℕ → List L3Instr) (t P : ℕ) : ∀ n q0,
    qcOut bodies t P q0 n
      = ((List.range n).map (fun i => loop3Out (bodies (q0 + i)) t 1 (P + 1))).flatten
  | 0, _ => rfl
  | n + 1, q0 => by
    rw [show qcOut bodies t P q0 (n + 1)
        = loop3Out (bodies q0) t 1 (P + 1) ++ qcOut bodies t P (q0 + 1) n from rfl,
      qcOut_range bodies t P n (q0 + 1), List.range_succ_eq_map, List.map_cons,
      List.flatten_cons, List.map_map]
    congr 1
    congr 1
    apply List.map_congr_left
    intro i hi
    simp only [Function.comp, Nat.succ_eq_add_one]
    rw [show q0 + (i + 1) = q0 + 1 + i from by omega]

/-- `finRange`-maps that factor through `Fin.val` are `range`-maps. -/
theorem finRange_map_val {α : Type} : ∀ (n : ℕ) (g : ℕ → α),
    (List.finRange n).map (fun q => g q.val) = (List.range n).map g
  | 0, _ => rfl
  | n + 1, g => by
    rw [List.finRange_succ, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map]
    congr 1
    rw [show ((fun q : Fin (n + 1) => g q.val) ∘ Fin.succ)
        = (fun q : Fin n => (fun i => g (i + 1)) q.val) from
          funext (fun q => by simp [Function.comp, Fin.val_succ]),
      finRange_map_val n (fun i => g (i + 1))]
    rfl

/-- **The write stream equals `encodeClause'` of the tableau's `writeFamily` — in order.** -/
theorem qcEmitOut_writeFamily (M : Machine) (P : ℕ) : ∀ B,
    qcEmitOut (writeBodies M) P (Fintype.card M.State) B
      = ((writeFamily M P B).map encodeClause').flatten
  | 0 => by simp [qcEmitOut, writeFamily, bigAnd]
  | B + 1 => by
    have hstep : writeFamily M P (B + 1)
        = writeFamily M P B
          ++ bigAnd ((List.finRange (Fintype.card M.State)).map (fun q =>
              bigAnd ((List.range (P + 1)).map (fun p =>
                bigAnd ([false, true].map (fun b => writeClause M B q p b)))))) := by
      rw [writeFamily, writeFamily, bigAnd, bigAnd, List.range_succ (n := B),
        List.map_append, List.flatten_append]
      simp [bigAnd]
    rw [show qcEmitOut (writeBodies M) P (Fintype.card M.State) (B + 1)
        = qcEmitOut (writeBodies M) P (Fintype.card M.State) B
            ++ qcOut (writeBodies M) B P 0 (Fintype.card M.State) from rfl,
      qcEmitOut_writeFamily M P B, hstep, List.map_append, List.flatten_append]
    congr 1
    rw [bigAnd, flatten_map_flatten, List.map_map,
      qcOut_range (writeBodies M) B P (Fintype.card M.State) 0]
    rw [show (fun i => loop3Out (writeBodies M (0 + i)) B 1 (P + 1))
        = (fun i => loop3Out (writeBodies M i) B 1 (P + 1)) from
          funext (fun i => by rw [Nat.zero_add]),
      ← finRange_map_val (Fintype.card M.State)
        (fun i => loop3Out (writeBodies M i) B 1 (P + 1))]
    congr 1
    apply List.map_congr_left
    intro q hq
    exact writeBlock_encode M B P q

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitWriteFamily
