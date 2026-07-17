import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitBodyLens

/-!
# Cook–Levin M2 emitter — E6 step 23: THE CLOSER (part i — the master clock bound)

The uniform pass bound `KU`, the global output budget `LMB`, and `masterClock2_le`: the
seventeen-piece master clock at the concrete sizes is at most an explicit polynomial
expression `MCB` in `(card, B, P, L0)`.  Everything by bricks 67–69's lemmas; generous slack
throughout.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitFinale

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction (Satisfiable)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPackage2 (emittedReduction)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitTapeCodec (decodeTape)
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCore (emitterCoreMachine)
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinOneHotWindow
open PallLean.Paper93.DeepMath.PathB.CookLevinInitAccept
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCodec
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPairT
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRepP
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitInterRow
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitTriangleHead
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitHeadFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitCellFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitWriteFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitDynFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitAcceptInit
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitQcPass
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitStateChain
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitMaster2
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPipeline
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitClockBounds
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitClockBounds2
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitClockBounds3
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitBodyLens

/-! ## The uniform budgets -/

/-- The uniform body budget. -/
def BDA (s : ℕ) : ℕ := 4 * s * s + 40 * s + 200

theorem writeBodies_le_BDA (M : Machine) (q : ℕ) (hq : q < Fintype.card M.State) :
    (writeBodies M q).length ≤ BDA (Fintype.card M.State) := by
  have := writeBodies_length_le M q
  rw [BDA]; nlinarith [Nat.zero_le (Fintype.card M.State)]

theorem dynBodies_le_BDA (M : Machine) (q : ℕ) (hq : q < Fintype.card M.State) :
    (dynBodies M q).length ≤ BDA (Fintype.card M.State) := by
  have := dynBodies_length_le M q
  rw [BDA]; nlinarith [Nat.zero_le (Fintype.card M.State)]

theorem stBodies_le_BDA (M : Machine) (q : ℕ) (hq : q < Fintype.card M.State + 1) :
    (stBodies M q).length ≤ BDA (Fintype.card M.State) := by
  have := stBodies_length_le M q (by omega)
  rw [BDA]; nlinarith [Nat.zero_le (Fintype.card M.State)]

theorem leftBodies_le_BDA (M : Machine) (q : ℕ) (hq : q < Fintype.card M.State) :
    (leftBodies M q).length ≤ BDA (Fintype.card M.State) := by
  have := leftBodies_length_le M q
  rw [BDA]; nlinarith [Nat.zero_le (Fintype.card M.State)]

theorem acceptBody_le_BDA (M : Machine) :
    (acceptBody M).length ≤ BDA (Fintype.card M.State) := by
  have := acceptBody_length_le M
  rw [BDA]; nlinarith [Nat.zero_le (Fintype.card M.State)]

theorem initConstBody_le_BDA (M : Machine) :
    (initConstBody M).length ≤ BDA (Fintype.card M.State) := by
  have := initConstBody_length_le M
  rw [BDA]; nlinarith [Nat.zero_le (Fintype.card M.State)]

theorem lit_le_BDA (s : ℕ) : 100 ≤ BDA s := by rw [BDA]; nlinarith [Nat.zero_le s]

/-- The global output budget: entry length plus every stream's full bound plus in-pass
slack. -/
def LMB (s B P L0 : ℕ) : ℕ :=
  L0 + B * ((P + 1) * (100 * (B + P + 3)))
    + B * (s * qcPassOut P (BDA s) B)
    + B * (s * qcPassOut P (BDA s) B)
    + B * headRoundOut P B
    + B * ((s + 1) * qcPassOut 0 (BDA s) B)
    + B * (s * qcPassOut 0 (BDA s) B)
    + 2 * headRoundOut P B
    + (s + 1) * qcPassOut 0 (BDA s) B
    + (s + 2) * qcPassOut P (BDA s) (B + 2)
    + P * (P * (100 * (B + 2 * P + 8)))
    + (P + 1) * (100 * (B + 2 * P + 8))
    + (P + 2) * (BDA s * (B + 2 * P + 8))
    + (P + 2)
    + 1000

/-! ## The uniform pass bounds -/

/-- The `qc`-pass bound at the worst chain parameters. -/
def KQ (s B P L0 : ℕ) : ℕ :=
  qcPassBound B P (P + 2) (B + 2) (P + 2) (P + 2) (B + 2) P (BDA s) (LMB s B P L0)

/-- The general-pass bound (`t2 ≤ P + 1`, `j ≤ P + 1`, bodies `≤ BDA`). -/
def KT (s B P L0 : ℕ) : ℕ :=
  (P + 1) * ((BDA s + 1) * ((B + 2 * P + 8) * (2 * (2 * B + 4 * P + 10)
      + 2 * (LMB s B P L0 + BDA s * (B + 2 * P + 8)) + 2 * (B + 2 * P + 8) + 26))
    + (4 * (2 * B + 3 * P + 8) + 4 * (P + 1) + 27))
  + (4 * B + 4 * P + 4 * (P + 1) + 12)

/-- A general pass (body `≤ BDA`, `t1 ≤ B + 2`, `t2 ≤ P + 1`, `j ≤ P + 1`, arg `≤ LMB`
with in-pass slack) is at most `KT`. -/
theorem tri_pass_le (s B P L0 : ℕ) (body : List L3Instr) (hlen : body.length ≤ BDA s)
    (t1 t2 j Lout : ℕ) (ht1 : t1 ≤ B + 2) (ht2 : t2 ≤ P + 1) (hj : j ≤ P + 1)
    (hL : Lout + (P + 2) * (BDA s * (B + 2 * P + 8)) ≤ LMB s B P L0) :
    pairTClock body B P (P + 2) (B + 2) (P + 2) (P + 2) t1 t2 j Lout
      ≤ KT s B P L0 := by
  have hLk : ∀ k, k < j → Lout + (loop3OutN body t1 t2 k).length ≤ LMB s B P L0 := by
    intro k hk
    have h1 := CookLevinEmitClockBounds.loop3OutN_length_le body t1 t2 k
    have h2 : k * (body.length * (t1 + t2 + k + 1))
        ≤ (P + 2) * (BDA s * (B + 2 * P + 8)) := by
      apply Nat.mul_le_mul (by omega)
      apply Nat.mul_le_mul hlen
      omega
    omega
  have h := pairTClock_le body B P (P + 2) (B + 2) (P + 2) (P + 2) t1 t2 j Lout
    (LMB s B P L0) hLk
  have hin : (t1 + t2 + j + 2) * (2 * (B + P + (P + 2) + (B + 2) + (P + 2) + (P + 2))
      + 2 * (LMB s B P L0 + body.length * (t1 + t2 + j + 1)) + 2 * (t1 + t2 + j) + 26)
      ≤ (B + 2 * P + 8) * (2 * (2 * B + 4 * P + 10)
        + 2 * (LMB s B P L0 + BDA s * (B + 2 * P + 8)) + 2 * (B + 2 * P + 8) + 26) := by
    apply Nat.mul_le_mul (by omega)
    have := Nat.mul_le_mul hlen (show t1 + t2 + j + 1 ≤ B + 2 * P + 8 by omega)
    omega
  have hout : (body.length + 1) * ((t1 + t2 + j + 2)
      * (2 * (B + P + (P + 2) + (B + 2) + (P + 2) + (P + 2))
        + 2 * (LMB s B P L0 + body.length * (t1 + t2 + j + 1)) + 2 * (t1 + t2 + j) + 26))
      ≤ (BDA s + 1) * ((B + 2 * P + 8) * (2 * (2 * B + 4 * P + 10)
        + 2 * (LMB s B P L0 + BDA s * (B + 2 * P + 8)) + 2 * (B + 2 * P + 8) + 26)) :=
    Nat.mul_le_mul (by omega) hin
  have hj2 : j * ((body.length + 1) * ((t1 + t2 + j + 2)
      * (2 * (B + P + (P + 2) + (B + 2) + (P + 2) + (P + 2))
        + 2 * (LMB s B P L0 + body.length * (t1 + t2 + j + 1)) + 2 * (t1 + t2 + j) + 26))
      + (4 * (B + P + (P + 2) + (B + 2) + (P + 2)) + 4 * j + 27))
      ≤ (P + 1) * ((BDA s + 1) * ((B + 2 * P + 8) * (2 * (2 * B + 4 * P + 10)
        + 2 * (LMB s B P L0 + BDA s * (B + 2 * P + 8)) + 2 * (B + 2 * P + 8) + 26))
        + (4 * (2 * B + 3 * P + 8) + 4 * (P + 1) + 27)) :=
    Nat.mul_le_mul hj (by omega)
  rw [KT]
  omega

/-! ## Stream helpers -/

theorem qcPassOut_mono {Q Q' BD t t' : ℕ} (hQ : Q ≤ Q') (ht : t ≤ t') :
    qcPassOut Q BD t ≤ qcPassOut Q' BD t' := by
  rw [qcPassOut, qcPassOut]
  exact Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (by omega))

theorem cellE_le (B P T : ℕ) (hT : T ≤ B) :
    (cellEmitOut P T).length ≤ B * ((P + 1) * (100 * (B + P + 3))) := by
  have h1 := cellEmitOut_length_le P T
  have h2 : T * ((P + 1) * (cellCopyRowBody.length * (T + P + 3)))
      ≤ B * ((P + 1) * (100 * (B + P + 3))) := by
    apply Nat.mul_le_mul hT
    apply Nat.mul_le_mul_left
    exact Nat.mul_le_mul cellCopyRowBody_length_le (by omega)
  omega

theorem qcE_le (bodies : ℕ → List L3Instr) (card' BD B Q T : ℕ)
    (hbd : ∀ q, q < card' → (bodies q).length ≤ BD) (hT : T ≤ B) :
    (qcEmitOut bodies Q card' T).length ≤ B * (card' * qcPassOut Q BD B) := by
  have h1 := qcEmitOut_length_le bodies Q card' BD hbd T
  have h2 : T * (card' * qcPassOut Q BD T) ≤ B * (card' * qcPassOut Q BD B) :=
    Nat.mul_le_mul hT (Nat.mul_le_mul_left _ (qcPassOut_mono (le_refl _) hT))
  omega

theorem headE_le (B P T : ℕ) (hT : T ≤ B) :
    (headEmitOut P T).length ≤ B * headRoundOut P B := by
  have h1 := headEmitOut_length_le P T
  have h2 : T * headRoundOut P T ≤ B * headRoundOut P B :=
    Nat.mul_le_mul hT (headRoundOut_mono P hT)
  omega

theorem triR_le (B P t r : ℕ) (ht : t ≤ B + 2) (hr : r ≤ P) :
    (triRowOut amoPairRowHeadBody t r).length
      ≤ P * (P * (100 * (B + 2 * P + 8))) := by
  have h1 := triRowOut_length_le amoPairRowHeadBody t r
  have h2 : r * (r * (amoPairRowHeadBody.length * (t + 2 * r + 3)))
      ≤ P * (P * (100 * (B + 2 * P + 8))) := by
    apply Nat.mul_le_mul hr
    apply Nat.mul_le_mul hr
    exact Nat.mul_le_mul amoPairRowHeadBody_length_le (by omega)
  omega

/-! ## The head-round core -/

/-- The head-round bound (the six pieces before the closer, over an abstract prefix `X`). -/
def KHC (s B P L0 : ℕ) : ℕ :=
  (P * (2 * B + 2 * P + 5 + (KT s B P L0
      + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (P + 1) + 19)))
    + (4 * B + 4 * P + 8))
  + 2 * KT s B P L0
  + 2 * (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (P + 1) + 18)
  + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (P + 2)
    + 2 * LMB s B P L0 + 24)
  + 5

theorem head_core_le (s B P L0 : ℕ) (X : List Bool) (t : ℕ) (ht : t ≤ B + 2)
    (hX : X.length + (P * (P * (100 * (B + 2 * P + 8)))
      + ((P + 2) + (P + 2) * (BDA s * (B + 2 * P + 8)))) ≤ LMB s B P L0) :
    (((((repPRounds B (fun r =>
          pairTClock amoPairRowHeadBody B P (P + 2) (B + 2) (P + 2) (P + 2) t (r + 1)
              (r + 1) (X ++ triRowOut amoPairRowHeadBody t r).length + 1
            + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (r + 1)
              + 18)) P
        + (4 * B + 4 * P + 8)) + 1
      + pairTClock cntTrueBody B P (P + 2) (B + 2) (P + 2) (P + 2) t (P + 1) (P + 1)
          (X ++ triRowOut amoPairRowHeadBody t P).length) + 1
      + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (P + 1) + 18)) + 1
      + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (P + 2)
        + 2 * ((X ++ triRowOut amoPairRowHeadBody t P)
            ++ List.replicate (P + 1) true).length + 24)) + 1
      + pairTClock aloRowHeadBody B P (P + 2) (B + 2) (P + 2) (P + 2) t (P + 1) (P + 1)
          (((X ++ triRowOut amoPairRowHeadBody t P)
            ++ List.replicate (P + 1) true) ++ [false]).length) + 1
      + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (P + 1) + 18)
      ≤ KHC s B P L0 := by
  have hbudget : ∀ r, r ≤ P →
      (X ++ triRowOut amoPairRowHeadBody t r).length
        + (P + 2) * (BDA s * (B + 2 * P + 8)) ≤ LMB s B P L0 := by
    intro r hr
    rw [List.length_append]
    have := triR_le B P t r ht hr
    omega
  have hRP := repPRounds_le B (fun r =>
      pairTClock amoPairRowHeadBody B P (P + 2) (B + 2) (P + 2) (P + 2) t (r + 1) (r + 1)
          (X ++ triRowOut amoPairRowHeadBody t r).length + 1
        + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (r + 1) + 18))
    (KT s B P L0
      + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (P + 1) + 19))
    P (by
      intro r hr
      simp only []
      have hp := tri_pass_le s B P L0 amoPairRowHeadBody
        (le_trans amoPairRowHeadBody_length_le (lit_le_BDA s)) t (r + 1) (r + 1)
        (X ++ triRowOut amoPairRowHeadBody t r).length ht (by omega) (by omega)
        (hbudget r (by omega))
      omega)
  have hCNT := tri_pass_le s B P L0 cntTrueBody
    (le_trans cntTrueBody_length_le (lit_le_BDA s)) t (P + 1) (P + 1)
    (X ++ triRowOut amoPairRowHeadBody t P).length ht (le_refl _) (le_refl _)
    (hbudget P (le_refl _))
  have hALO := tri_pass_le s B P L0 aloRowHeadBody
    (le_trans aloRowHeadBody_length_le (lit_le_BDA s)) t (P + 1) (P + 1)
    (((X ++ triRowOut amoPairRowHeadBody t P) ++ List.replicate (P + 1) true)
      ++ [false]).length ht (le_refl _) (le_refl _) (by
      simp only [List.length_append, List.length_replicate, List.length_cons,
        List.length_nil]
      have := triR_le B P t P ht (le_refl _)
      omega)
  have hSN : ((X ++ triRowOut amoPairRowHeadBody t P)
      ++ List.replicate (P + 1) true).length ≤ LMB s B P L0 := by
    simp only [List.length_append, List.length_replicate]
    have := triR_le B P t P ht (le_refl _)
    omega
  rw [KHC]
  omega

/-! ## THE MASTER CLOCK BOUND -/

/-- The accept block's length, via the accept-body emission equation. -/
theorem acceptBlock_len_le (M : Machine) (B : ℕ) :
    (((acceptFormula M B).map encodeClause').flatten).length
      ≤ BDA (Fintype.card M.State) * (B + 1) := by
  have h0 : ((acceptFormula M B).map encodeClause').flatten
      = encodeClause' (CookLevinCNFEncode.atLeastOne ((acceptStates M).map (fun q => stateVar B q.val))) := by
    rw [acceptFormula]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil]
  have h0' : (((acceptFormula M B).map encodeClause').flatten).length
      = (encodeClause' (CookLevinCNFEncode.atLeastOne
        ((acceptStates M).map (fun q => stateVar B q.val)))).length := by rw [h0]
  have h1 : (encodeClause' (CookLevinCNFEncode.atLeastOne
        ((acceptStates M).map (fun q => stateVar B q.val)))).length
      = (prog3Out (acceptBody M) B 0 0).length := by
    rw [accept_prog3Out]
  have h2 := prog3Out_length_le (acceptBody M) B 0 0
  have h3 := acceptBody_le_BDA M
  have h4 : (acceptBody M).length * (B + 0 + 0 + 1)
      ≤ BDA (Fintype.card M.State) * (B + 1) := Nat.mul_le_mul h3 (by omega)
  omega

/-- The `qc`-pass bound at bound `1` (`Q := 0`). -/
def KQ0 (s B P L0 : ℕ) : ℕ :=
  qcPassBound B P (P + 2) (B + 2) (P + 2) (P + 2) (B + 2) 0 (BDA s) (LMB s B P L0)

/-- One uniform bound dominating every piece's round. -/
def KALL (s B P L0 : ℕ) : ℕ :=
  (s + 2) * (KQ s B P L0 + KQ0 s B P L0 + KHC s B P L0 + KT s B P L0 + LMB s B P L0
    + 20 * B + 30 * P + 300)

/-- The explicit master-clock majorant. -/
def MCB (s B P L0 : ℕ) : ℕ :=
  17 * (B * (2 * B + 3 + KALL s B P L0) + (4 * B + 4) + KALL s B P L0) + 16

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 8192 in
/-- **THE MASTER CLOCK IS BOUNDED** at the concrete sizes by the explicit majorant. -/
theorem masterClock2_le (M : Machine) (B P L0 : ℕ) (out : List Bool)
    (hout : out.length ≤ L0) :
    masterClock2 M B P (P + 2) (B + 2) (P + 2) (P + 2) out
      ≤ MCB (Fintype.card M.State) B P L0 := by
  unfold masterClock2
  extract_lets O1 O2 O3 O4 O5 O6 O7 O8 O9 rc cCell cWrite cDynA cOne cHead cState
    cDynB cStTop cHdTop cAcc cIC
  have hSUM : KQ (Fintype.card M.State) B P L0 + KQ0 (Fintype.card M.State) B P L0
      + KHC (Fintype.card M.State) B P L0 + KT (Fintype.card M.State) B P L0
      + LMB (Fintype.card M.State) B P L0 + 20 * B + 30 * P + 300
      ≤ KALL (Fintype.card M.State) B P L0 := by
    rw [KALL]
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hLMB : LMB (Fintype.card M.State) B P L0
      = L0 + B * ((P + 1) * (100 * (B + P + 3)))
        + B * (Fintype.card M.State * qcPassOut P (BDA (Fintype.card M.State)) B)
        + B * (Fintype.card M.State * qcPassOut P (BDA (Fintype.card M.State)) B)
        + B * headRoundOut P B
        + B * ((Fintype.card M.State + 1) * qcPassOut 0 (BDA (Fintype.card M.State)) B)
        + B * (Fintype.card M.State * qcPassOut 0 (BDA (Fintype.card M.State)) B)
        + 2 * headRoundOut P B
        + (Fintype.card M.State + 1) * qcPassOut 0 (BDA (Fintype.card M.State)) B
        + (Fintype.card M.State + 2)
            * qcPassOut P (BDA (Fintype.card M.State)) (B + 2)
        + P * (P * (100 * (B + 2 * P + 8)))
        + (P + 1) * (100 * (B + 2 * P + 8))
        + (P + 2) * (BDA (Fintype.card M.State) * (B + 2 * P + 8))
        + (P + 2)
        + 1000 := rfl
  have hqmono : ∀ Q t, Q ≤ P → t ≤ B + 2 →
      qcPassOut Q (BDA (Fintype.card M.State)) t
        ≤ qcPassOut P (BDA (Fintype.card M.State)) (B + 2) :=
    fun Q t hQ ht => qcPassOut_mono hQ ht
  -- accumulated stream lengths
  have hlen1 : O1.length ≤ L0 + B * ((P + 1) * (100 * (B + P + 3))) := by
    simp only [O1]
    rw [List.length_append]
    have := cellE_le B P B (le_refl _)
    omega
  have hlen2 : O2.length ≤ L0 + B * ((P + 1) * (100 * (B + P + 3)))
      + B * (Fintype.card M.State * qcPassOut P (BDA (Fintype.card M.State)) B) := by
    simp only [O2]
    rw [List.length_append]
    have := qcE_le (writeBodies M) (Fintype.card M.State) (BDA (Fintype.card M.State))
      B P B (fun q hq => writeBodies_le_BDA M q hq) (le_refl _)
    omega
  have hlen3 : O3.length ≤ L0 + B * ((P + 1) * (100 * (B + P + 3)))
      + B * (Fintype.card M.State * qcPassOut P (BDA (Fintype.card M.State)) B)
      + B * (Fintype.card M.State * qcPassOut P (BDA (Fintype.card M.State)) B) := by
    simp only [O3]
    rw [List.length_append]
    have := qcE_le (dynBodies M) (Fintype.card M.State) (BDA (Fintype.card M.State))
      B P B (fun q hq => dynBodies_le_BDA M q hq) (le_refl _)
    omega
  have hlen4 : O4.length ≤ L0 + B * ((P + 1) * (100 * (B + P + 3)))
      + B * (Fintype.card M.State * qcPassOut P (BDA (Fintype.card M.State)) B)
      + B * (Fintype.card M.State * qcPassOut P (BDA (Fintype.card M.State)) B)
      + B * headRoundOut P B := by
    simp only [O4]
    rw [List.length_append]
    have := headE_le B P B (le_refl _)
    omega
  have hlen5 : O5.length ≤ L0 + B * ((P + 1) * (100 * (B + P + 3)))
      + B * (Fintype.card M.State * qcPassOut P (BDA (Fintype.card M.State)) B)
      + B * (Fintype.card M.State * qcPassOut P (BDA (Fintype.card M.State)) B)
      + B * headRoundOut P B
      + B * ((Fintype.card M.State + 1)
          * qcPassOut 0 (BDA (Fintype.card M.State)) B) := by
    simp only [O5]
    rw [List.length_append]
    have := qcE_le (stBodies M) (Fintype.card M.State + 1) (BDA (Fintype.card M.State))
      B 0 B (fun q hq => stBodies_le_BDA M q hq) (le_refl _)
    omega
  have hlen6 : O6.length ≤ L0 + B * ((P + 1) * (100 * (B + P + 3)))
      + B * (Fintype.card M.State * qcPassOut P (BDA (Fintype.card M.State)) B)
      + B * (Fintype.card M.State * qcPassOut P (BDA (Fintype.card M.State)) B)
      + B * headRoundOut P B
      + B * ((Fintype.card M.State + 1) * qcPassOut 0 (BDA (Fintype.card M.State)) B)
      + B * (Fintype.card M.State * qcPassOut 0 (BDA (Fintype.card M.State)) B) := by
    simp only [O6]
    rw [List.length_append]
    have := qcE_le (leftBodies M) (Fintype.card M.State) (BDA (Fintype.card M.State))
      B 0 B (fun q hq => leftBodies_le_BDA M q hq) (le_refl _)
    omega
  have hlen7 : O7.length ≤ L0 + B * ((P + 1) * (100 * (B + P + 3)))
      + B * (Fintype.card M.State * qcPassOut P (BDA (Fintype.card M.State)) B)
      + B * (Fintype.card M.State * qcPassOut P (BDA (Fintype.card M.State)) B)
      + B * headRoundOut P B
      + B * ((Fintype.card M.State + 1) * qcPassOut 0 (BDA (Fintype.card M.State)) B)
      + B * (Fintype.card M.State * qcPassOut 0 (BDA (Fintype.card M.State)) B)
      + (Fintype.card M.State + 1) * qcPassOut 0 (BDA (Fintype.card M.State)) B := by
    simp only [O7]
    rw [List.length_append, ← stOut_oneHot M B]
    have := qcOut_length_le (stBodies M) B 0 (BDA (Fintype.card M.State))
      (Fintype.card M.State + 1) 0 (fun q _ hq => stBodies_le_BDA M q (by omega))
    omega
  have hlen8 : O8.length ≤ L0 + B * ((P + 1) * (100 * (B + P + 3)))
      + B * (Fintype.card M.State * qcPassOut P (BDA (Fintype.card M.State)) B)
      + B * (Fintype.card M.State * qcPassOut P (BDA (Fintype.card M.State)) B)
      + B * headRoundOut P B
      + B * ((Fintype.card M.State + 1) * qcPassOut 0 (BDA (Fintype.card M.State)) B)
      + B * (Fintype.card M.State * qcPassOut 0 (BDA (Fintype.card M.State)) B)
      + (Fintype.card M.State + 1) * qcPassOut 0 (BDA (Fintype.card M.State)) B
      + (P * (P * (100 * (B + 2 * P + 8))) + (P + 1) * (100 * (B + 2 * P + 8))
        + (P + 2)) := by
    simp only [O8]
    simp only [List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]
    have h1 := triR_le B P B P (by omega) (le_refl _)
    have h2 := CookLevinEmitClockBounds.loop3Out_length_le aloRowHeadBody B (P + 1) (P + 1)
    have h2' : (P + 1) * (aloRowHeadBody.length * (B + (P + 1) + (P + 1) + 1))
        ≤ (P + 1) * (100 * (B + 2 * P + 8)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul aloRowHeadBody_length_le (by omega))
    omega
  have hlen9 : O9.length ≤ L0 + B * ((P + 1) * (100 * (B + P + 3)))
      + B * (Fintype.card M.State * qcPassOut P (BDA (Fintype.card M.State)) B)
      + B * (Fintype.card M.State * qcPassOut P (BDA (Fintype.card M.State)) B)
      + B * headRoundOut P B
      + B * ((Fintype.card M.State + 1) * qcPassOut 0 (BDA (Fintype.card M.State)) B)
      + B * (Fintype.card M.State * qcPassOut 0 (BDA (Fintype.card M.State)) B)
      + (Fintype.card M.State + 1) * qcPassOut 0 (BDA (Fintype.card M.State)) B
      + (P * (P * (100 * (B + 2 * P + 8))) + (P + 1) * (100 * (B + 2 * P + 8))
        + (P + 2))
      + (Fintype.card M.State + 2)
          * qcPassOut P (BDA (Fintype.card M.State)) (B + 2) := by
    simp only [O9]
    rw [List.length_append]
    have hab := acceptBlock_len_le M B
    have hq : qcPassOut P (BDA (Fintype.card M.State)) (B + 2)
        = (P + 1) * (BDA (Fintype.card M.State) * ((B + 2) + P + 3)) := rfl
    have h4 : BDA (Fintype.card M.State) * (B + 1)
        ≤ BDA (Fintype.card M.State) * ((B + 2) + P + 3) :=
      Nat.mul_le_mul_left _ (by omega)
    have h5 : BDA (Fintype.card M.State) * ((B + 2) + P + 3)
        ≤ (P + 1) * (BDA (Fintype.card M.State) * ((B + 2) + P + 3)) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have h6 : qcPassOut P (BDA (Fintype.card M.State)) (B + 2)
        ≤ (Fintype.card M.State + 2)
          * qcPassOut P (BDA (Fintype.card M.State)) (B + 2) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  -- the thirteen pieces
  have hCell : cCell ≤ B * (2 * B + 3 + KALL (Fintype.card M.State) B P L0)
      + (4 * B + 4) := by
    simp only [cCell]
    refine Nat.add_le_add_right (repRounds_le _ _ B (fun t ht => ?_)) (4 * B + 4)
    have hpt := pairTClock_le' cellCopyRowBody (BDA (Fintype.card M.State))
      (le_trans cellCopyRowBody_length_le (lit_le_BDA _)) B P (P + 2) (B + 2) (P + 2)
      (P + 2) t P (out ++ cellEmitOut P t).length
      (LMB (Fintype.card M.State) B P L0) (fun k hk => by
        have h1 := loop3Out_le_passOut cellCopyRowBody (BDA (Fintype.card M.State)) t
          (le_trans cellCopyRowBody_length_le (lit_le_BDA _)) P k (by omega)
        have h2 := hqmono P t (le_refl _) (by omega)
        have h3 : qcPassOut P (BDA (Fintype.card M.State)) (B + 2)
            ≤ (Fintype.card M.State + 2)
              * qcPassOut P (BDA (Fintype.card M.State)) (B + 2) :=
          Nat.le_mul_of_pos_left _ (by omega)
        rw [List.length_append]
        have h4 := cellE_le B P t (by omega)
        omega)
    have hmt := qcPassBound_mono_t B P (P + 2) (B + 2) (P + 2) (P + 2) P
      (BDA (Fintype.card M.State)) (LMB (Fintype.card M.State) B P L0)
      (show t ≤ B + 2 by omega)
    have hKQ : qcPassBound B P (P + 2) (B + 2) (P + 2) (P + 2) (B + 2) P
        (BDA (Fintype.card M.State)) (LMB (Fintype.card M.State) B P L0)
        = KQ (Fintype.card M.State) B P L0 := rfl
    omega
  have hW : cWrite ≤ B * (2 * B + 3 + KALL (Fintype.card M.State) B P L0)
      + (4 * B + 4) := by
    simp only [cWrite]
    refine Nat.add_le_add_right (repRounds_le _ _ B (fun t ht => ?_)) (4 * B + 4)
    have hq := qcClock_le (writeBodies M) B P (P + 2) (B + 2) (P + 2) (P + 2) t
      (BDA (Fintype.card M.State)) (Fintype.card M.State) 0
      (O1 ++ qcEmitOut (writeBodies M) P (Fintype.card M.State) t).length
      (LMB (Fintype.card M.State) B P L0)
      (fun q h1 h2 => writeBodies_le_BDA M q (by omega)) (by
        rw [List.length_append]
        have h1 := qcE_le (writeBodies M) (Fintype.card M.State)
          (BDA (Fintype.card M.State)) B P t
          (fun q hq => writeBodies_le_BDA M q hq) (by omega)
        have h2 := hqmono P t (le_refl _) (by omega)
        have h3 : Fintype.card M.State
            * qcPassOut P (BDA (Fintype.card M.State)) t
            ≤ (Fintype.card M.State + 2)
              * qcPassOut P (BDA (Fintype.card M.State)) (B + 2) :=
          Nat.mul_le_mul (by omega) h2
        omega)
    have hmt := qcPassBound_mono_t B P (P + 2) (B + 2) (P + 2) (P + 2) P
      (BDA (Fintype.card M.State)) (LMB (Fintype.card M.State) B P L0)
      (show t ≤ B + 2 by omega)
    have hKQ : qcPassBound B P (P + 2) (B + 2) (P + 2) (P + 2) (B + 2) P
        (BDA (Fintype.card M.State)) (LMB (Fintype.card M.State) B P L0)
        = KQ (Fintype.card M.State) B P L0 := rfl
    have hml : Fintype.card M.State * (qcPassBound B P (P + 2) (B + 2) (P + 2) (P + 2) t
        P (BDA (Fintype.card M.State)) (LMB (Fintype.card M.State) B P L0)
        + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (P + 1) + 20))
        ≤ Fintype.card M.State * (KQ (Fintype.card M.State) B P L0
          + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (P + 1)
            + 20)) :=
      Nat.mul_le_mul_left _ (by omega)
    have hsm : Fintype.card M.State * (KQ (Fintype.card M.State) B P L0
        + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (P + 1) + 20))
        + (2 * B + 2 * P + 2 * (P + 2) + 2 * t + 12)
        ≤ KALL (Fintype.card M.State) B P L0 := by
      rw [KALL]
      have hin : KQ (Fintype.card M.State) B P L0
          + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (P + 1) + 20)
          ≤ KQ (Fintype.card M.State) B P L0 + KQ0 (Fintype.card M.State) B P L0
            + KHC (Fintype.card M.State) B P L0 + KT (Fintype.card M.State) B P L0
            + LMB (Fintype.card M.State) B P L0 + 20 * B + 30 * P + 300 := by omega
      have h1 := Nat.mul_le_mul (show Fintype.card M.State ≤ Fintype.card M.State + 2
        by omega) hin
      have h2 : 2 * B + 2 * P + 2 * (P + 2) + 2 * t + 12
          ≤ KQ (Fintype.card M.State) B P L0 + KQ0 (Fintype.card M.State) B P L0
            + KHC (Fintype.card M.State) B P L0 + KT (Fintype.card M.State) B P L0
            + LMB (Fintype.card M.State) B P L0 + 20 * B + 30 * P + 300 := by omega
      nlinarith [Nat.zero_le (Fintype.card M.State)]
    omega
  have hDA : cDynA ≤ B * (2 * B + 3 + KALL (Fintype.card M.State) B P L0)
      + (4 * B + 4) := by
    simp only [cDynA]
    refine Nat.add_le_add_right (repRounds_le _ _ B (fun t ht => ?_)) (4 * B + 4)
    have hq := qcClock_le (dynBodies M) B P (P + 2) (B + 2) (P + 2) (P + 2) t
      (BDA (Fintype.card M.State)) (Fintype.card M.State) 0
      (O2 ++ qcEmitOut (dynBodies M) P (Fintype.card M.State) t).length
      (LMB (Fintype.card M.State) B P L0)
      (fun q h1 h2 => dynBodies_le_BDA M q (by omega)) (by
        rw [List.length_append]
        have h1 := qcE_le (dynBodies M) (Fintype.card M.State)
          (BDA (Fintype.card M.State)) B P t
          (fun q hq => dynBodies_le_BDA M q hq) (by omega)
        have h2 := hqmono P t (le_refl _) (by omega)
        have h3 : Fintype.card M.State
            * qcPassOut P (BDA (Fintype.card M.State)) t
            ≤ (Fintype.card M.State + 2)
              * qcPassOut P (BDA (Fintype.card M.State)) (B + 2) :=
          Nat.mul_le_mul (by omega) h2
        omega)
    have hmt := qcPassBound_mono_t B P (P + 2) (B + 2) (P + 2) (P + 2) P
      (BDA (Fintype.card M.State)) (LMB (Fintype.card M.State) B P L0)
      (show t ≤ B + 2 by omega)
    have hKQ : qcPassBound B P (P + 2) (B + 2) (P + 2) (P + 2) (B + 2) P
        (BDA (Fintype.card M.State)) (LMB (Fintype.card M.State) B P L0)
        = KQ (Fintype.card M.State) B P L0 := rfl
    have hml : Fintype.card M.State * (qcPassBound B P (P + 2) (B + 2) (P + 2) (P + 2) t
        P (BDA (Fintype.card M.State)) (LMB (Fintype.card M.State) B P L0)
        + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (P + 1) + 20))
        ≤ Fintype.card M.State * (KQ (Fintype.card M.State) B P L0
          + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (P + 1)
            + 20)) :=
      Nat.mul_le_mul_left _ (by omega)
    have hsm : Fintype.card M.State * (KQ (Fintype.card M.State) B P L0
        + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (P + 1) + 20))
        + (2 * B + 2 * P + 2 * (P + 2) + 2 * t + 12)
        ≤ KALL (Fintype.card M.State) B P L0 := by
      rw [KALL]
      have hin : KQ (Fintype.card M.State) B P L0
          + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (P + 1) + 20)
          ≤ KQ (Fintype.card M.State) B P L0 + KQ0 (Fintype.card M.State) B P L0
            + KHC (Fintype.card M.State) B P L0 + KT (Fintype.card M.State) B P L0
            + LMB (Fintype.card M.State) B P L0 + 20 * B + 30 * P + 300 := by omega
      have h1 := Nat.mul_le_mul (show Fintype.card M.State ≤ Fintype.card M.State + 2
        by omega) hin
      have h2 : 2 * B + 2 * P + 2 * (P + 2) + 2 * t + 12
          ≤ KQ (Fintype.card M.State) B P L0 + KQ0 (Fintype.card M.State) B P L0
            + KHC (Fintype.card M.State) B P L0 + KT (Fintype.card M.State) B P L0
            + LMB (Fintype.card M.State) B P L0 + 20 * B + 30 * P + 300 := by omega
      nlinarith [Nat.zero_le (Fintype.card M.State)]
    omega
  have hHd : cHead ≤ B * (2 * B + 3 + KALL (Fintype.card M.State) B P L0)
      + (4 * B + 4) := by
    simp only [cHead]
    refine Nat.add_le_add_right (repRounds_le _ _ B (fun t ht => ?_)) (4 * B + 4)
    have hc := head_core_le (Fintype.card M.State) B P L0
      (O3 ++ headEmitOut P t) t (by omega) (by
        rw [List.length_append]
        have h1 := headE_le B P t (by omega)
        omega)
    omega
  have hSt : cState ≤ B * (2 * B + 3 + KALL (Fintype.card M.State) B P L0)
      + (4 * B + 4) := by
    simp only [cState]
    refine Nat.add_le_add_right (repRounds_le _ _ B (fun t ht => ?_)) (4 * B + 4)
    have hq := qcClockD_le (stBodies M) B P 0 (P + 2) (B + 2) (P + 2) (P + 2) t
      (BDA (Fintype.card M.State)) (Fintype.card M.State + 1) 0
      (O4 ++ qcEmitOut (stBodies M) 0 (Fintype.card M.State + 1) t).length
      (LMB (Fintype.card M.State) B P L0)
      (fun q h1 h2 => stBodies_le_BDA M q (by omega)) (by
        rw [List.length_append]
        have h1 := qcE_le (stBodies M) (Fintype.card M.State + 1)
          (BDA (Fintype.card M.State)) B 0 t
          (fun q hq => stBodies_le_BDA M q hq) (by omega)
        have h2 := qcPassOut_mono (le_refl 0) (show t ≤ B by omega)
          (BD := BDA (Fintype.card M.State))
        have h3 : (Fintype.card M.State + 1)
            * qcPassOut 0 (BDA (Fintype.card M.State)) t
            ≤ (Fintype.card M.State + 1)
              * qcPassOut 0 (BDA (Fintype.card M.State)) B :=
          Nat.mul_le_mul_left _ h2
        omega)
    have hmt := qcPassBound_mono_t B P (P + 2) (B + 2) (P + 2) (P + 2) 0
      (BDA (Fintype.card M.State)) (LMB (Fintype.card M.State) B P L0)
      (show t ≤ B + 2 by omega)
    have hKQ0 : qcPassBound B P (P + 2) (B + 2) (P + 2) (P + 2) (B + 2) 0
        (BDA (Fintype.card M.State)) (LMB (Fintype.card M.State) B P L0)
        = KQ0 (Fintype.card M.State) B P L0 := rfl
    have hml : (Fintype.card M.State + 1)
        * (qcPassBound B P (P + 2) (B + 2) (P + 2) (P + 2) t
          0 (BDA (Fintype.card M.State)) (LMB (Fintype.card M.State) B P L0)
        + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (0 + 1) + 20))
        ≤ (Fintype.card M.State + 1) * (KQ0 (Fintype.card M.State) B P L0
          + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (0 + 1)
            + 20)) :=
      Nat.mul_le_mul_left _ (by omega)
    have hsm : (Fintype.card M.State + 1) * (KQ0 (Fintype.card M.State) B P L0
        + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (0 + 1) + 20))
        + (2 * B + 2 * P + 2 * (P + 2) + 2 * t + 12)
        ≤ KALL (Fintype.card M.State) B P L0 := by
      rw [KALL]
      have hin : KQ0 (Fintype.card M.State) B P L0
          + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (0 + 1) + 20)
          ≤ KQ (Fintype.card M.State) B P L0 + KQ0 (Fintype.card M.State) B P L0
            + KHC (Fintype.card M.State) B P L0 + KT (Fintype.card M.State) B P L0
            + LMB (Fintype.card M.State) B P L0 + 20 * B + 30 * P + 300 := by omega
      have h1 := Nat.mul_le_mul (show Fintype.card M.State + 1
          ≤ Fintype.card M.State + 2 by omega) hin
      have h2 : 2 * B + 2 * P + 2 * (P + 2) + 2 * t + 12
          ≤ KQ (Fintype.card M.State) B P L0 + KQ0 (Fintype.card M.State) B P L0
            + KHC (Fintype.card M.State) B P L0 + KT (Fintype.card M.State) B P L0
            + LMB (Fintype.card M.State) B P L0 + 20 * B + 30 * P + 300 := by omega
      nlinarith [Nat.zero_le (Fintype.card M.State)]
    omega
  have hDB : cDynB ≤ B * (2 * B + 3 + KALL (Fintype.card M.State) B P L0)
      + (4 * B + 4) := by
    simp only [cDynB]
    refine Nat.add_le_add_right (repRounds_le _ _ B (fun t ht => ?_)) (4 * B + 4)
    have hq := qcClockD_le (leftBodies M) B P 0 (P + 2) (B + 2) (P + 2) (P + 2) t
      (BDA (Fintype.card M.State)) (Fintype.card M.State) 0
      (O5 ++ qcEmitOut (leftBodies M) 0 (Fintype.card M.State) t).length
      (LMB (Fintype.card M.State) B P L0)
      (fun q h1 h2 => leftBodies_le_BDA M q (by omega)) (by
        rw [List.length_append]
        have h1 := qcE_le (leftBodies M) (Fintype.card M.State)
          (BDA (Fintype.card M.State)) B 0 t
          (fun q hq => leftBodies_le_BDA M q hq) (by omega)
        have h2 := qcPassOut_mono (le_refl 0) (show t ≤ B by omega)
          (BD := BDA (Fintype.card M.State))
        have h3 : Fintype.card M.State
            * qcPassOut 0 (BDA (Fintype.card M.State)) t
            ≤ (Fintype.card M.State + 1)
              * qcPassOut 0 (BDA (Fintype.card M.State)) B :=
          Nat.mul_le_mul (by omega) h2
        omega)
    have hmt := qcPassBound_mono_t B P (P + 2) (B + 2) (P + 2) (P + 2) 0
      (BDA (Fintype.card M.State)) (LMB (Fintype.card M.State) B P L0)
      (show t ≤ B + 2 by omega)
    have hKQ0 : qcPassBound B P (P + 2) (B + 2) (P + 2) (P + 2) (B + 2) 0
        (BDA (Fintype.card M.State)) (LMB (Fintype.card M.State) B P L0)
        = KQ0 (Fintype.card M.State) B P L0 := rfl
    have hml : Fintype.card M.State
        * (qcPassBound B P (P + 2) (B + 2) (P + 2) (P + 2) t
          0 (BDA (Fintype.card M.State)) (LMB (Fintype.card M.State) B P L0)
        + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (0 + 1) + 20))
        ≤ Fintype.card M.State * (KQ0 (Fintype.card M.State) B P L0
          + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (0 + 1)
            + 20)) :=
      Nat.mul_le_mul_left _ (by omega)
    have hsm : Fintype.card M.State * (KQ0 (Fintype.card M.State) B P L0
        + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (0 + 1) + 20))
        + (2 * B + 2 * P + 2 * (P + 2) + 2 * t + 12)
        ≤ KALL (Fintype.card M.State) B P L0 := by
      rw [KALL]
      have hin : KQ0 (Fintype.card M.State) B P L0
          + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (0 + 1) + 20)
          ≤ KQ (Fintype.card M.State) B P L0 + KQ0 (Fintype.card M.State) B P L0
            + KHC (Fintype.card M.State) B P L0 + KT (Fintype.card M.State) B P L0
            + LMB (Fintype.card M.State) B P L0 + 20 * B + 30 * P + 300 := by omega
      have h1 := Nat.mul_le_mul (show Fintype.card M.State ≤ Fintype.card M.State + 2
        by omega) hin
      have h2 : 2 * B + 2 * P + 2 * (P + 2) + 2 * t + 12
          ≤ KQ (Fintype.card M.State) B P L0 + KQ0 (Fintype.card M.State) B P L0
            + KHC (Fintype.card M.State) B P L0 + KT (Fintype.card M.State) B P L0
            + LMB (Fintype.card M.State) B P L0 + 20 * B + 30 * P + 300 := by omega
      nlinarith [Nat.zero_le (Fintype.card M.State)]
    omega
  have hStT : cStTop ≤ KALL (Fintype.card M.State) B P L0 := by
    simp only [cStTop]
    have hq := qcnClockD_le (stBodies M) B P 0 (P + 2) (B + 2) (P + 2) (P + 2) B
      (BDA (Fintype.card M.State)) (Fintype.card M.State + 1) 0 O6.length
      (LMB (Fintype.card M.State) B P L0)
      (fun q h1 h2 => stBodies_le_BDA M q (by omega)) (by omega)
    have hmt := qcPassBound_mono_t B P (P + 2) (B + 2) (P + 2) (P + 2) 0
      (BDA (Fintype.card M.State)) (LMB (Fintype.card M.State) B P L0)
      (show B ≤ B + 2 by omega)
    have hKQ0 : qcPassBound B P (P + 2) (B + 2) (P + 2) (P + 2) (B + 2) 0
        (BDA (Fintype.card M.State)) (LMB (Fintype.card M.State) B P L0)
        = KQ0 (Fintype.card M.State) B P L0 := rfl
    have hml : (Fintype.card M.State + 1)
        * (qcPassBound B P (P + 2) (B + 2) (P + 2) (P + 2) B
          0 (BDA (Fintype.card M.State)) (LMB (Fintype.card M.State) B P L0)
        + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (0 + 1) + 20))
        ≤ (Fintype.card M.State + 1) * (KQ0 (Fintype.card M.State) B P L0
          + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (0 + 1)
            + 20)) :=
      Nat.mul_le_mul_left _ (by omega)
    have hsm : (Fintype.card M.State + 1) * (KQ0 (Fintype.card M.State) B P L0
        + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (0 + 1) + 20))
        ≤ KALL (Fintype.card M.State) B P L0 := by
      rw [KALL]
      have hin : KQ0 (Fintype.card M.State) B P L0
          + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (0 + 1) + 20)
          ≤ KQ (Fintype.card M.State) B P L0 + KQ0 (Fintype.card M.State) B P L0
            + KHC (Fintype.card M.State) B P L0 + KT (Fintype.card M.State) B P L0
            + LMB (Fintype.card M.State) B P L0 + 20 * B + 30 * P + 300 := by omega
      have h1 := Nat.mul_le_mul (show Fintype.card M.State + 1
          ≤ Fintype.card M.State + 2 by omega) hin
      exact h1
    omega
  have hHdT : cHdTop ≤ KALL (Fintype.card M.State) B P L0 := by
    simp only [cHdTop]
    have hc := head_core_le (Fintype.card M.State) B P L0 O7 B (by omega) (by omega)
    omega
  have hAc : cAcc ≤ KALL (Fintype.card M.State) B P L0 := by
    simp only [cAcc]
    have hp := tri_pass_le (Fintype.card M.State) B P L0 (acceptBody M)
      (acceptBody_le_BDA M) B (P + 1) 1 O8.length (by omega) (by omega) (by omega)
      (by omega)
    omega
  have hIC : cIC ≤ KALL (Fintype.card M.State) B P L0 := by
    simp only [cIC]
    have hp := tri_pass_le (Fintype.card M.State) B P L0 (initConstBody M)
      (initConstBody_le_BDA M) (B + 1) (P + 1) 1 O9.length (by omega) (by omega)
      (by omega) (by omega)
    omega
  -- final assembly
  have hrc : rc = 2 * B + 2 * P + 2 * (P + 2) + 2 * B + 10 := rfl
  have hcOne : cOne = 2 * B + 2 * P + 2 * (P + 1) + 6 := rfl
  have hMCB : MCB (Fintype.card M.State) B P L0
      = 17 * (B * (2 * B + 3 + KALL (Fintype.card M.State) B P L0) + (4 * B + 4)
        + KALL (Fintype.card M.State) B P L0) + 16 := rfl
  clear_value O1 O2 O3 O4 O5 O6 O7 O8 O9 rc cCell cWrite cDynA cOne cHead cState
    cDynB cStTop cHdTop cAcc cIC
  omega

/-! ## THE FULL OUTPUT LENGTH -/

/-- The init-const block's length, via the init-const emission equation. -/
theorem icBlock_len_le (M : Machine) :
    (encodeClause' [(stateVar 0 (Fintype.equivFin M.State M.start).val, true)]
      ++ encodeClause' [(headVar 0 0, true)]).length
      ≤ BDA (Fintype.card M.State) := by
  have h0 : encodeClause' [(stateVar 0 (Fintype.equivFin M.State M.start).val, true)]
        ++ encodeClause' [(headVar 0 0, true)]
      = prog3Out (initConstBody M) 0 0 0 := (initConst_prog3Out M 0 0 0).symm
  have h0' : (encodeClause' [(stateVar 0 (Fintype.equivFin M.State M.start).val, true)]
        ++ encodeClause' [(headVar 0 0, true)]).length
      = (prog3Out (initConstBody M) 0 0 0).length := by rw [h0]
  have h1 := prog3Out_length_le (initConstBody M) 0 0 0
  have h2 := initConstBody_le_BDA M
  omega

/-- The explicit bound on the full master output stream. -/
def TOTB (s B P : ℕ) : ℕ :=
  B * ((P + 1) * (100 * (B + P + 3)))
    + B * (s * qcPassOut P (BDA s) B)
    + B * (s * qcPassOut P (BDA s) B)
    + B * headRoundOut P B
    + B * ((s + 1) * qcPassOut 0 (BDA s) B)
    + B * (s * qcPassOut 0 (BDA s) B)
    + (s + 1) * qcPassOut 0 (BDA s) B
    + (P * (P * (100 * (B + 2 * P + 8))) + (P + 1) * (100 * (B + 2 * P + 8))
      + (P + 2))
    + BDA (s) * (B + 1)
    + BDA s

/-- **The master output stream is explicitly bounded.** -/
theorem masterOut2_length_le (M : Machine) (B P : ℕ) :
    (masterOut2 M P B).length ≤ TOTB (Fintype.card M.State) B P := by
  rw [masterOut2, TOTB]
  simp only [List.length_append, List.length_replicate, List.length_cons,
    List.length_nil]
  have h1 := cellE_le B P B (le_refl _)
  have h2 := qcE_le (writeBodies M) (Fintype.card M.State) (BDA (Fintype.card M.State))
    B P B (fun q hq => writeBodies_le_BDA M q hq) (le_refl _)
  have h3 := qcE_le (dynBodies M) (Fintype.card M.State) (BDA (Fintype.card M.State))
    B P B (fun q hq => dynBodies_le_BDA M q hq) (le_refl _)
  have h4 := headE_le B P B (le_refl _)
  have h5 := qcE_le (stBodies M) (Fintype.card M.State + 1) (BDA (Fintype.card M.State))
    B 0 B (fun q hq => stBodies_le_BDA M q hq) (le_refl _)
  have h6 := qcE_le (leftBodies M) (Fintype.card M.State) (BDA (Fintype.card M.State))
    B 0 B (fun q hq => leftBodies_le_BDA M q hq) (le_refl _)
  have h7 : (((stateOneHot M B).map encodeClause').flatten).length
      ≤ (Fintype.card M.State + 1) * qcPassOut 0 (BDA (Fintype.card M.State)) B := by
    rw [← stOut_oneHot M B]
    have := qcOut_length_le (stBodies M) B 0 (BDA (Fintype.card M.State))
      (Fintype.card M.State + 1) 0 (fun q _ hq => stBodies_le_BDA M q (by omega))
    omega
  have h8 := triR_le B P B P (by omega) (le_refl _)
  have h9 := CookLevinEmitClockBounds.loop3Out_length_le aloRowHeadBody B (P + 1) (P + 1)
  have h9' : (P + 1) * (aloRowHeadBody.length * (B + (P + 1) + (P + 1) + 1))
      ≤ (P + 1) * (100 * (B + 2 * P + 8)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul aloRowHeadBody_length_le (by omega))
  have h10 := acceptBlock_len_le M B
  have h11 := icBlock_len_le M
  rw [List.length_append] at h11
  omega

/-! ## THE CORE CLOCK MAJORANT -/

/-- The full emitter-core clock majorant: a function of `B` and `P` only. -/
def ECB (s B P : ℕ) : ℕ :=
  MCB s B P ((P + 1) * (P + 10)) + 1
    + (2 * B + 2 * P + 2 * (P + 2) + 2 * (B + 2) + 2 * (P + 2) + 2 * (P + 2)
      + 2 * ((P + 1) * (P + 10) + TOTB s B P) + 24)

/-- **THE EXACT CORE CLOCK IS BOUNDED by the length-only majorant.** -/
theorem coreClock_le (M : Machine) (clock : ℕ → ℕ) (x : List Bool) :
    coreClock M clock x
      ≤ ECB (Fintype.card M.State) (clock x.length) (x.length + clock x.length) := by
  have h1 := masterClock2_le M (clock x.length) (x.length + clock x.length)
    ((x.length + clock x.length + 1) * (x.length + clock x.length + 10))
    (cellStream x (x.length + clock x.length))
    (cellStream_length_le x (x.length + clock x.length))
  have h2 : (cellStream x (x.length + clock x.length)
        ++ masterOut2 M (x.length + clock x.length) (clock x.length)).length
      ≤ (x.length + clock x.length + 1) * (x.length + clock x.length + 10)
        + TOTB (Fintype.card M.State) (clock x.length) (x.length + clock x.length) := by
    rw [List.length_append]
    have h3 := cellStream_length_le x (x.length + clock x.length)
    have h4 := masterOut2_length_le M (clock x.length) (x.length + clock x.length)
    omega
  have hE : ECB (Fintype.card M.State) (clock x.length) (x.length + clock x.length)
      = MCB (Fintype.card M.State) (clock x.length) (x.length + clock x.length)
          ((x.length + clock x.length + 1) * (x.length + clock x.length + 10)) + 1
        + (2 * clock x.length + 2 * (x.length + clock x.length)
          + 2 * (x.length + clock x.length + 2) + 2 * (clock x.length + 2)
          + 2 * (x.length + clock x.length + 2) + 2 * (x.length + clock x.length + 2)
          + 2 * ((x.length + clock x.length + 1) * (x.length + clock x.length + 10)
            + TOTB (Fintype.card M.State) (clock x.length)
                (x.length + clock x.length)) + 24) := rfl
  unfold coreClock
  omega

/-! ## POLYNOMIAL BOUNDEDNESS OF THE MAJORANT -/

theorem PB_qcPassOut {Q BD t : ℕ → ℕ} (hQ : PolyBounded Q) (hBD : PolyBounded BD)
    (ht : PolyBounded t) : PolyBounded (fun n => qcPassOut (Q n) (BD n) (t n)) :=
  PB_mul (PB_add hQ (PB_const 1)) (PB_mul hBD (PB_add (PB_add ht hQ) (PB_const 3)))

theorem PB_headRoundOut {P T : ℕ → ℕ} (hP : PolyBounded P) (hT : PolyBounded T) :
    PolyBounded (fun n => headRoundOut (P n) (T n)) :=
  PB_add (PB_add (PB_add
      (PB_mul hP (PB_mul hP (PB_mul (PB_const amoPairRowHeadBody.length)
        (PB_add (PB_add hT (PB_mul (PB_const 2) hP)) (PB_const 3)))))
      (PB_add hP (PB_const 1)))
      (PB_const 1))
    (PB_mul (PB_add hP (PB_const 1)) (PB_mul (PB_const aloRowHeadBody.length)
      (PB_add (PB_add hT (PB_mul (PB_const 2) hP)) (PB_const 3))))

theorem PB_qcPassBound {SG SR CB C1 C2 NV t Q BD LM : ℕ → ℕ}
    (hSG : PolyBounded SG) (hSR : PolyBounded SR) (hCB : PolyBounded CB)
    (hC1 : PolyBounded C1) (hC2 : PolyBounded C2) (hNV : PolyBounded NV)
    (ht : PolyBounded t) (hQ : PolyBounded Q) (hBD : PolyBounded BD)
    (hLM : PolyBounded LM) :
    PolyBounded (fun n => qcPassBound (SG n) (SR n) (CB n) (C1 n) (C2 n) (NV n)
      (t n) (Q n) (BD n) (LM n)) := by
  have hQ1 : PolyBounded (fun n => Q n + 1) := PB_add hQ (PB_const 1)
  have htQ : PolyBounded (fun n => t n + 1 + (Q n + 1)) :=
    PB_add (PB_add ht (PB_const 1)) hQ1
  have h5 : PolyBounded (fun n => SG n + SR n + CB n + C1 n + C2 n) :=
    PB_add (PB_add (PB_add (PB_add hSG hSR) hCB) hC1) hC2
  exact PB_add
    (PB_mul hQ1
      (PB_add
        (PB_mul (PB_add hBD (PB_const 1))
          (PB_mul (PB_add htQ (PB_const 2))
            (PB_add (PB_add (PB_add
                (PB_mul (PB_const 2) (PB_add h5 hNV))
                (PB_mul (PB_const 2) (PB_add hLM
                  (PB_mul hBD (PB_add htQ (PB_const 1))))))
              (PB_mul (PB_const 2) htQ))
              (PB_const 26))))
        (PB_add (PB_add (PB_mul (PB_const 4) h5) (PB_mul (PB_const 4) hQ1))
          (PB_const 27))))
    (PB_add (PB_add (PB_add (PB_mul (PB_const 4) hSG) (PB_mul (PB_const 4) hSR))
      (PB_mul (PB_const 4) hQ1)) (PB_const 12))

theorem PB_LMB (s : ℕ) {B P L0 : ℕ → ℕ} (hB : PolyBounded B) (hP : PolyBounded P)
    (hL0 : PolyBounded L0) : PolyBounded (fun n => LMB s (B n) (P n) (L0 n)) := by
  have hpassP : PolyBounded (fun n => qcPassOut (P n) (BDA s) (B n)) :=
    PB_qcPassOut hP (PB_const (BDA s)) hB
  have hpass0 : PolyBounded (fun n => qcPassOut 0 (BDA s) (B n)) :=
    PB_qcPassOut (PB_const 0) (PB_const (BDA s)) hB
  have hpassP2 : PolyBounded (fun n => qcPassOut (P n) (BDA s) (B n + 2)) :=
    PB_qcPassOut hP (PB_const (BDA s)) (PB_add hB (PB_const 2))
  have hhro : PolyBounded (fun n => headRoundOut (P n) (B n)) := PB_headRoundOut hP hB
  have hbp8 : PolyBounded (fun n => B n + 2 * P n + 8) :=
    PB_add (PB_add hB (PB_mul (PB_const 2) hP)) (PB_const 8)
  exact PB_add (PB_add (PB_add (PB_add (PB_add (PB_add (PB_add (PB_add (PB_add
    (PB_add (PB_add (PB_add (PB_add (PB_add hL0
    (PB_mul hB (PB_mul (PB_add hP (PB_const 1)) (PB_mul (PB_const 100)
      (PB_add (PB_add hB hP) (PB_const 3))))))
    (PB_mul hB (PB_mul (PB_const s) hpassP)))
    (PB_mul hB (PB_mul (PB_const s) hpassP)))
    (PB_mul hB hhro))
    (PB_mul hB (PB_mul (PB_const (s + 1)) hpass0)))
    (PB_mul hB (PB_mul (PB_const s) hpass0)))
    (PB_mul (PB_const 2) hhro))
    (PB_mul (PB_const (s + 1)) hpass0))
    (PB_mul (PB_const (s + 2)) hpassP2))
    (PB_mul hP (PB_mul hP (PB_mul (PB_const 100) hbp8))))
    (PB_mul (PB_add hP (PB_const 1)) (PB_mul (PB_const 100) hbp8)))
    (PB_mul (PB_add hP (PB_const 2)) (PB_mul (PB_const (BDA s)) hbp8)))
    (PB_add hP (PB_const 2)))
    (PB_const 1000)

theorem PB_KQ (s : ℕ) {B P L0 : ℕ → ℕ} (hB : PolyBounded B) (hP : PolyBounded P)
    (hL0 : PolyBounded L0) : PolyBounded (fun n => KQ s (B n) (P n) (L0 n)) :=
  PB_qcPassBound hB hP (PB_add hP (PB_const 2)) (PB_add hB (PB_const 2))
    (PB_add hP (PB_const 2)) (PB_add hP (PB_const 2)) (PB_add hB (PB_const 2)) hP
    (PB_const (BDA s)) (PB_LMB s hB hP hL0)

theorem PB_KQ0 (s : ℕ) {B P L0 : ℕ → ℕ} (hB : PolyBounded B) (hP : PolyBounded P)
    (hL0 : PolyBounded L0) : PolyBounded (fun n => KQ0 s (B n) (P n) (L0 n)) :=
  PB_qcPassBound hB hP (PB_add hP (PB_const 2)) (PB_add hB (PB_const 2))
    (PB_add hP (PB_const 2)) (PB_add hP (PB_const 2)) (PB_add hB (PB_const 2))
    (PB_const 0) (PB_const (BDA s)) (PB_LMB s hB hP hL0)

theorem PB_KT (s : ℕ) {B P L0 : ℕ → ℕ} (hB : PolyBounded B) (hP : PolyBounded P)
    (hL0 : PolyBounded L0) : PolyBounded (fun n => KT s (B n) (P n) (L0 n)) := by
  have hbp8 : PolyBounded (fun n => B n + 2 * P n + 8) :=
    PB_add (PB_add hB (PB_mul (PB_const 2) hP)) (PB_const 8)
  have hLMBc := PB_LMB s hB hP hL0
  exact PB_add
    (PB_mul (PB_add hP (PB_const 1))
      (PB_add
        (PB_mul (PB_const (BDA s + 1))
          (PB_mul hbp8
            (PB_add (PB_add (PB_add
                (PB_mul (PB_const 2) (PB_add (PB_add (PB_mul (PB_const 2) hB)
                  (PB_mul (PB_const 4) hP)) (PB_const 10)))
                (PB_mul (PB_const 2) (PB_add hLMBc
                  (PB_mul (PB_const (BDA s)) hbp8))))
              (PB_mul (PB_const 2) hbp8))
              (PB_const 26))))
        (PB_add (PB_add
            (PB_mul (PB_const 4) (PB_add (PB_add (PB_mul (PB_const 2) hB)
              (PB_mul (PB_const 3) hP)) (PB_const 8)))
            (PB_mul (PB_const 4) (PB_add hP (PB_const 1))))
          (PB_const 27))))
    (PB_add (PB_add (PB_add (PB_mul (PB_const 4) hB) (PB_mul (PB_const 4) hP))
      (PB_mul (PB_const 4) (PB_add hP (PB_const 1)))) (PB_const 12))

theorem PB_KHC (s : ℕ) {B P L0 : ℕ → ℕ} (hB : PolyBounded B) (hP : PolyBounded P)
    (hL0 : PolyBounded L0) : PolyBounded (fun n => KHC s (B n) (P n) (L0 n)) := by
  have hKTc := PB_KT s hB hP hL0
  have hLMBc := PB_LMB s hB hP hL0
  have hlin19 : PolyBounded (fun n => 2 * B n + 2 * P n + 2 * (P n + 2)
      + 2 * (B n + 2) + 2 * (P n + 2) + 2 * (P n + 1) + 19) :=
    PB_add (PB_add (PB_add (PB_add (PB_add (PB_add (PB_mul (PB_const 2) hB)
      (PB_mul (PB_const 2) hP)) (PB_mul (PB_const 2) (PB_add hP (PB_const 2))))
      (PB_mul (PB_const 2) (PB_add hB (PB_const 2))))
      (PB_mul (PB_const 2) (PB_add hP (PB_const 2))))
      (PB_mul (PB_const 2) (PB_add hP (PB_const 1)))) (PB_const 19)
  have hlin18 : PolyBounded (fun n => 2 * B n + 2 * P n + 2 * (P n + 2)
      + 2 * (B n + 2) + 2 * (P n + 2) + 2 * (P n + 1) + 18) :=
    PB_add (PB_add (PB_add (PB_add (PB_add (PB_add (PB_mul (PB_const 2) hB)
      (PB_mul (PB_const 2) hP)) (PB_mul (PB_const 2) (PB_add hP (PB_const 2))))
      (PB_mul (PB_const 2) (PB_add hB (PB_const 2))))
      (PB_mul (PB_const 2) (PB_add hP (PB_const 2))))
      (PB_mul (PB_const 2) (PB_add hP (PB_const 1)))) (PB_const 18)
  exact PB_add (PB_add (PB_add (PB_add
    (PB_add
      (PB_mul hP (PB_add (PB_add (PB_add (PB_mul (PB_const 2) hB)
          (PB_mul (PB_const 2) hP)) (PB_const 5))
        (PB_add hKTc hlin19)))
      (PB_add (PB_add (PB_mul (PB_const 4) hB) (PB_mul (PB_const 4) hP))
        (PB_const 8)))
    (PB_mul (PB_const 2) hKTc))
    (PB_mul (PB_const 2) hlin18))
    (PB_add (PB_add (PB_add (PB_add (PB_add (PB_add (PB_add
        (PB_mul (PB_const 2) hB) (PB_mul (PB_const 2) hP))
        (PB_mul (PB_const 2) (PB_add hP (PB_const 2))))
        (PB_mul (PB_const 2) (PB_add hB (PB_const 2))))
        (PB_mul (PB_const 2) (PB_add hP (PB_const 2))))
        (PB_mul (PB_const 2) (PB_add hP (PB_const 2))))
        (PB_mul (PB_const 2) hLMBc))
      (PB_const 24)))
    (PB_const 5)

theorem PB_KALL (s : ℕ) {B P L0 : ℕ → ℕ} (hB : PolyBounded B) (hP : PolyBounded P)
    (hL0 : PolyBounded L0) : PolyBounded (fun n => KALL s (B n) (P n) (L0 n)) :=
  PB_mul (PB_const (s + 2))
    (PB_add (PB_add (PB_add (PB_add (PB_add (PB_add (PB_add
        (PB_KQ s hB hP hL0) (PB_KQ0 s hB hP hL0)) (PB_KHC s hB hP hL0))
        (PB_KT s hB hP hL0)) (PB_LMB s hB hP hL0))
        (PB_mul (PB_const 20) hB)) (PB_mul (PB_const 30) hP))
      (PB_const 300))

theorem PB_MCB (s : ℕ) {B P L0 : ℕ → ℕ} (hB : PolyBounded B) (hP : PolyBounded P)
    (hL0 : PolyBounded L0) : PolyBounded (fun n => MCB s (B n) (P n) (L0 n)) := by
  have hKALLc := PB_KALL s hB hP hL0
  exact PB_add
    (PB_mul (PB_const 17)
      (PB_add (PB_add
          (PB_mul hB (PB_add (PB_add (PB_mul (PB_const 2) hB) (PB_const 3)) hKALLc))
          (PB_add (PB_mul (PB_const 4) hB) (PB_const 4)))
        hKALLc))
    (PB_const 16)

theorem PB_TOTB (s : ℕ) {B P : ℕ → ℕ} (hB : PolyBounded B) (hP : PolyBounded P) :
    PolyBounded (fun n => TOTB s (B n) (P n)) := by
  have hpassP : PolyBounded (fun n => qcPassOut (P n) (BDA s) (B n)) :=
    PB_qcPassOut hP (PB_const (BDA s)) hB
  have hpass0 : PolyBounded (fun n => qcPassOut 0 (BDA s) (B n)) :=
    PB_qcPassOut (PB_const 0) (PB_const (BDA s)) hB
  have hhro : PolyBounded (fun n => headRoundOut (P n) (B n)) := PB_headRoundOut hP hB
  have hbp8 : PolyBounded (fun n => B n + 2 * P n + 8) :=
    PB_add (PB_add hB (PB_mul (PB_const 2) hP)) (PB_const 8)
  exact PB_add (PB_add (PB_add (PB_add (PB_add (PB_add (PB_add (PB_add (PB_add
    (PB_mul hB (PB_mul (PB_add hP (PB_const 1)) (PB_mul (PB_const 100)
      (PB_add (PB_add hB hP) (PB_const 3)))))
    (PB_mul hB (PB_mul (PB_const s) hpassP)))
    (PB_mul hB (PB_mul (PB_const s) hpassP)))
    (PB_mul hB hhro))
    (PB_mul hB (PB_mul (PB_const (s + 1)) hpass0)))
    (PB_mul hB (PB_mul (PB_const s) hpass0)))
    (PB_mul (PB_const (s + 1)) hpass0))
    (PB_add (PB_add (PB_mul hP (PB_mul hP (PB_mul (PB_const 100) hbp8)))
      (PB_mul (PB_add hP (PB_const 1)) (PB_mul (PB_const 100) hbp8)))
      (PB_add hP (PB_const 2))))
    (PB_mul (PB_const (BDA s)) (PB_add hB (PB_const 1))))
    (PB_const (BDA s))

theorem PB_ECB (s : ℕ) {B P : ℕ → ℕ} (hB : PolyBounded B) (hP : PolyBounded P) :
    PolyBounded (fun n => ECB s (B n) (P n)) := by
  have hL0' : PolyBounded (fun n => (P n + 1) * (P n + 10)) :=
    PB_mul (PB_add hP (PB_const 1)) (PB_add hP (PB_const 10))
  exact PB_add (PB_add (PB_MCB s hB hP hL0') (PB_const 1))
    (PB_add (PB_add (PB_add (PB_add (PB_add (PB_add (PB_add
        (PB_mul (PB_const 2) hB) (PB_mul (PB_const 2) hP))
        (PB_mul (PB_const 2) (PB_add hP (PB_const 2))))
        (PB_mul (PB_const 2) (PB_add hB (PB_const 2))))
        (PB_mul (PB_const 2) (PB_add hP (PB_const 2))))
        (PB_mul (PB_const 2) (PB_add hP (PB_const 2))))
        (PB_mul (PB_const 2) (PB_add hL0' (PB_TOTB s hB hP))))
      (PB_const 24))

/-! ## THE CLOSER -/

/-- **E6 CLOSED — THE MACHINE-EMITTED COOK–LEVIN REDUCTION, TOTAL AND POLYNOMIALLY
CLOCKED.**  For every machine `M` with a nonempty accept set and every positive
polynomially-bounded clock: there is a polynomially-bounded time bound `T` such that on
EVERY input `x`, the emitter core — one fixed machine — halts within `T |x|` steps on the
armed input encoding, its raw output tape decodes to the emitted reduction formula, and
that formula is satisfiable iff `M` accepts `x` within the clock.  Machine-checked
Cook–Levin emission end to end: reduction computed by a machine in polynomial time,
correctness unconditional. -/
theorem EmitsEmittedT (M : Machine) (clock : ℕ → ℕ) (hAcc : acceptStates M ≠ [])
    (hclk : ∀ n, 0 < clock n) (hpoly : PolyBounded clock) :
    ∃ T : ℕ → ℕ, PolyBounded T ∧ ∀ x : List Bool,
      HaltsBy (emitterCoreMachine M) (encTape clock x) (T x.length)
      ∧ decodeTape (transOut (emitterCoreMachine M) (encTape clock x) (T x.length))
        = emittedReduction M x (clock x.length)
      ∧ (Satisfiable (decodeTape (transOut (emitterCoreMachine M) (encTape clock x)
            (T x.length)))
          ↔ (HaltsBy M x (clock x.length) ∧ decideOut M x (clock x.length) = true)) := by
  refine ⟨fun n => ECB (Fintype.card M.State) (clock n) (n + clock n),
    PB_ECB (Fintype.card M.State) hpoly (PB_add PB_id hpoly), fun x => ?_⟩
  have hT := coreClock_le M clock x
  obtain ⟨hH, hout⟩ := pipeline_at M clock x
    (ECB (Fintype.card M.State) (clock x.length) (x.length + clock x.length))
    (hclk x.length) hT
  refine ⟨hH, ?_, ?_⟩
  · rw [hout]
    exact pipeline_decodes M clock x (hclk x.length) hAcc
  · rw [hout]
    exact pipeline_correct M clock x (hclk x.length) hAcc

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitFinale