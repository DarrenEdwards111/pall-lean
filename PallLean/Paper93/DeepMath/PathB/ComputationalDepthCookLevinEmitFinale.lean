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

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitFinale
