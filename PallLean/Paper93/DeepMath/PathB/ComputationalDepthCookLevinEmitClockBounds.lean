import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitPipeline

/-!
# Cook–Levin M2 emitter — E6 step 19: PAIRT-LEVEL CLOCK BOUNDS

The foundation of the `coreClock` polynomial majorant: every clock function of the `pairT`
engine bounded by an explicit product form — the splice costs, the per-instruction cost, the
segment sum, the round cost, the full pass clock — plus the output-length bounds
(`prog3Out`/`loop3Out`) and the generic grand/row round sums (`repRounds`/`repPRounds`).
Generous constants throughout: only polynomiality matters.
Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitClockBounds

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRep
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitRepP
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPairT

/-! ## Output-length bounds -/

theorem instr3Out_length_le (a c k : ℕ) (ins : L3Instr) :
    (instr3Out a c k ins).length ≤ a + c + k + 1 := by
  cases ins <;> simp [instr3Out] <;> omega

theorem prog3OutN_length_le (body : List L3Instr) (a c k : ℕ) : ∀ n,
    (prog3OutN body a c k n).length ≤ n * (a + c + k + 1)
  | 0 => by simp [prog3OutN]
  | n + 1 => by
    rw [prog3OutN, List.length_append]
    have h1 := prog3OutN_length_le body a c k n
    have h2 := instr3Out_length_le a c k (body.getD n .spJo)
    have : (n + 1) * (a + c + k + 1) = n * (a + c + k + 1) + (a + c + k + 1) := by ring
    omega

theorem prog3Out_length_le (body : List L3Instr) (a c k : ℕ) :
    (prog3Out body a c k).length ≤ body.length * (a + c + k + 1) :=
  prog3OutN_length_le body a c k body.length

theorem loop3OutN_length_le (body : List L3Instr) (a c : ℕ) : ∀ N,
    (loop3OutN body a c N).length ≤ N * (body.length * (a + c + N + 1))
  | 0 => by simp [loop3OutN]
  | N + 1 => by
    rw [loop3OutN, List.length_append]
    have h1 := loop3OutN_length_le body a c N
    have h2 := prog3Out_length_le body a c N
    have h3 : body.length * (a + c + N + 1) ≤ body.length * (a + c + (N + 1) + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have h4 : N * (body.length * (a + c + N + 1))
        ≤ N * (body.length * (a + c + (N + 1) + 1)) :=
      Nat.mul_le_mul_left _ h3
    have h5 : (N + 1) * (body.length * (a + c + (N + 1) + 1))
        = N * (body.length * (a + c + (N + 1) + 1))
          + body.length * (a + c + (N + 1) + 1) := by ring
    omega

theorem loop3Out_length_le (body : List L3Instr) (a c N : ℕ) :
    (loop3Out body a c N).length ≤ N * (body.length * (a + c + N + 1)) :=
  loop3OutN_length_le body a c N

/-! ## The splice-round sum -/

theorem lp3SpRounds_le (B : ℕ) : ∀ i, lp3SpRounds B i ≤ i * (B + 2 * i)
  | 0 => by simp [lp3SpRounds]
  | i + 1 => by
    rw [lp3SpRounds]
    have h1 := lp3SpRounds_le B i
    have h2 : i * (B + 2 * i) ≤ i * (B + 2 * (i + 1)) :=
      Nat.mul_le_mul_left _ (by omega)
    have h3 : (i + 1) * (B + 2 * (i + 1)) = i * (B + 2 * (i + 1)) + (B + 2 * (i + 1)) := by
      ring
    omega

/-! ## The splice costs

Uniform bound: with `S := G1 + G2 + CB + C1 + C2 + NV` and the spliced value `v`,
each cost is at most `(v + 2) * (2 * S + 2 * L + 2 * v + 26)`. -/

theorem pairTaCost_le (G1 G2 CB C1 C2 NV t1 L : ℕ) :
    pairTaCost G1 G2 CB C1 C2 NV t1 L
      ≤ (t1 + 2) * (2 * (G1 + G2 + CB + C1 + C2 + NV) + 2 * L + 2 * t1 + 26) := by
  rw [pairTaCost]
  have h1 := lp3SpRounds_le
    (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * L + 20) t1
  nlinarith [Nat.zero_le G1, Nat.zero_le G2, Nat.zero_le CB, Nat.zero_le C1,
    Nat.zero_le C2, Nat.zero_le NV, Nat.zero_le t1, Nat.zero_le L]

theorem pairTcCost_le (G1 G2 CB C1 C2 NV t2 L : ℕ) :
    pairTcCost G1 G2 CB C1 C2 NV t2 L
      ≤ (t2 + 2) * (2 * (G1 + G2 + CB + C1 + C2 + NV) + 2 * L + 2 * t2 + 26) := by
  rw [pairTcCost]
  have h1 := lp3SpRounds_le
    (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * L + 22) t2
  nlinarith [Nat.zero_le G1, Nat.zero_le G2, Nat.zero_le CB, Nat.zero_le C1,
    Nat.zero_le C2, Nat.zero_le NV, Nat.zero_le t2, Nat.zero_le L]

theorem pairTjCost_le (G1 G2 CB C1 C2 NV k L : ℕ) :
    pairTjCost G1 G2 CB C1 C2 NV k L
      ≤ (k + 2) * (2 * (G1 + G2 + CB + C1 + C2 + NV) + 2 * L + 2 * k + 26) := by
  rw [pairTjCost]
  have h1 := lp3SpRounds_le
    (2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV + 2 * L + 24) k
  nlinarith [Nat.zero_le G1, Nat.zero_le G2, Nat.zero_le CB, Nat.zero_le C1,
    Nat.zero_le C2, Nat.zero_le NV, Nat.zero_le k, Nat.zero_le L]

/-! ## Instruction, segment, round, pass -/

/-- The uniform per-instruction bound at spliced-value budget `W := t1 + t2 + k` and
output-length budget `L' := L + |body| · (W + 1)`. -/
theorem pairTInstrCost_le (body : List L3Instr) (G1 G2 CB C1 C2 NV t1 t2 k L n : ℕ)
    (hn : n ≤ body.length) :
    pairTInstrCost body G1 G2 CB C1 C2 NV t1 t2 k L n
      ≤ (t1 + t2 + k + 2) * (2 * (G1 + G2 + CB + C1 + C2 + NV)
          + 2 * (L + body.length * (t1 + t2 + k + 1)) + 2 * (t1 + t2 + k) + 26) := by
  have hpl : (prog3OutN body t1 t2 k n).length ≤ body.length * (t1 + t2 + k + 1) :=
    le_trans (prog3OutN_length_le body t1 t2 k n) (Nat.mul_le_mul_right _ hn)
  cases hins : body.getD n .spJo with
  | bit b =>
    simp only [pairTInstrCost, hins]
    have hstep : 2 * G1 + 2 * G2 + 2 * CB + 2 * C1 + 2 * C2 + 2 * NV
        + 2 * (L + (prog3OutN body t1 t2 k n).length) + 19
        ≤ 2 * (G1 + G2 + CB + C1 + C2 + NV)
          + 2 * (L + body.length * (t1 + t2 + k + 1)) + 2 * (t1 + t2 + k) + 26 := by
      omega
    have hmul : 2 * (G1 + G2 + CB + C1 + C2 + NV)
        + 2 * (L + body.length * (t1 + t2 + k + 1)) + 2 * (t1 + t2 + k) + 26
        ≤ (t1 + t2 + k + 2) * (2 * (G1 + G2 + CB + C1 + C2 + NV)
          + 2 * (L + body.length * (t1 + t2 + k + 1)) + 2 * (t1 + t2 + k) + 26) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  | spAo =>
    simp only [pairTInstrCost, hins]
    have h1 := pairTaCost_le G1 G2 CB C1 C2 NV t1
      (L + (prog3OutN body t1 t2 k n).length)
    have h2 : (t1 + 2) * (2 * (G1 + G2 + CB + C1 + C2 + NV)
        + 2 * (L + (prog3OutN body t1 t2 k n).length) + 2 * t1 + 26)
        ≤ (t1 + t2 + k + 2) * (2 * (G1 + G2 + CB + C1 + C2 + NV)
          + 2 * (L + body.length * (t1 + t2 + k + 1)) + 2 * (t1 + t2 + k) + 26) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  | spCo =>
    simp only [pairTInstrCost, hins]
    have h1 := pairTcCost_le G1 G2 CB C1 C2 NV t2
      (L + (prog3OutN body t1 t2 k n).length)
    have h2 : (t2 + 2) * (2 * (G1 + G2 + CB + C1 + C2 + NV)
        + 2 * (L + (prog3OutN body t1 t2 k n).length) + 2 * t2 + 26)
        ≤ (t1 + t2 + k + 2) * (2 * (G1 + G2 + CB + C1 + C2 + NV)
          + 2 * (L + body.length * (t1 + t2 + k + 1)) + 2 * (t1 + t2 + k) + 26) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  | spJo =>
    simp only [pairTInstrCost, hins]
    have h1 := pairTjCost_le G1 G2 CB C1 C2 NV k
      (L + (prog3OutN body t1 t2 k n).length)
    have h2 : (k + 2) * (2 * (G1 + G2 + CB + C1 + C2 + NV)
        + 2 * (L + (prog3OutN body t1 t2 k n).length) + 2 * k + 26)
        ≤ (t1 + t2 + k + 2) * (2 * (G1 + G2 + CB + C1 + C2 + NV)
          + 2 * (L + body.length * (t1 + t2 + k + 1)) + 2 * (t1 + t2 + k) + 26) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega

theorem pairTSegN_le (body : List L3Instr) (G1 G2 CB C1 C2 NV t1 t2 k L : ℕ) : ∀ n,
    n ≤ body.length →
    pairTSegN body G1 G2 CB C1 C2 NV t1 t2 k L n
      ≤ n * ((t1 + t2 + k + 2) * (2 * (G1 + G2 + CB + C1 + C2 + NV)
          + 2 * (L + body.length * (t1 + t2 + k + 1)) + 2 * (t1 + t2 + k) + 26))
  | 0, _ => by simp [pairTSegN]
  | n + 1, hn => by
    rw [pairTSegN]
    have h1 := pairTSegN_le body G1 G2 CB C1 C2 NV t1 t2 k L n (by omega)
    have h2 := pairTInstrCost_le body G1 G2 CB C1 C2 NV t1 t2 k L n (by omega)
    have h3 : (n + 1) * ((t1 + t2 + k + 2) * (2 * (G1 + G2 + CB + C1 + C2 + NV)
        + 2 * (L + body.length * (t1 + t2 + k + 1)) + 2 * (t1 + t2 + k) + 26))
        = n * ((t1 + t2 + k + 2) * (2 * (G1 + G2 + CB + C1 + C2 + NV)
          + 2 * (L + body.length * (t1 + t2 + k + 1)) + 2 * (t1 + t2 + k) + 26))
          + ((t1 + t2 + k + 2) * (2 * (G1 + G2 + CB + C1 + C2 + NV)
          + 2 * (L + body.length * (t1 + t2 + k + 1)) + 2 * (t1 + t2 + k) + 26)) := by
      ring
    omega

theorem pairTRoundCost_le (body : List L3Instr) (G1 G2 CB C1 C2 NV t1 t2 k L : ℕ) :
    pairTRoundCost body G1 G2 CB C1 C2 NV t1 t2 k L
      ≤ (body.length + 1) * ((t1 + t2 + k + 2)
          * (2 * (G1 + G2 + CB + C1 + C2 + NV)
            + 2 * (L + body.length * (t1 + t2 + k + 1)) + 2 * (t1 + t2 + k) + 26))
        + (4 * (G1 + G2 + CB + C1 + C2) + 4 * k + 27) := by
  rw [pairTRoundCost]
  have h1 := pairTSegN_le body G1 G2 CB C1 C2 NV t1 t2 k L body.length (le_refl _)
  have h3 : body.length * ((t1 + t2 + k + 2) * (2 * (G1 + G2 + CB + C1 + C2 + NV)
      + 2 * (L + body.length * (t1 + t2 + k + 1)) + 2 * (t1 + t2 + k) + 26))
      ≤ (body.length + 1) * ((t1 + t2 + k + 2)
        * (2 * (G1 + G2 + CB + C1 + C2 + NV)
          + 2 * (L + body.length * (t1 + t2 + k + 1)) + 2 * (t1 + t2 + k) + 26)) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-! ## The pass clock -/

/-- The uniform per-round bound with all rounds' output budgets majorised by `LM`. -/
theorem pairTClockN_le (body : List L3Instr) (G1 G2 CB C1 C2 NV t1 t2 Lout LM : ℕ) : ∀ j,
    (∀ k, k < j → Lout + (loop3OutN body t1 t2 k).length ≤ LM) →
    pairTClockN body G1 G2 CB C1 C2 NV t1 t2 Lout j
      ≤ j * ((body.length + 1) * ((t1 + t2 + j + 2)
          * (2 * (G1 + G2 + CB + C1 + C2 + NV)
            + 2 * (LM + body.length * (t1 + t2 + j + 1)) + 2 * (t1 + t2 + j) + 26))
        + (4 * (G1 + G2 + CB + C1 + C2) + 4 * j + 27))
  | 0, _ => by simp [pairTClockN]
  | j + 1, hL => by
    rw [pairTClockN]
    have h1 := pairTClockN_le body G1 G2 CB C1 C2 NV t1 t2 Lout LM j
      (fun k hk => hL k (by omega))
    have h2 := pairTRoundCost_le body G1 G2 CB C1 C2 NV t1 t2 j
      (Lout + (loop3OutN body t1 t2 j).length)
    -- monotonicity of the per-round bound in (k := j ↦ j + 1) and (L ↦ LM)
    have hmono : (body.length + 1) * ((t1 + t2 + j + 2)
        * (2 * (G1 + G2 + CB + C1 + C2 + NV)
          + 2 * ((Lout + (loop3OutN body t1 t2 j).length)
              + body.length * (t1 + t2 + j + 1)) + 2 * (t1 + t2 + j) + 26))
        + (4 * (G1 + G2 + CB + C1 + C2) + 4 * j + 27)
        ≤ (body.length + 1) * ((t1 + t2 + (j + 1) + 2)
          * (2 * (G1 + G2 + CB + C1 + C2 + NV)
            + 2 * (LM + body.length * (t1 + t2 + (j + 1) + 1))
            + 2 * (t1 + t2 + (j + 1)) + 26))
        + (4 * (G1 + G2 + CB + C1 + C2) + 4 * (j + 1) + 27) := by
      have hLj := hL j (by omega)
      have hin : (t1 + t2 + j + 2) * (2 * (G1 + G2 + CB + C1 + C2 + NV)
          + 2 * ((Lout + (loop3OutN body t1 t2 j).length)
              + body.length * (t1 + t2 + j + 1)) + 2 * (t1 + t2 + j) + 26)
          ≤ (t1 + t2 + (j + 1) + 2) * (2 * (G1 + G2 + CB + C1 + C2 + NV)
            + 2 * (LM + body.length * (t1 + t2 + (j + 1) + 1))
            + 2 * (t1 + t2 + (j + 1)) + 26) := by
        apply Nat.mul_le_mul (by omega)
        have : body.length * (t1 + t2 + j + 1) ≤ body.length * (t1 + t2 + (j + 1) + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        omega
      have := Nat.mul_le_mul_left (body.length + 1) hin
      omega
    have hrec : j * ((body.length + 1) * ((t1 + t2 + j + 2)
        * (2 * (G1 + G2 + CB + C1 + C2 + NV)
          + 2 * (LM + body.length * (t1 + t2 + j + 1)) + 2 * (t1 + t2 + j) + 26))
        + (4 * (G1 + G2 + CB + C1 + C2) + 4 * j + 27))
        ≤ j * ((body.length + 1) * ((t1 + t2 + (j + 1) + 2)
          * (2 * (G1 + G2 + CB + C1 + C2 + NV)
            + 2 * (LM + body.length * (t1 + t2 + (j + 1) + 1))
            + 2 * (t1 + t2 + (j + 1)) + 26))
        + (4 * (G1 + G2 + CB + C1 + C2) + 4 * (j + 1) + 27)) := by
      apply Nat.mul_le_mul_left
      have hin : (t1 + t2 + j + 2) * (2 * (G1 + G2 + CB + C1 + C2 + NV)
          + 2 * (LM + body.length * (t1 + t2 + j + 1)) + 2 * (t1 + t2 + j) + 26)
          ≤ (t1 + t2 + (j + 1) + 2) * (2 * (G1 + G2 + CB + C1 + C2 + NV)
            + 2 * (LM + body.length * (t1 + t2 + (j + 1) + 1))
            + 2 * (t1 + t2 + (j + 1)) + 26) := by
        apply Nat.mul_le_mul (by omega)
        have : body.length * (t1 + t2 + j + 1) ≤ body.length * (t1 + t2 + (j + 1) + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        omega
      have := Nat.mul_le_mul_left (body.length + 1) hin
      omega
    have h4 : (j + 1) * ((body.length + 1) * ((t1 + t2 + (j + 1) + 2)
        * (2 * (G1 + G2 + CB + C1 + C2 + NV)
          + 2 * (LM + body.length * (t1 + t2 + (j + 1) + 1))
          + 2 * (t1 + t2 + (j + 1)) + 26))
        + (4 * (G1 + G2 + CB + C1 + C2) + 4 * (j + 1) + 27))
        = j * ((body.length + 1) * ((t1 + t2 + (j + 1) + 2)
          * (2 * (G1 + G2 + CB + C1 + C2 + NV)
            + 2 * (LM + body.length * (t1 + t2 + (j + 1) + 1))
            + 2 * (t1 + t2 + (j + 1)) + 26))
        + (4 * (G1 + G2 + CB + C1 + C2) + 4 * (j + 1) + 27))
          + ((body.length + 1) * ((t1 + t2 + (j + 1) + 2)
            * (2 * (G1 + G2 + CB + C1 + C2 + NV)
              + 2 * (LM + body.length * (t1 + t2 + (j + 1) + 1))
              + 2 * (t1 + t2 + (j + 1)) + 26))
          + (4 * (G1 + G2 + CB + C1 + C2) + 4 * (j + 1) + 27)) := by
      ring
    omega

/-- **The full pass clock bound**: with all output budgets `≤ LM`. -/
theorem pairTClock_le (body : List L3Instr) (G1 G2 CB C1 C2 NV t1 t2 j Lout LM : ℕ)
    (hL : ∀ k, k < j → Lout + (loop3OutN body t1 t2 k).length ≤ LM) :
    pairTClock body G1 G2 CB C1 C2 NV t1 t2 j Lout
      ≤ j * ((body.length + 1) * ((t1 + t2 + j + 2)
          * (2 * (G1 + G2 + CB + C1 + C2 + NV)
            + 2 * (LM + body.length * (t1 + t2 + j + 1)) + 2 * (t1 + t2 + j) + 26))
        + (4 * (G1 + G2 + CB + C1 + C2) + 4 * j + 27))
        + (4 * G1 + 4 * G2 + 4 * j + 12) := by
  rw [pairTClock]
  have h1 := pairTClockN_le body G1 G2 CB C1 C2 NV t1 t2 Lout LM j hL
  omega

/-! ## The grand and row round sums -/

theorem repRounds_le (clk : ℕ → ℕ) (K : ℕ) : ∀ B, (∀ t, t < B → clk t ≤ K) →
    repRounds clk B ≤ B * (2 * B + 3 + K)
  | 0, _ => by simp [repRounds]
  | B + 1, hclk => by
    rw [repRounds]
    have h1 := repRounds_le clk K B (fun t ht => hclk t (by omega))
    have h2 := hclk B (by omega)
    have h3 : B * (2 * B + 3 + K) ≤ B * (2 * (B + 1) + 3 + K) :=
      Nat.mul_le_mul_left _ (by omega)
    have h4 : (B + 1) * (2 * (B + 1) + 3 + K)
        = B * (2 * (B + 1) + 3 + K) + (2 * (B + 1) + 3 + K) := by ring
    omega

theorem repPRounds_le (G : ℕ) (clk : ℕ → ℕ) (K : ℕ) : ∀ P, (∀ t, t < P → clk t ≤ K) →
    repPRounds G clk P ≤ P * (2 * G + 2 * P + 5 + K)
  | 0, _ => by simp [repPRounds]
  | P + 1, hclk => by
    rw [repPRounds]
    have h1 := repPRounds_le G clk K P (fun t ht => hclk t (by omega))
    have h2 := hclk P (by omega)
    have h3 : P * (2 * G + 2 * P + 5 + K) ≤ P * (2 * G + 2 * (P + 1) + 5 + K) :=
      Nat.mul_le_mul_left _ (by omega)
    have h4 : (P + 1) * (2 * G + 2 * (P + 1) + 5 + K)
        = P * (2 * G + 2 * (P + 1) + 5 + K) + (2 * G + 2 * (P + 1) + 5 + K) := by ring
    omega

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitClockBounds
