import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinEmitClockBounds

/-!
# Cook–Levin M2 emitter — E6 step 20: QC-FAMILY CLOCK BOUNDS

The second layer of the `coreClock` majorant: the chain-clock recursions
(`qcClock`/`qcClockD`/`qcnClockD`) bounded at a body-length budget `BD` and an output budget
`LM` — each chain step costs at most `qcPassBound + rearm`, the accumulated output is tracked
by the pass-output bound — plus the chain and grand-loop stream-length bounds
(`qcOut`/`qcEmitOut`).  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinEmitClockBounds2

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitLoopProg3
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitPairT
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitWriteFamily
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitQcPass
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitStateChain
open PallLean.Paper93.DeepMath.PathB.CookLevinEmitClockBounds

/-! ## The pass bound at a body-length budget -/

/-- One chain pass's clock bound: grand `SG`, row `SR`, bound `Q + 1`, `t`-source `t`,
body budget `BD`, output budget `LM`. -/
def qcPassBound (SG SR CB C1 C2 NV t Q BD LM : ℕ) : ℕ :=
  (Q + 1) * ((BD + 1) * ((t + 1 + (Q + 1) + 2)
      * (2 * (SG + SR + CB + C1 + C2 + NV)
        + 2 * (LM + BD * (t + 1 + (Q + 1) + 1)) + 2 * (t + 1 + (Q + 1)) + 26))
    + (4 * (SG + SR + CB + C1 + C2) + 4 * (Q + 1) + 27))
  + (4 * SG + 4 * SR + 4 * (Q + 1) + 12)

/-- `pairTClock` at `t2 := 1`, `j := Q + 1`, body length `≤ BD`: the pass bound. -/
theorem pairTClock_le' (body : List L3Instr) (BD : ℕ) (hbd : body.length ≤ BD)
    (SG SR CB C1 C2 NV t Q Lout LM : ℕ)
    (hL : ∀ k, k < Q + 1 → Lout + (loop3OutN body t 1 k).length ≤ LM) :
    pairTClock body SG SR CB C1 C2 NV t 1 (Q + 1) Lout
      ≤ qcPassBound SG SR CB C1 C2 NV t Q BD LM := by
  have h := pairTClock_le body SG SR CB C1 C2 NV t 1 (Q + 1) Lout LM hL
  have hin : (t + 1 + (Q + 1) + 2) * (2 * (SG + SR + CB + C1 + C2 + NV)
      + 2 * (LM + body.length * (t + 1 + (Q + 1) + 1)) + 2 * (t + 1 + (Q + 1)) + 26)
      ≤ (t + 1 + (Q + 1) + 2) * (2 * (SG + SR + CB + C1 + C2 + NV)
        + 2 * (LM + BD * (t + 1 + (Q + 1) + 1)) + 2 * (t + 1 + (Q + 1)) + 26) := by
    apply Nat.mul_le_mul_left
    have := Nat.mul_le_mul_right (t + 1 + (Q + 1) + 1) hbd
    omega
  have hout : (body.length + 1) * ((t + 1 + (Q + 1) + 2)
      * (2 * (SG + SR + CB + C1 + C2 + NV)
        + 2 * (LM + body.length * (t + 1 + (Q + 1) + 1)) + 2 * (t + 1 + (Q + 1)) + 26))
      ≤ (BD + 1) * ((t + 1 + (Q + 1) + 2) * (2 * (SG + SR + CB + C1 + C2 + NV)
        + 2 * (LM + BD * (t + 1 + (Q + 1) + 1)) + 2 * (t + 1 + (Q + 1)) + 26)) :=
    Nat.mul_le_mul (by omega) hin
  have hmul : (Q + 1) * ((body.length + 1) * ((t + 1 + (Q + 1) + 2)
      * (2 * (SG + SR + CB + C1 + C2 + NV)
        + 2 * (LM + body.length * (t + 1 + (Q + 1) + 1)) + 2 * (t + 1 + (Q + 1)) + 26))
      + (4 * (SG + SR + CB + C1 + C2) + 4 * (Q + 1) + 27))
      ≤ (Q + 1) * ((BD + 1) * ((t + 1 + (Q + 1) + 2)
        * (2 * (SG + SR + CB + C1 + C2 + NV)
          + 2 * (LM + BD * (t + 1 + (Q + 1) + 1)) + 2 * (t + 1 + (Q + 1)) + 26))
      + (4 * (SG + SR + CB + C1 + C2) + 4 * (Q + 1) + 27)) :=
    Nat.mul_le_mul_left _ (by omega)
  rw [qcPassBound]
  omega

/-! ## Stream-length bounds -/

/-- The per-pass output bound. -/
def qcPassOut (Q BD t : ℕ) : ℕ := (Q + 1) * (BD * (t + Q + 3))

theorem loop3Out_le_passOut (body : List L3Instr) (BD t : ℕ) (hbd : body.length ≤ BD)
    (Q : ℕ) : ∀ k, k ≤ Q + 1 → (loop3OutN body t 1 k).length ≤ qcPassOut Q BD t := by
  intro k hk
  have h1 := CookLevinEmitClockBounds.loop3OutN_length_le body t 1 k
  have h2 : k * (body.length * (t + 1 + k + 1)) ≤ (Q + 1) * (BD * (t + Q + 3)) := by
    apply Nat.mul_le_mul hk
    apply Nat.mul_le_mul hbd
    omega
  rw [qcPassOut]
  omega

theorem qcOut_length_le (bodies : ℕ → List L3Instr) (t Q BD : ℕ) : ∀ n q0,
    (∀ q, q0 ≤ q → q < q0 + n → (bodies q).length ≤ BD) →
    (qcOut bodies t Q q0 n).length ≤ n * qcPassOut Q BD t
  | 0, _, _ => by simp [qcOut]
  | n + 1, q0, hbd => by
    have hbd0 : (bodies q0).length ≤ BD := hbd q0 (le_refl _) (by omega)
    rw [show qcOut bodies t Q q0 (n + 1)
        = loop3Out (bodies q0) t 1 (Q + 1) ++ qcOut bodies t Q (q0 + 1) n from rfl,
      List.length_append]
    have h1 := loop3Out_le_passOut (bodies q0) BD t hbd0 Q (Q + 1) (le_refl _)
    have h2 := qcOut_length_le bodies t Q BD n (q0 + 1)
      (fun q ha hb => hbd q (by omega) (by omega))
    have h3 : (n + 1) * qcPassOut Q BD t = n * qcPassOut Q BD t + qcPassOut Q BD t := by
      ring
    exact le_trans (Nat.add_le_add h1 h2) (by omega)

theorem qcEmitOut_length_le (bodies : ℕ → List L3Instr) (Q card BD : ℕ)
    (hbd : ∀ q, q < card → (bodies q).length ≤ BD) : ∀ T,
    (qcEmitOut bodies Q card T).length ≤ T * (card * qcPassOut Q BD T)
  | 0 => by simp [qcEmitOut]
  | T + 1 => by
    rw [show qcEmitOut bodies Q card (T + 1)
        = qcEmitOut bodies Q card T ++ qcOut bodies T Q 0 card from rfl,
      List.length_append]
    have h1 := qcEmitOut_length_le bodies Q card BD hbd T
    have h2 := qcOut_length_le bodies T Q BD card 0
      (fun q ha hb => hbd q (by omega))
    have hmono : qcPassOut Q BD T ≤ qcPassOut Q BD (T + 1) := by
      rw [qcPassOut, qcPassOut]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    have h3 : T * (card * qcPassOut Q BD T) ≤ T * (card * qcPassOut Q BD (T + 1)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hmono)
    have h4 : card * qcPassOut Q BD T ≤ card * qcPassOut Q BD (T + 1) :=
      Nat.mul_le_mul_left _ hmono
    have h5 : (T + 1) * (card * qcPassOut Q BD (T + 1))
        = T * (card * qcPassOut Q BD (T + 1)) + card * qcPassOut Q BD (T + 1) := by ring
    omega

/-! ## The chain-clock bounds -/

/-- The coupled chain clock (`qcClock`, brick 47): each step at most the pass bound plus the
re-arm, the output budget threaded through the chain. -/
theorem qcClock_le (bodies : ℕ → List L3Instr) (B P CB C1 C2 NV t BD : ℕ) :
    ∀ (n q0 L LM : ℕ), (∀ q, q0 ≤ q → q < q0 + n → (bodies q).length ≤ BD) →
    L + n * qcPassOut P BD t ≤ LM →
    qcClock bodies B P CB C1 C2 NV t q0 n L
      ≤ n * (qcPassBound B P CB C1 C2 NV t P BD LM
          + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 20))
        + (2 * B + 2 * P + 2 * CB + 2 * t + 12)
  | 0, q0, L, LM, _, _ => by
    rw [show qcClock bodies B P CB C1 C2 NV t q0 0 L
        = 2 * B + 2 * P + 2 * CB + 2 * t + 12 from rfl]
    omega
  | n + 1, q0, L, LM, hbd, hLM => by
    have hbd0 : (bodies q0).length ≤ BD := hbd q0 (le_refl _) (by omega)
    rw [show qcClock bodies B P CB C1 C2 NV t q0 (n + 1) L
        = (pairTClock (bodies q0) B P CB C1 C2 NV t 1 (P + 1) L + 1
          + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 18)) + 1
          + qcClock bodies B P CB C1 C2 NV t (q0 + 1) n
              (L + (loop3Out (bodies q0) t 1 (P + 1)).length) from rfl]
    have hstep : (n + 1) * qcPassOut P BD t = n * qcPassOut P BD t + qcPassOut P BD t := by
      ring
    have hloop : (loop3Out (bodies q0) t 1 (P + 1)).length ≤ qcPassOut P BD t :=
      loop3Out_le_passOut (bodies q0) BD t hbd0 P (P + 1) (le_refl _)
    have hpt := pairTClock_le' (bodies q0) BD hbd0 B P CB C1 C2 NV t P L LM
      (fun k hk => by
        have := loop3Out_le_passOut (bodies q0) BD t hbd0 P k (by omega)
        omega)
    have hrec := qcClock_le bodies B P CB C1 C2 NV t BD n (q0 + 1)
      (L + (loop3Out (bodies q0) t 1 (P + 1)).length) LM
      (fun q h1 h2 => hbd q (by omega) (by omega)) (by omega)
    have h4 : (n + 1) * (qcPassBound B P CB C1 C2 NV t P BD LM
        + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 20))
        = n * (qcPassBound B P CB C1 C2 NV t P BD LM
          + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 20))
          + (qcPassBound B P CB C1 C2 NV t P BD LM
          + (2 * B + 2 * P + 2 * CB + 2 * C1 + 2 * C2 + 2 * (P + 1) + 20)) := by ring
    omega

/-- The decoupled chain clock (`qcClockD`, brick 50). -/
theorem qcClockD_le (bodies : ℕ → List L3Instr) (G R Q CB C1 C2 NV t BD : ℕ) :
    ∀ (n q0 L LM : ℕ), (∀ q, q0 ≤ q → q < q0 + n → (bodies q).length ≤ BD) →
    L + n * qcPassOut Q BD t ≤ LM →
    qcClockD bodies G R Q CB C1 C2 NV t q0 n L
      ≤ n * (qcPassBound G R CB C1 C2 NV t Q BD LM
          + (2 * G + 2 * R + 2 * CB + 2 * C1 + 2 * C2 + 2 * (Q + 1) + 20))
        + (2 * G + 2 * R + 2 * CB + 2 * t + 12)
  | 0, q0, L, LM, _, _ => by
    rw [show qcClockD bodies G R Q CB C1 C2 NV t q0 0 L
        = 2 * G + 2 * R + 2 * CB + 2 * t + 12 from rfl]
    omega
  | n + 1, q0, L, LM, hbd, hLM => by
    have hbd0 : (bodies q0).length ≤ BD := hbd q0 (le_refl _) (by omega)
    rw [show qcClockD bodies G R Q CB C1 C2 NV t q0 (n + 1) L
        = (pairTClock (bodies q0) G R CB C1 C2 NV t 1 (Q + 1) L + 1
          + (2 * G + 2 * R + 2 * CB + 2 * C1 + 2 * C2 + 2 * (Q + 1) + 18)) + 1
          + qcClockD bodies G R Q CB C1 C2 NV t (q0 + 1) n
              (L + (loop3Out (bodies q0) t 1 (Q + 1)).length) from rfl]
    have hstep : (n + 1) * qcPassOut Q BD t = n * qcPassOut Q BD t + qcPassOut Q BD t := by
      ring
    have hloop : (loop3Out (bodies q0) t 1 (Q + 1)).length ≤ qcPassOut Q BD t :=
      loop3Out_le_passOut (bodies q0) BD t hbd0 Q (Q + 1) (le_refl _)
    have hpt := pairTClock_le' (bodies q0) BD hbd0 G R CB C1 C2 NV t Q L LM
      (fun k hk => by
        have := loop3Out_le_passOut (bodies q0) BD t hbd0 Q k (by omega)
        omega)
    have hrec := qcClockD_le bodies G R Q CB C1 C2 NV t BD n (q0 + 1)
      (L + (loop3Out (bodies q0) t 1 (Q + 1)).length) LM
      (fun q h1 h2 => hbd q (by omega) (by omega)) (by omega)
    have h4 : (n + 1) * (qcPassBound G R CB C1 C2 NV t Q BD LM
        + (2 * G + 2 * R + 2 * CB + 2 * C1 + 2 * C2 + 2 * (Q + 1) + 20))
        = n * (qcPassBound G R CB C1 C2 NV t Q BD LM
          + (2 * G + 2 * R + 2 * CB + 2 * C1 + 2 * C2 + 2 * (Q + 1) + 20))
          + (qcPassBound G R CB C1 C2 NV t Q BD LM
          + (2 * G + 2 * R + 2 * CB + 2 * C1 + 2 * C2 + 2 * (Q + 1) + 20)) := by ring
    omega

/-- The no-bump chain clock (`qcnClockD`, brick 54). -/
theorem qcnClockD_le (bodies : ℕ → List L3Instr) (G R Q CB C1 C2 NV t BD : ℕ) :
    ∀ (n q0 L LM : ℕ), (∀ q, q0 ≤ q → q < q0 + n → (bodies q).length ≤ BD) →
    L + n * qcPassOut Q BD t ≤ LM →
    qcnClockD bodies G R Q CB C1 C2 NV t q0 n L
      ≤ n * (qcPassBound G R CB C1 C2 NV t Q BD LM
          + (2 * G + 2 * R + 2 * CB + 2 * C1 + 2 * C2 + 2 * (Q + 1) + 20))
  | 0, q0, L, LM, _, _ => by
    rw [show qcnClockD bodies G R Q CB C1 C2 NV t q0 0 L = 0 from rfl]
    omega
  | n + 1, q0, L, LM, hbd, hLM => by
    have hbd0 : (bodies q0).length ≤ BD := hbd q0 (le_refl _) (by omega)
    rw [show qcnClockD bodies G R Q CB C1 C2 NV t q0 (n + 1) L
        = (pairTClock (bodies q0) G R CB C1 C2 NV t 1 (Q + 1) L + 1
          + (2 * G + 2 * R + 2 * CB + 2 * C1 + 2 * C2 + 2 * (Q + 1) + 18)) + 1
          + qcnClockD bodies G R Q CB C1 C2 NV t (q0 + 1) n
              (L + (loop3Out (bodies q0) t 1 (Q + 1)).length) from rfl]
    have hstep : (n + 1) * qcPassOut Q BD t = n * qcPassOut Q BD t + qcPassOut Q BD t := by
      ring
    have hloop : (loop3Out (bodies q0) t 1 (Q + 1)).length ≤ qcPassOut Q BD t :=
      loop3Out_le_passOut (bodies q0) BD t hbd0 Q (Q + 1) (le_refl _)
    have hpt := pairTClock_le' (bodies q0) BD hbd0 G R CB C1 C2 NV t Q L LM
      (fun k hk => by
        have := loop3Out_le_passOut (bodies q0) BD t hbd0 Q k (by omega)
        omega)
    have hrec := qcnClockD_le bodies G R Q CB C1 C2 NV t BD n (q0 + 1)
      (L + (loop3Out (bodies q0) t 1 (Q + 1)).length) LM
      (fun q h1 h2 => hbd q (by omega) (by omega)) (by omega)
    have h4 : (n + 1) * (qcPassBound G R CB C1 C2 NV t Q BD LM
        + (2 * G + 2 * R + 2 * CB + 2 * C1 + 2 * C2 + 2 * (Q + 1) + 20))
        = n * (qcPassBound G R CB C1 C2 NV t Q BD LM
          + (2 * G + 2 * R + 2 * CB + 2 * C1 + 2 * C2 + 2 * (Q + 1) + 20))
          + (qcPassBound G R CB C1 C2 NV t Q BD LM
          + (2 * G + 2 * R + 2 * CB + 2 * C1 + 2 * C2 + 2 * (Q + 1) + 20)) := by ring
    omega

end PallLean.Paper93.DeepMath.PathB.CookLevinEmitClockBounds2
