import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinRoundInvariant

/-!
# Cook–Levin M1 — the whole-run induction over the counter `v`

`roundInv_round` (CookLevinRoundInvariant) is the iterable per-round step: from a round-start config with `k`
counters and `D` data pairs, one master loop iteration reaches the round-start config for `k-1` counters (and `D-1`
data pairs), with the invariant preserved.  Iterating it `v` times drives the counter from `v` down to `0`.

Because each round also deletes a data pair (`D → D-1`), the per-round step count depends on the *current* data
count, so the total clock is a **sum over rounds** — `clockSum v D = roundClock D + roundClock (D-1) + … `.

`rounds`: from `RoundInv T v D` (`v ≤ D`), after `clockSum v D` steps the master reaches the counter-empty
round-start config (head at `SEP` low `2`) on a tape `T'` that satisfies `RoundInv T' 0 (D-v)` — i.e. `a₀…a_{v-1}`
and all `v` counters have been deleted, leaving `a_v…` at the front of the data region.  The final terminal read
(`tail_read`, the `k=0` done-branch) then produces `a_v`.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinWholeRun

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinMaster
open PallLean.Paper93.DeepMath.PathB.CookLevinMasterRound
open PallLean.Paper93.DeepMath.PathB.CookLevinRendShift
open PallLean.Paper93.DeepMath.PathB.CookLevinRoundInvariant

/-- The master step count of one loop iteration with `D` data pairs (matches `roundInv_round`'s clock). -/
def roundClock (D : ℕ) : ℕ :=
  (2 + 1 + 2 + (8 * (D - 1) + 8) + 1) + ((2 * (D - 1 + 1) + 2) + 1 + 1 + (8 * D + 8) + 1 + (2 * D + 2) + 1)

/-- Total step count of `v` rounds starting from `D` data pairs (each round decrements `D`). -/
def clockSum : ℕ → ℕ → ℕ
  | 0, _ => 0
  | (v + 1), D => roundClock D + clockSum v (D - 1)

/-! ## The `O(v·|x|)` clock bound -/

/-- One round costs `≤ 32(D+1)` steps — linear in the data count (`roundClock D ≈ 20D+22`). -/
theorem roundClock_le (D : ℕ) : roundClock D ≤ 32 * (D + 1) := by
  unfold roundClock; omega

/-- **The polynomial clock bound.**  `v` rounds cost `≤ 32·v·(D+1)` steps — `O(v·D)`.  With `D ≤ |x|` and `v ≤ |x|`
this is `O(|x|²)`; the full run adds the constant terminal `+7`. -/
theorem clockSum_le (v : ℕ) : ∀ D, clockSum v D ≤ 32 * v * (D + 1) := by
  induction v with
  | zero => intro D; simp [clockSum]
  | succ v ih =>
    intro D
    simp only [clockSum]
    have h2 : clockSum v (D - 1) ≤ 32 * v * (D - 1 + 1) := ih (D - 1)
    have h3 : 32 * v * (D - 1 + 1) ≤ 32 * v * (D + 1) := Nat.mul_le_mul (le_refl _) (by omega)
    have h1 : roundClock D ≤ 32 * (D + 1) := roundClock_le D
    calc roundClock D + clockSum v (D - 1)
        ≤ 32 * (D + 1) + 32 * v * (D + 1) := by omega
      _ = 32 * (v + 1) * (D + 1) := by ring

/-- **Quadratic clock bound** for the well-formed case `v ≤ D`: `clockSum v D ≤ 32(D+1)²` — polynomial in the data
count `D` alone (hence in `|x|`), the form the `InP` clock needs. -/
theorem clockSum_le_quad (v D : ℕ) (hv : v ≤ D) : clockSum v D ≤ 32 * (D + 1) * (D + 1) := by
  calc clockSum v D ≤ 32 * v * (D + 1) := clockSum_le v D
    _ ≤ 32 * (D + 1) * (D + 1) := Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (le_refl _)

/-- **Whole-run induction on the counter `v`.**  From a round-start config satisfying `RoundInv T v D` (`v ≤ D`),
`clockSum v D` master steps reach the counter-empty round-start config (head at `SEP` low `2`) on a tape `T'` with
`RoundInv T' 0 (D-v)` — the first `v` data pairs and all `v` counters deleted. -/
theorem rounds (v : ℕ) : ∀ (T : List Bool) (D : ℕ), v ≤ D → RoundInv T v D →
    ∃ T', run masterM (clockSum v D) ⟨(1, 0, false, false), 2 * v + 2, T⟩
        = ⟨(1, 0, false, false), 2, T'⟩ ∧ RoundInv T' 0 (D - v)
        ∧ T'.getD 4 false = T.getD (2 * v + 4 + 2 * v) false := by
  induction v with
  | zero =>
    intro T D _ h
    refine ⟨T, ?_, by simpa using h, by rw [show (2 * 0 + 4 + 2 * 0 : ℕ) = 4 from by norm_num]⟩
    simp [clockSum]
  | succ v ih =>
    intro T D hv h
    obtain ⟨T1, hrun1, hinv1, htrack1⟩ := roundInv_round T (v + 1) D (by omega) (by omega) h
    obtain ⟨T', hrun2, hinv2, htrack2⟩ := ih T1 (D - 1) (by omega) hinv1
    refine ⟨T', ?_, by rw [show D - (v + 1) = D - 1 - v from by omega]; exact hinv2, ?_⟩
    · simp only [clockSum, roundClock]
      rw [run_add, hrun1, show 2 * ((v + 1) - 1) + 2 = 2 * v + 2 from by omega]
      exact hrun2
    · -- track a_v back one round: T'[a₀] = T1[a_v] (IH) = T[a_{v+1}] (round_data_shift)
      rw [htrack2, show (2 * v + 4 + 2 * v : ℕ) = 2 * ((v + 1) - 1) + 4 + 2 * v from by omega]
      exact htrack1 v (by omega)

/-! ## The complete run: `v` rounds then the terminal read -/

/-- **The full `read a_v` run, decoded.**  From a round-start config satisfying `RoundInv T v D` (`v ≤ D`), the
master runs the `v` loop iterations and the terminal counter-empty branch, halting in the `HALT` group with
`accept` equal to `T.getD (2v+4+2v) false` — the low cell of the *input's* `v`-th data pair, i.e. the doubled
assignment bit `a_v`.  The value tracking (`rounds`) folds the `v` per-round data shifts back to the input, so the
accept cell is read off the *original* tape, not the final one.  Total step count `clockSum v D + 7`. -/
theorem wholeRun (v : ℕ) (T : List Bool) (D : ℕ) (hv : v ≤ D) (h : RoundInv T v D) :
    ∃ T', run masterM (clockSum v D + 7) ⟨(1, 0, false, false), 2 * v + 2, T⟩
        = ⟨(9, 0, T.getD (2 * v + 4 + 2 * v) false, false), 4, T'⟩ := by
  obtain ⟨T', hrun, hinv, htrack⟩ := rounds v T D hv h
  refine ⟨T', ?_⟩
  rw [run_add, hrun]
  have ht := tail_read (s := 2) (tape := T') (by omega) (by simpa using hinv.lsent)
  rw [show (2 : ℕ) + 2 = 4 from rfl, htrack] at ht
  exact ht

/-- The full run genuinely halts, with `accept` reading the input's doubled `a_v = T[2v+4+2v]`. -/
theorem wholeRun_halts (v : ℕ) (T : List Bool) (D : ℕ) (hv : v ≤ D) (h : RoundInv T v D) :
    masterM.halt (run masterM (clockSum v D + 7) ⟨(1, 0, false, false), 2 * v + 2, T⟩).st = true
    ∧ masterM.accept (run masterM (clockSum v D + 7) ⟨(1, 0, false, false), 2 * v + 2, T⟩).st
        = T.getD (2 * v + 4 + 2 * v) false := by
  obtain ⟨T', hrun⟩ := wholeRun v T D hv h
  refine ⟨?_, ?_⟩ <;> rw [hrun] <;> rfl

/-- **Decode, stated as the read of the `v`-th assignment bit.**  For a well-formed round-start tape, the accept bit
equals the input's `v`-th data pair value `a_v` (`= T.getD (2v+4+2v) false`).  This closes the machine ⇒ algorithm
gap: the master's answer is exactly the `RoundInv`-encoded assignment's `v`-th entry. -/
theorem accept_eq_av (v : ℕ) (T : List Bool) (D : ℕ) (hv : v ≤ D) (h : RoundInv T v D) :
    masterM.accept (run masterM (clockSum v D + 7) ⟨(1, 0, false, false), 2 * v + 2, T⟩).st
      = T.getD (2 * v + 4 + 2 * v) false :=
  (wholeRun_halts v T D hv h).2

end PallLean.Paper93.DeepMath.PathB.CookLevinWholeRun
