import PallLean.Paper93.DeepMath.PathB.ComputationalDepthHennieGeneral

/-!
# The peak lemma, part 1: rightward repeats never halt

This is the load-bearing claim for the excursion-peak bound.  It says: in a blank region (positions
`≥ R` read `false` throughout a halting run), the machine can never be in the *same state at two
times with a strictly larger head*, with the head staying `≥ R` in between.  Such a configuration
would seed an infinite rightward drift — the state cycles while the head marches right forever
through the semi-infinite blank region — so the machine never halts, contradicting the halt.

The proof avoids partial sums.  It carries a clean existential invariant
`∀ k, ∃ r < p, state(t₁+k) = state(t₁+r) ∧ head(t₁+r) ≤ head(t₁+k)`:
the state is always one of the `p` states of the base window `[t₁,t₂)` (periodicity), and the head
never drops below its base value (monotonicity of `moveHead` under the shift, using that no reset
move fires while the head stays `≥ R ≥ 1`).  Evaluated at `k = T - t₁`, the state at the halt time
`T` equals a base state, which is non-halt — contradiction.

`no_rightward_repeat` is exactly what a returning excursion needs ruled out: combined with a
record-position pigeonhole it will give `maxHead ≤ frontier + |State|`.  That pigeonhole step is the
remaining piece; this file lands the drift core.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.  This file proves no SAT lower bound.
-/

namespace PallLean.Paper93.DeepMath.PathB.HennieDrift

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.EmptySpaceHennie (blankNext step_st_blank)

variable {M : Machine}

/-- The head update on reading `false` (companion to `step_st_blank`). -/
theorem step_hd_blank {c : Cfg M} (hnh : M.halt c.st = false)
    (hf : c.tp.getD c.hd false = false) :
    (step M c).hd = moveHead c.hd (M.δ c.st false).2.2 := by
  have h1 : ¬ M.halt c.st = true := by rw [hnh]; simp
  unfold step
  rw [if_neg h1]
  show moveHead c.hd (M.δ c.st (c.tp.getD c.hd false)).2.2 = moveHead c.hd (M.δ c.st false).2.2
  rw [hf]

/-- `moveHead _ 3` (reset) always lands on `0`. -/
theorem moveHead_reset (h : ℕ) : moveHead h 3 = 0 := by simp [moveHead]

/-- `moveHead` is monotone in the head position for any non-reset move. -/
theorem moveHead_mono {a b : ℕ} {m : Move} (hm : m ≠ 3) (hab : a ≤ b) :
    moveHead a m ≤ moveHead b m := by
  fin_cases m <;> simp_all [moveHead]
  all_goals omega

/-- **No rightward repeat in a blank region.**  If positions `≥ R` read `false` throughout a run
that first-halts at `T`, then there is no pair of times `t₁ < t₂ ≤ T` in the same state with a
strictly larger head at `t₂` and the head staying `≥ R` on `[t₁,t₂]`.  Such a pair would drift right
forever and never halt. -/
theorem no_rightward_repeat (c : Cfg M) (R T : ℕ) (hR1 : 1 ≤ R)
    (hhalt : M.halt (run M T c).st = true)
    (hfirst : ∀ j, j < T → M.halt (run M j c).st = false)
    (hblank : ∀ t, R ≤ (run M t c).hd → (run M t c).tp.getD (run M t c).hd false = false)
    (t1 t2 : ℕ) (ht12 : t1 < t2) (ht2T : t2 ≤ T)
    (hst : (run M t1 c).st = (run M t2 c).st)
    (hhd : (run M t1 c).hd < (run M t2 c).hd)
    (hge : ∀ t, t1 ≤ t → t ≤ t2 → R ≤ (run M t c).hd) :
    False := by
  set p := t2 - t1 with hp_def
  have hp : 0 < p := by omega
  have ht1p : t1 + p = t2 := by omega
  -- base facts within [t1, t2): each step is a blank step with a non-reset move
  have hbase : ∀ r, r < p →
      (run M (t1 + r + 1) c).st = blankNext M (run M (t1 + r) c).st ∧
      (run M (t1 + r + 1) c).hd =
        moveHead (run M (t1 + r) c).hd (M.δ (run M (t1 + r) c).st false).2.2 ∧
      (M.δ (run M (t1 + r) c).st false).2.2 ≠ 3 := by
    intro r hr
    have hnh : M.halt (run M (t1 + r) c).st = false := hfirst (t1 + r) (by omega)
    have hgeR : R ≤ (run M (t1 + r) c).hd := hge (t1 + r) (by omega) (by omega)
    have hf : (run M (t1 + r) c).tp.getD (run M (t1 + r) c).hd false = false := hblank (t1 + r) hgeR
    have hst' : (run M (t1 + r + 1) c).st = blankNext M (run M (t1 + r) c).st := by
      rw [run_succ]; exact step_st_blank hnh hf
    have hhd' : (run M (t1 + r + 1) c).hd =
        moveHead (run M (t1 + r) c).hd (M.δ (run M (t1 + r) c).st false).2.2 := by
      rw [run_succ]; exact step_hd_blank hnh hf
    have hm3 : (M.δ (run M (t1 + r) c).st false).2.2 ≠ 3 := by
      intro hm
      have hge2 : R ≤ (run M (t1 + r + 1) c).hd := hge (t1 + r + 1) (by omega) (by omega)
      rw [hhd', hm, moveHead_reset] at hge2
      omega
    exact ⟨hst', hhd', hm3⟩
  -- the existential drift invariant
  have hQ : ∀ k, ∃ r, r < p ∧ (run M (t1 + k) c).st = (run M (t1 + r) c).st ∧
      (run M (t1 + r) c).hd ≤ (run M (t1 + k) c).hd := by
    intro k
    induction k with
    | zero => exact ⟨0, hp, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨r, hrp, ihst, ihhd⟩ := ih
      obtain ⟨hbst, hbhd, hbm3⟩ := hbase r hrp
      have hgeR : R ≤ (run M (t1 + r) c).hd := hge (t1 + r) (by omega) (by omega)
      have hnhk : M.halt (run M (t1 + k) c).st = false := by rw [ihst]; exact hfirst (t1 + r) (by omega)
      have hfk : (run M (t1 + k) c).tp.getD (run M (t1 + k) c).hd false = false :=
        hblank (t1 + k) (le_trans hgeR ihhd)
      have hstk1 : (run M (t1 + k + 1) c).st = blankNext M (run M (t1 + r) c).st := by
        rw [run_succ, step_st_blank hnhk hfk, ihst]
      have hmeq : (M.δ (run M (t1 + k) c).st false).2.2 = (M.δ (run M (t1 + r) c).st false).2.2 := by
        rw [ihst]
      have hhdk1 : (run M (t1 + k + 1) c).hd =
          moveHead (run M (t1 + k) c).hd (M.δ (run M (t1 + r) c).st false).2.2 := by
        rw [run_succ, step_hd_blank hnhk hfk, hmeq]
      by_cases hcase : r + 1 < p
      · refine ⟨r + 1, hcase, ?_, ?_⟩
        · show (run M (t1 + k + 1) c).st = (run M (t1 + r + 1) c).st
          rw [hstk1, hbst]
        · show (run M (t1 + r + 1) c).hd ≤ (run M (t1 + k + 1) c).hd
          rw [hbhd, hhdk1]; exact moveHead_mono hbm3 ihhd
      · have hrp1 : r + 1 = p := by omega
        refine ⟨0, hp, ?_, ?_⟩
        · show (run M (t1 + k + 1) c).st = (run M (t1 + 0) c).st
          rw [hstk1, ← hbst, show t1 + r + 1 = t2 from by omega, Nat.add_zero]; exact hst.symm
        · show (run M (t1 + 0) c).hd ≤ (run M (t1 + k + 1) c).hd
          have h2 : (run M (t1 + r + 1) c).hd ≤ (run M (t1 + k + 1) c).hd := by
            rw [hbhd, hhdk1]; exact moveHead_mono hbm3 ihhd
          have h3 : (run M t2 c).hd ≤ (run M (t1 + k + 1) c).hd := by
            rw [show t2 = t1 + r + 1 from by omega]; exact h2
          rw [Nat.add_zero]; omega
  -- contradiction at the halt time
  obtain ⟨r, hrp, hst_eq, _⟩ := hQ (T - t1)
  rw [show t1 + (T - t1) = T from by omega] at hst_eq
  have hnh : M.halt (run M (t1 + r) c).st = false := hfirst (t1 + r) (by omega)
  rw [← hst_eq, hhalt] at hnh
  exact absurd hnh (by decide)

end PallLean.Paper93.DeepMath.PathB.HennieDrift
