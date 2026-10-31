import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityBlockSeqDT

/-!
# Block-DT model, route-2 step [171f]: a CONCRETE m-free depth-3 block parity lower bound

A concrete instantiation of the decoupled capstone `parity_not_altO_block_seq_dt` [171e′] at `d = 1`
(depth `3`): `p = 1/1000`, constant width/depth threshold `w = t = 10`, gate bound `M = 10^6`, and the
explicit decreasing star schedule `490007001, 70001, 10, 10, …`.  All side conditions discharge by
`norm_num`/`omega` (the gap closes strictly: `7·70001 = 490007 < 490007.001 = s₀·p`, and
`7·10 = 70 < 70.001`); the union `2·10^6·(82/999)^10/(1-82/999) < 1/2` is a finite `norm_num` check.

* `parity_not_depth3_block` — every depth-`3` alternating (`AltO 3`), bottom-width-`≤ 10`,
  `BottomClean`, `≤ 10^6`-bottom-gate tower over `n ≥ 490007001` variables, on a base `τ₀` with at least
  `490007001` stars, fails to compute parity.  **No probabilistic or budget hypothesis** — fully
  unconditional, m-free, constant width.

The depth here is fixed (`3`); a general-`d` version needs the geometric schedule `s_i` in closed form
(a `norm_num`-friendly recurrence), a separate brick.  Clean, no `sorry`, no `native_decide`.  AC⁰
ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- The explicit depth-3 star schedule: `490007001, 70001, 10, 10, …`. -/
private def sched3 : ℕ → ℕ := fun i => if i = 0 then 490007001 else if i = 1 then 70001 else 10

/-- **A concrete unconditional m-free depth-3 parity lower bound (constant width 10).**  Every
depth-`3`, width-`≤ 10`, `BottomClean`, `≤ 10^6`-gate alternating tower over `n ≥ 490007001` variables,
on a `≥ 490007001`-star base, disagrees with parity somewhere. -/
theorem parity_not_depth3_block (hn : 490007001 < n)
    (C₀ : Layered n) (τ₀ : Fin n → Option Bool)
    (hC₀ : AltO 3 C₀) (hbw₀ : BottomWidth 10 C₀) (hcl₀ : BottomClean C₀)
    (hcnt₀ : (bottomGates C₀).length ≤ 1000000)
    (hτ₀ : 490007001 ≤ SwitchingCounting.stars τ₀) :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x := by
  haveI : NeZero (10 : ℕ) := ⟨by norm_num⟩
  have hs0 : sched3 0 = 490007001 := rfl
  have hs1 : sched3 1 = 70001 := rfl
  have hs2 : sched3 2 = 10 := rfl
  have hmono : ∀ i, sched3 (i + 1) ≤ sched3 i := by
    intro i
    rcases i with _ | _ | k
    · decide
    · decide
    · show sched3 (k + 3) ≤ sched3 (k + 2)
      have e1 : sched3 (k + 3) = 10 := by
        simp only [sched3]; rw [if_neg (show ¬ (k + 3 = 0) by omega),
          if_neg (show ¬ (k + 3 = 1) by omega)]
      have e2 : sched3 (k + 2) = 10 := by
        simp only [sched3]; rw [if_neg (show ¬ (k + 2 = 0) by omega),
          if_neg (show ¬ (k + 2 = 1) by omega)]
      omega
  have hpos : ∀ i, i ≤ 1 → 2 ≤ sched3 (i + 1) := by
    intro i hi; interval_cases i <;> decide
  have hgap : ∀ i, i ≤ 1 →
      7 * (sched3 (i + 1) : ℚ) < (sched3 i : ℚ) * (1 / 1000) := by
    intro i hi; interval_cases i
    · show 7 * ((sched3 1 : ℕ) : ℚ) < ((sched3 0 : ℕ) : ℚ) * (1 / 1000)
      rw [hs0, hs1]; norm_num
    · show 7 * ((sched3 2 : ℕ) : ℚ) < ((sched3 1 : ℕ) : ℚ) * (1 / 1000)
      rw [hs1, hs2]; norm_num
  refine parity_not_altO_block_seq_dt (p := 1 / 1000) (by norm_num) (by norm_num) (by norm_num)
    sched3 10 (n + 1) 1 1000000 10
    hmono (le_refl 10) (by decide) hpos (by omega) (by norm_num)
    C₀ τ₀ hC₀ hbw₀ hcl₀ hcnt₀ (by show sched3 0 ≤ _; rw [hs0]; exact hτ₀) hgap (by norm_num)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_depth3_block
