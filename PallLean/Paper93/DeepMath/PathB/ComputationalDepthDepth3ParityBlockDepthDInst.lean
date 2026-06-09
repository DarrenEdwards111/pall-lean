import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityBlockSeqDT

/-!
# Block-DT model, route-2 step [171g]: the GENERAL-`d` unconditional m-free block parity bound

The general-`d` instantiation of the decoupled capstone `parity_not_altO_block_seq_dt` [171e′], using
the closed-form **geometric** star schedule `s i = 10 · 7001^(d+1-i)` (ratio `7001`, so the gap closes
strictly: `7001 · p = 7.001 > 7` at `p = 1/1000`).  Constant width/depth `t = w = 10`, gate bound
`M = 10^6`.

* `parity_not_depthd_block` — for every `d`, every depth-`(d+2)` alternating (`AltO (d+2)`),
  bottom-width-`≤ 10`, `BottomClean`, `≤ 10^6`-bottom-gate tower over `n` variables, on a base `τ₀`
  with at least `10 · 7001^(d+1)` stars, fails to compute parity.  **No probabilistic or budget
  hypothesis** — fully unconditional, m-free, constant width, for all depths `d` (the star requirement
  `10·7001^(d+1) ≤ stars τ₀ ≤ n` caps the usable depth at `d = O(log n)`, the classical AC⁰ regime).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **The general-`d` unconditional m-free depth-`(d+2)` parity lower bound (constant width 10).** -/
theorem parity_not_depthd_block (d : ℕ)
    (C₀ : Layered n) (τ₀ : Fin n → Option Bool)
    (hC₀ : AltO (d + 2) C₀) (hbw₀ : BottomWidth 10 C₀) (hcl₀ : BottomClean C₀)
    (hcnt₀ : (bottomGates C₀).length ≤ 1000000)
    (hτ₀ : 10 * 7001 ^ (d + 1) ≤ SwitchingCounting.stars τ₀) :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x := by
  haveI : NeZero (10 : ℕ) := ⟨by norm_num⟩
  set s : ℕ → ℕ := fun i => 10 * 7001 ^ (d + 1 - i) with hs
  have hmono : ∀ i, s (i + 1) ≤ s i := by
    intro i; simp only [hs]; gcongr
    · norm_num
    · omega
  have hpos : ∀ i, i ≤ d → 2 ≤ s (i + 1) := by
    intro i _; simp only [hs]
    calc 2 ≤ 10 * 1 := by norm_num
      _ ≤ 10 * 7001 ^ (d + 1 - (i + 1)) := by gcongr; exact Nat.one_le_pow _ _ (by norm_num)
  have hgap : ∀ i, i ≤ d → 7 * (s (i + 1) : ℚ) < (s i : ℚ) * (1 / 1000) := by
    intro i hi
    simp only [hs]
    have h1 : d + 1 - (i + 1) = d - i := by omega
    have h2 : d + 1 - i = (d - i) + 1 := by omega
    rw [h1, h2]
    push_cast
    have hX : (0 : ℚ) < 7001 ^ (d - i) := by positivity
    rw [pow_succ]
    nlinarith [hX]
  have htsd : (10 : ℕ) ≤ s (d + 1) := by
    simp only [hs]; rw [show d + 1 - (d + 1) = 0 by omega]; norm_num
  have hτ : s 0 ≤ SwitchingCounting.stars τ₀ := by
    simp only [hs]; rw [show d + 1 - 0 = d + 1 by omega]; exact hτ₀
  refine parity_not_altO_block_seq_dt (p := 1 / 1000) (by norm_num) (by norm_num) (by norm_num)
    s 10 (n + 1) d 1000000 10
    hmono (le_refl 10) htsd hpos (by omega) (by norm_num)
    C₀ τ₀ hC₀ hbw₀ hcl₀ hcnt₀ hτ hgap (by norm_num)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_depthd_block
