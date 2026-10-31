import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityWidthAwareBlockClean

/-!
# Block-DT model, route-2 step [171a]: the width-aware block bound on the PER-ROUND-threshold engine

The seq (per-round-threshold) twin of [170b].  A constant threshold `s` cannot close the Håstad
budget (at the last round `stars τ` can fall to `s`, so `P[stars ≤ s-1 | extBox τ]` is large); the fix
is a **decreasing** threshold sequence `s i` with `stars τ_i = s i ≫ s (i+1)`, which is what lets the
Chernoff gap `7·s(i+1) < stars τ · p` hold round by round.  Round `i` assumes the *input* count
`s i ≤ stars τ` and pulls a survivor with the *output* count `s (i+1) ≤ stars ρ`, shallowing every
bottom gate below the *output* threshold `s (i+1)` (`ShallowsBlock w F ρ (s (i+1)) C`).

`BottomClean` is threaded as in [170b] (so the m-free survivor [164] applies); the engine is the block
seq engine [166].

* `parity_not_altO_block_width_aware_clean_seq` — the general-`d` block parity bound with a per-round
  threshold sequence, sole structural input the two-threshold clean+width-aware block survivor `hsurv`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **The width-aware general-`d` block parity bound with a per-round threshold sequence.**  With a
decreasing threshold `s` (`hmono`), each below `w` (`hsw`), and the two-threshold clean+width-aware
block survivor `hsurv` (input count `s i`, output count and shallowness `s (i+1)`), a depth-`(d+2)`
alternating width-`≤ w` `BottomClean` tower does not compute parity. -/
theorem parity_not_altO_block_width_aware_clean_seq (s : ℕ → ℕ) (w F d : ℕ)
    (hmono : ∀ i, s (i + 1) ≤ s i) (hsw : ∀ i, s (i + 1) ≤ w) (C₀ : Layered n)
    (τ₀ : Fin n → Option Bool) (hC₀ : AltO (d + 2) C₀) (hbw₀ : BottomWidth w C₀)
    (hcl₀ : BottomClean C₀) (hτ₀ : s 0 ≤ SwitchingCounting.stars τ₀)
    (hsurv : ∀ (i : ℕ) (C : Layered n) (τ : Fin n → Option Bool), BottomWidth w C → BottomClean C →
        s i ≤ SwitchingCounting.stars τ →
        ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ s (i + 1) ≤ SwitchingCounting.stars ρ ∧
          SwitchingCounting.stars ρ < F ∧ ShallowsBlock w F ρ (s (i + 1)) C) :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x := by
  refine recursive_tower_not_parity_surv_seq_block
    (fun i C => (if i ≤ d then AltO (d + 2 - i) C else True) ∧ BottomWidth w C ∧ BottomClean C)
    s C₀ τ₀ ?_ hτ₀ ?_ d w F ?_
  · -- Valid 0 C₀
    refine ⟨?_, hbw₀, hcl₀⟩
    simp only [Nat.zero_le, if_true, Nat.sub_zero]; exact hC₀
  · -- oracle
    intro i C τ hV hsurvτ
    obtain ⟨hP, hbw, hcl⟩ := hV
    by_cases hid : i < d
    · simp only [] at hP; rw [if_pos (le_of_lt hid)] at hP
      obtain ⟨ρ, hext, hge, hltF, hshallow⟩ := hsurv i C τ hbw hcl hsurvτ
      refine ⟨collapseRoundBlock w F ρ C, ρ, hext, hge,
        collapseRoundBlock_EquivOn w F hltF C, ?_, ?_, ?_⟩
      · show (if i + 1 ≤ d then AltO (d + 2 - (i + 1)) (collapseRoundBlock w F ρ C) else True)
        rw [if_pos (show i + 1 ≤ d from hid)]
        have hk : d + 2 - i = (d - 1 - i) + 3 := by omega
        rw [hk] at hP
        have hred := collapseRoundBlock_AltO w F ρ hP
        have hk2 : d + 2 - (i + 1) = (d - 1 - i) + 2 := by omega
        rw [hk2]; exact hred
      · exact BottomWidth_mono (hsw i) (collapseRoundBlock_BottomWidth w F ρ hshallow)
      · exact collapseRoundBlock_BottomClean w F ρ hcl.2
    · refine ⟨C, τ, fun _ _ h => h, le_trans (hmono i) hsurvτ, fun _ _ => rfl, ?_, hbw, hcl⟩
      show (if i + 1 ≤ d then AltO (d + 2 - (i + 1)) C else True)
      rw [if_neg (by omega : ¬ i + 1 ≤ d)]; trivial
  · -- terminal (block), discharged from hsurv at index d
    intro Cd σ hVd _hextσ hsurvσ
    obtain ⟨hPd, hbwd, hcld⟩ := hVd
    simp only [] at hPd
    rw [if_pos (le_refl d), show d + 2 - d = 2 from by omega] at hPd
    obtain ⟨D, rfl⟩ := AltO_two_dnf hPd
    obtain ⟨ρ, hext, hge, hltF, hshallow⟩ := hsurv d (dnf D) σ hbwd hcld hsurvσ
    refine ⟨ρ, D, hext, rfl, hltF, ?_⟩
    have hsh := (hshallow D (by rw [show bottomGates (dnf D) = [D] from rfl]; simp)).1
    exact lt_of_lt_of_le hsh hge

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_altO_block_width_aware_clean_seq
