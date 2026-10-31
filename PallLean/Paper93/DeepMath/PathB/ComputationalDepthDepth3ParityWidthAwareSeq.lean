import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RecursiveTowerSeq
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3AltReduce
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRoundBounded

/-!
# Tight switching, step 65: the width-aware capstone on the per-round-threshold engine (branch `razborov-recoverRho-wip`)

The two-threshold oracle: the width-aware capstone (step 59) rebuilt on the per-round-threshold engine (step
64).  Round `i` assumes `s i ≤ stars τ` (the *input* survivor count, controlling the budget) and pulls from
`hsurv` a survivor `ρ` with `s (i+1) ≤ stars ρ` (the *output* count) shallowing every bottom gate below the
*output* threshold `s (i+1)` (`Shallows F ρ (s (i+1)) C`).  The collapse drops one alternation level, stays
`EquivOn`, and the new bottom width is `≤ s (i+1) ≤ w`.  After `d` rounds the bottom `DNF` is shallowed below
`s (d+1) ≤ stars ρ`, the terminal shallowness.  The decreasing threshold (`hmono`) is what lets the budget
hold round by round in the Håstad regime — `stars τ = s i ≫ s (i+1)`.

* `parity_not_altO_width_aware_seq` — the general-`d` parity bound with a per-round threshold sequence.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **The width-aware general-`d` parity bound with a per-round threshold sequence.**  A depth-`(d+2)`
alternating tower of bottom width `≤ w` does not compute parity, given a decreasing threshold sequence `s`
(`hmono`), each below `w` (`hsw`), and the two-threshold per-round survivor `hsurv` (input count `s i`, output
count and shallowness `s (i+1)`). -/
theorem parity_not_altO_width_aware_seq (s : ℕ → ℕ) (w F d : ℕ)
    (hmono : ∀ i, s (i + 1) ≤ s i) (hsw : ∀ i, s (i + 1) ≤ w) (C₀ : Layered n)
    (τ₀ : Fin n → Option Bool) (hC₀ : AltO (d + 2) C₀) (hbw₀ : BottomWidth w C₀)
    (hτ₀ : s 0 ≤ SwitchingCounting.stars τ₀)
    (hsurv : ∀ (i : ℕ) (C : Layered n) (τ : Fin n → Option Bool), BottomWidth w C →
        s i ≤ SwitchingCounting.stars τ →
        ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ s (i + 1) ≤ SwitchingCounting.stars ρ ∧
          SwitchingCounting.stars ρ ≤ F ∧ Shallows F ρ (s (i + 1)) C) :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x := by
  refine recursive_tower_not_parity_surv_seq
    (fun i C => (if i ≤ d then AltO (d + 2 - i) C else True) ∧ BottomWidth w C)
    s C₀ τ₀ ?_ hτ₀ ?_ d F ?_
  · -- Valid 0 C₀
    refine ⟨?_, hbw₀⟩
    simp only [Nat.zero_le, if_true, Nat.sub_zero]; exact hC₀
  · -- oracle
    intro i C τ hV hsurvτ
    obtain ⟨hP, hbw⟩ := hV
    by_cases hid : i < d
    · simp only [] at hP; rw [if_pos (le_of_lt hid)] at hP
      obtain ⟨ρ, hext, hge, hle, hshallow⟩ := hsurv i C τ hbw hsurvτ
      refine ⟨collapseRound F ρ C, ρ, hext, hge, collapseRound_EquivOn F hle C, ?_, ?_⟩
      · show (if i + 1 ≤ d then AltO (d + 2 - (i + 1)) (collapseRound F ρ C) else True)
        rw [if_pos (show i + 1 ≤ d from hid)]
        have hk : d + 2 - i = (d - 1 - i) + 3 := by omega
        rw [hk] at hP
        have hred := collapseRound_AltO F ρ hP
        have hk2 : d + 2 - (i + 1) = (d - 1 - i) + 2 := by omega
        rw [hk2]; exact hred
      · exact BottomWidth_mono (hsw i) (collapseRound_BottomWidth F ρ hshallow)
    · refine ⟨C, τ, fun _ _ h => h, le_trans (hmono i) hsurvτ, fun _ _ => rfl, ?_, hbw⟩
      show (if i + 1 ≤ d then AltO (d + 2 - (i + 1)) C else True)
      rw [if_neg (by omega : ¬ i + 1 ≤ d)]; trivial
  · -- hterm, discharged from hsurv at index d
    intro Cd σ hVd _hextσ hsurvσ
    obtain ⟨hPd, hbwd⟩ := hVd
    simp only [] at hPd
    rw [if_pos (le_refl d), show d + 2 - d = 2 from by omega] at hPd
    obtain ⟨D, rfl⟩ := AltO_two_dnf hPd
    obtain ⟨ρ, hext, hge, hle, hshallow⟩ := hsurv d (dnf D) σ hbwd hsurvσ
    refine ⟨ρ, D, hext, rfl, hle, ?_⟩
    have hsh := (hshallow D (by rw [show bottomGates (dnf D) = [D] from rfl]; simp)).1
    exact lt_of_lt_of_le hsh hge

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_altO_width_aware_seq
