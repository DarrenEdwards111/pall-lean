import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RecursiveTowerSeqBlock
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3AltReduceBlock
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRoundBlockBounded
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityWidthAware

/-!
# Block-DT model, route-2 step [169e]: the width-aware general-`d` parity bound, BLOCK (option (b))

The block twin of `parity_not_altO_width_aware`, and the completion of [169]: with the bottom width
threaded through the tower (`BottomWidth w`), the terminal switching is discharged from the per-round
**block** survivor `hsurv` (`ShallowsBlock`).  Routed through the block engine [166], so every
shallowness is over `canonicalDTree` — **no `canonicalDT ↔ canonicalDTree` depth bridge**.

Each round: `hsurv` gives `ρ` (extending the running subcube, `stars ρ < F`, shallowing every bottom
gate below `s`); `collapseRoundBlock` drops one alternation level (`collapseRoundBlock_AltO`, [169d]),
is `EquivOn` ([169b]), and keeps bottom width `≤ s ≤ w` (`collapseRoundBlock_BottomWidth` [169c] +
`BottomWidth_mono`).  After `d` rounds the tower is a bottom `DNF` of width `≤ w`, so the *same*
`hsurv` shallows it — exactly the block terminal the parity capstone needs.

* `parity_not_altO_block_width_aware` — `AltO (d+2) C₀ ∧ BottomWidth w C₀ ⟹ ∃ x, eval C₀ x ≠ parity x`,
  with the sole structural input the per-round **block** survivor `hsurv` (an instance of the m-free
  conditional survivor [164]).

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **The width-aware general-`d` parity lower bound, block.**  A depth-`(d+2)` alternating tower of
bottom width `≤ w` does not compute parity, given only that every reachable width-`≤ w` tower admits a
**block** survivor shallowing all its bottom gates below `s` (with `s ≤ w`), via `canonicalDTree`. -/
theorem parity_not_altO_block_width_aware (s w F d : ℕ) (hsw : s ≤ w) (C₀ : Layered n)
    (τ₀ : Fin n → Option Bool) (hC₀ : AltO (d + 2) C₀) (hbw₀ : BottomWidth w C₀)
    (hτ₀ : s ≤ SwitchingCounting.stars τ₀)
    (hsurv : ∀ (C : Layered n) (τ : Fin n → Option Bool), BottomWidth w C →
        s ≤ SwitchingCounting.stars τ →
        ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ s ≤ SwitchingCounting.stars ρ ∧
          SwitchingCounting.stars ρ < F ∧ ShallowsBlock w F ρ s C) :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x := by
  refine recursive_tower_not_parity_surv_seq_block
    (fun i C => (if i ≤ d then AltO (d + 2 - i) C else True) ∧ BottomWidth w C)
    (fun _ => s) C₀ τ₀ ?_ hτ₀ ?_ d w F ?_
  · -- Valid 0 C₀
    refine ⟨?_, hbw₀⟩
    simp only [Nat.zero_le, if_true, Nat.sub_zero]; exact hC₀
  · -- oracle
    intro i C τ hV hsurvτ
    obtain ⟨hP, hbw⟩ := hV
    by_cases hid : i < d
    · simp only [] at hP; rw [if_pos (le_of_lt hid)] at hP
      obtain ⟨ρ, hext, hge, hltF, hshallow⟩ := hsurv C τ hbw hsurvτ
      refine ⟨collapseRoundBlock w F ρ C, ρ, hext, hge,
        collapseRoundBlock_EquivOn w F hltF C, ?_, ?_⟩
      · show (if i + 1 ≤ d then AltO (d + 2 - (i + 1)) (collapseRoundBlock w F ρ C) else True)
        rw [if_pos (show i + 1 ≤ d from hid)]
        have hk : d + 2 - i = (d - 1 - i) + 3 := by omega
        rw [hk] at hP
        have hred := collapseRoundBlock_AltO w F ρ hP
        have hk2 : d + 2 - (i + 1) = (d - 1 - i) + 2 := by omega
        rw [hk2]; exact hred
      · exact BottomWidth_mono hsw (collapseRoundBlock_BottomWidth w F ρ hshallow)
    · refine ⟨C, τ, fun _ _ h => h, hsurvτ, fun _ _ => rfl, ?_, hbw⟩
      show (if i + 1 ≤ d then AltO (d + 2 - (i + 1)) C else True)
      rw [if_neg (by omega : ¬ i + 1 ≤ d)]; trivial
  · -- terminal (block), discharged from hsurv at the final bottom DNF
    intro Cd σ hVd _hextσ hsurvσ
    obtain ⟨hPd, hbwd⟩ := hVd
    simp only [] at hPd
    rw [if_pos (le_refl d), show d + 2 - d = 2 from by omega] at hPd
    obtain ⟨D, rfl⟩ := AltO_two_dnf hPd
    obtain ⟨ρ, hext, hge, hltF, hshallow⟩ := hsurv (dnf D) σ hbwd hsurvσ
    refine ⟨ρ, D, hext, rfl, hltF, ?_⟩
    have hsh := (hshallow D (by rw [show bottomGates (dnf D) = [D] from rfl]; simp)).1
    exact lt_of_lt_of_le hsh hge

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_altO_block_width_aware
