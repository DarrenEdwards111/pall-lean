import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityWidthAwareBlock
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRoundBlockClean

/-!
# Block-DT model, route-2 step [170b]: the width-aware block bound with `BottomClean` threaded

The clean-tracking refinement of `parity_not_altO_block_width_aware` [169e].  The `Valid` invariant
now also carries `BottomClean` (bottom gates `Consistent` + variable-`Nodup`), threaded by
`collapseRoundBlock_BottomClean` [170a] — self-preserving from the nodup half.  Consequently the
per-round survivor `hsurv` may **assume** the current tower is clean (and width-`≤ w`), which is
exactly what the m-free conditional survivor [164] needs to discharge it ([170c]): its injectivity
hypotheses are `Consistent` + `Nodup`.

* `parity_not_altO_block_width_aware_clean` — `AltO (d+2) C₀ ∧ BottomWidth w C₀ ∧ BottomClean C₀ ⟹
  ∃ x, eval C₀ x ≠ parity x`, with the sole structural input a *clean+width-aware* per-round block
  survivor.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **The width-aware general-`d` parity bound, block, with `BottomClean` threaded.**  The per-round
block survivor `hsurv` may assume the current width-`≤ w` tower is `BottomClean`. -/
theorem parity_not_altO_block_width_aware_clean (s w F d : ℕ) (hsw : s ≤ w) (C₀ : Layered n)
    (τ₀ : Fin n → Option Bool) (hC₀ : AltO (d + 2) C₀) (hbw₀ : BottomWidth w C₀)
    (hcl₀ : BottomClean C₀) (hτ₀ : s ≤ SwitchingCounting.stars τ₀)
    (hsurv : ∀ (C : Layered n) (τ : Fin n → Option Bool), BottomWidth w C → BottomClean C →
        s ≤ SwitchingCounting.stars τ →
        ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ s ≤ SwitchingCounting.stars ρ ∧
          SwitchingCounting.stars ρ < F ∧ ShallowsBlock w F ρ s C) :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x := by
  refine recursive_tower_not_parity_surv_seq_block
    (fun i C => (if i ≤ d then AltO (d + 2 - i) C else True) ∧ BottomWidth w C ∧ BottomClean C)
    (fun _ => s) C₀ τ₀ ?_ hτ₀ ?_ d w F ?_
  · -- Valid 0 C₀
    refine ⟨?_, hbw₀, hcl₀⟩
    simp only [Nat.zero_le, if_true, Nat.sub_zero]; exact hC₀
  · -- oracle
    intro i C τ hV hsurvτ
    obtain ⟨hP, hbw, hcl⟩ := hV
    by_cases hid : i < d
    · simp only [] at hP; rw [if_pos (le_of_lt hid)] at hP
      obtain ⟨ρ, hext, hge, hltF, hshallow⟩ := hsurv C τ hbw hcl hsurvτ
      refine ⟨collapseRoundBlock w F ρ C, ρ, hext, hge,
        collapseRoundBlock_EquivOn w F hltF C, ?_, ?_, ?_⟩
      · show (if i + 1 ≤ d then AltO (d + 2 - (i + 1)) (collapseRoundBlock w F ρ C) else True)
        rw [if_pos (show i + 1 ≤ d from hid)]
        have hk : d + 2 - i = (d - 1 - i) + 3 := by omega
        rw [hk] at hP
        have hred := collapseRoundBlock_AltO w F ρ hP
        have hk2 : d + 2 - (i + 1) = (d - 1 - i) + 2 := by omega
        rw [hk2]; exact hred
      · exact BottomWidth_mono hsw (collapseRoundBlock_BottomWidth w F ρ hshallow)
      · exact collapseRoundBlock_BottomClean w F ρ hcl.2
    · refine ⟨C, τ, fun _ _ h => h, hsurvτ, fun _ _ => rfl, ?_, hbw, hcl⟩
      show (if i + 1 ≤ d then AltO (d + 2 - (i + 1)) C else True)
      rw [if_neg (by omega : ¬ i + 1 ≤ d)]; trivial
  · -- terminal (block), discharged from hsurv at the final clean bottom DNF
    intro Cd σ hVd _hextσ hsurvσ
    obtain ⟨hPd, hbwd, hcld⟩ := hVd
    simp only [] at hPd
    rw [if_pos (le_refl d), show d + 2 - d = 2 from by omega] at hPd
    obtain ⟨D, rfl⟩ := AltO_two_dnf hPd
    obtain ⟨ρ, hext, hge, hltF, hshallow⟩ := hsurv (dnf D) σ hbwd hcld hsurvσ
    refine ⟨ρ, D, hext, rfl, hltF, ?_⟩
    have hsh := (hshallow D (by rw [show bottomGates (dnf D) = [D] from rfl]; simp)).1
    exact lt_of_lt_of_le hsh hge

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_altO_block_width_aware_clean
