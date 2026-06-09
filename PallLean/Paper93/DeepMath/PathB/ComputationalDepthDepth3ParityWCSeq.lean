import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityWidthAwareSeq
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRoundCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3NonEmptyGates

/-!
# Tight switching, step 91: the width-and-count-aware capstone on the per-round-threshold engine (branch `razborov-recoverRho-wip`)

The width-aware sequence capstone (step 65) augmented with the **gate-count** invariant (step 90): the
`Valid` predicate now also tracks `(bottomGates C).length ≤ M`, threaded by `collapseRound_count_le` (the count
is non-increasing on the alternating — hence non-empty-gates — towers).  So the per-round survivor `hsurv` now
receives the gate-count bound, which the box-free union bound needs.

* `parity_not_altO_wc_seq` — the general-`d` parity bound with both the bottom width and the gate count
  threaded through the rounds.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **The width-and-count-aware general-`d` parity bound.**  As `parity_not_altO_width_aware_seq`, but the
`Valid` invariant also carries `(bottomGates C).length ≤ M`, so the per-round survivor `hsurv` receives the
gate-count bound (used by the union bound). -/
theorem parity_not_altO_wc_seq (s : ℕ → ℕ) (w F d M : ℕ)
    (hmono : ∀ i, s (i + 1) ≤ s i) (hsw : ∀ i, s (i + 1) ≤ w) (C₀ : Layered n)
    (τ₀ : Fin n → Option Bool) (hC₀ : AltO (d + 2) C₀) (hbw₀ : BottomWidth w C₀)
    (hcnt₀ : (bottomGates C₀).length ≤ M) (hτ₀ : s 0 ≤ SwitchingCounting.stars τ₀)
    (hsurv : ∀ (i : ℕ), i ≤ d → ∀ (C : Layered n) (τ : Fin n → Option Bool), BottomWidth w C →
        (bottomGates C).length ≤ M → s i ≤ SwitchingCounting.stars τ →
        ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ s (i + 1) ≤ SwitchingCounting.stars ρ ∧
          SwitchingCounting.stars ρ ≤ F ∧ Shallows F ρ (s (i + 1)) C) :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x := by
  refine recursive_tower_not_parity_surv_seq
    (fun i C => (if i ≤ d then AltO (d + 2 - i) C else True) ∧ BottomWidth w C ∧
      (bottomGates C).length ≤ M)
    s C₀ τ₀ ?_ hτ₀ ?_ d F ?_
  · -- Valid 0 C₀
    refine ⟨?_, hbw₀, hcnt₀⟩
    simp only [Nat.zero_le, if_true, Nat.sub_zero]; exact hC₀
  · -- oracle
    intro i C τ hV hsurvτ
    obtain ⟨hP, hbw, hcnt⟩ := hV
    by_cases hid : i < d
    · simp only [] at hP; rw [if_pos (le_of_lt hid)] at hP
      obtain ⟨ρ, hext, hge, hle, hshallow⟩ := hsurv i (le_of_lt hid) C τ hbw hcnt hsurvτ
      refine ⟨collapseRound F ρ C, ρ, hext, hge, collapseRound_EquivOn F hle C, ?_, ?_, ?_⟩
      · show (if i + 1 ≤ d then AltO (d + 2 - (i + 1)) (collapseRound F ρ C) else True)
        rw [if_pos (show i + 1 ≤ d from hid)]
        have hk : d + 2 - i = (d - 1 - i) + 3 := by omega
        rw [hk] at hP
        have hred := collapseRound_AltO F ρ hP
        have hk2 : d + 2 - (i + 1) = (d - 1 - i) + 2 := by omega
        rw [hk2]; exact hred
      · exact BottomWidth_mono (hsw i) (collapseRound_BottomWidth F ρ hshallow)
      · exact le_trans (collapseRound_count_le F ρ (AltO_NonEmptyGates hP)) hcnt
    · refine ⟨C, τ, fun _ _ h => h, le_trans (hmono i) hsurvτ, fun _ _ => rfl, ?_, hbw, hcnt⟩
      show (if i + 1 ≤ d then AltO (d + 2 - (i + 1)) C else True)
      rw [if_neg (by omega : ¬ i + 1 ≤ d)]; trivial
  · -- hterm
    intro Cd σ hVd _hextσ hsurvσ
    obtain ⟨hPd, hbwd, hcntd⟩ := hVd
    simp only [] at hPd
    rw [if_pos (le_refl d), show d + 2 - d = 2 from by omega] at hPd
    obtain ⟨D, rfl⟩ := AltO_two_dnf hPd
    obtain ⟨ρ, hext, hge, hle, hshallow⟩ := hsurv d (le_refl d) (dnf D) σ hbwd hcntd hsurvσ
    refine ⟨ρ, D, hext, rfl, hle, ?_⟩
    have hsh := (hshallow D (by rw [show bottomGates (dnf D) = [D] from rfl]; simp)).1
    exact lt_of_lt_of_le hsh hge

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_altO_wc_seq
