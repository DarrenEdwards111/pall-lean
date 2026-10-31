import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityWCSeq2
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRoundCount2

/-!
# Tight switching, step 99: the full four-invariant capstone (alternation, width `t`, gate count, clause count) (branch `razborov-recoverRho-wip`)

The two-parameter capstone (step 97) augmented with the **per-gate clause-count** invariant `BottomCount m`,
threaded by `collapseRound_BottomCount` (step 98): a round leaves per-gate clause-count `≤ M·2^t ≤ m` (with
`t` the *small* depth threshold, so `M·2^t` is constant).  So the per-round survivor `hsurv` now receives all
four bounds — alternation depth, bottom width `t`, gate count `≤ M`, per-gate clause-count `≤ m` — i.e.
everything the two-parameter survivor (`hsurv_REL2_round`, step 96) needs at a *constant* rate.

* `parity_not_altO_wc_seq3` — the general-`d` parity bound with all four invariants threaded.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

theorem BottomCount_mono {M M' : ℕ} (h : M ≤ M') {C : Layered n} (hbc : BottomCount M C) :
    BottomCount M' C :=
  fun cs hcs => le_trans (hbc cs hcs) h

/-- **The full four-invariant capstone.**  Alternation, bottom width `t`, gate count `≤ M`, and per-gate
clause-count `≤ m` are all threaded; the survivor `hsurv` receives all four. -/
theorem parity_not_altO_wc_seq3 (s : ℕ → ℕ) (t F d M m : ℕ)
    (hmono : ∀ i, s (i + 1) ≤ s i) (htd : t ≤ s (d + 1)) (hM1 : 1 ≤ M) (hMm : M * 2 ^ t ≤ m)
    (C₀ : Layered n) (τ₀ : Fin n → Option Bool) (hC₀ : AltO (d + 2) C₀) (hbw₀ : BottomWidth t C₀)
    (hcnt₀ : (bottomGates C₀).length ≤ M) (hmc₀ : BottomCount m C₀)
    (hτ₀ : s 0 ≤ SwitchingCounting.stars τ₀)
    (hsurv : ∀ (i : ℕ), i ≤ d → ∀ (C : Layered n) (τ : Fin n → Option Bool), BottomWidth t C →
        (bottomGates C).length ≤ M → BottomCount m C → s i ≤ SwitchingCounting.stars τ →
        ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ s (i + 1) ≤ SwitchingCounting.stars ρ ∧
          SwitchingCounting.stars ρ ≤ F ∧ Shallows F ρ t C) :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x := by
  refine recursive_tower_not_parity_surv_seq
    (fun i C => (if i ≤ d then AltO (d + 2 - i) C else True) ∧ BottomWidth t C ∧
      (bottomGates C).length ≤ M ∧ BottomCount m C)
    s C₀ τ₀ ?_ hτ₀ ?_ d F ?_
  · refine ⟨?_, hbw₀, hcnt₀, hmc₀⟩
    simp only [Nat.zero_le, if_true, Nat.sub_zero]; exact hC₀
  · intro i C τ hV hsurvτ
    obtain ⟨hP, hbw, hcnt, hmcc⟩ := hV
    by_cases hid : i < d
    · simp only [] at hP; rw [if_pos (le_of_lt hid)] at hP
      obtain ⟨ρ, hext, hge, hle, hshallow⟩ := hsurv i (le_of_lt hid) C τ hbw hcnt hmcc hsurvτ
      refine ⟨collapseRound F ρ C, ρ, hext, hge, collapseRound_EquivOn F hle C, ?_, ?_, ?_, ?_⟩
      · show (if i + 1 ≤ d then AltO (d + 2 - (i + 1)) (collapseRound F ρ C) else True)
        rw [if_pos (show i + 1 ≤ d from hid)]
        have hk : d + 2 - i = (d - 1 - i) + 3 := by omega
        rw [hk] at hP
        have hred := collapseRound_AltO F ρ hP
        have hk2 : d + 2 - (i + 1) = (d - 1 - i) + 2 := by omega
        rw [hk2]; exact hred
      · exact collapseRound_BottomWidth F ρ hshallow
      · exact le_trans (collapseRound_count_le F ρ (AltO_NonEmptyGates hP)) hcnt
      · exact BottomCount_mono hMm
          (collapseRound_BottomCount F ρ hM1 (AltO_NonEmptyGates hP) hshallow hcnt)
    · refine ⟨C, τ, fun _ _ h => h, le_trans (hmono i) hsurvτ, fun _ _ => rfl, ?_, hbw, hcnt, hmcc⟩
      show (if i + 1 ≤ d then AltO (d + 2 - (i + 1)) C else True)
      rw [if_neg (by omega : ¬ i + 1 ≤ d)]; trivial
  · intro Cd σ hVd _hextσ hsurvσ
    obtain ⟨hPd, hbwd, hcntd, hmcd⟩ := hVd
    simp only [] at hPd
    rw [if_pos (le_refl d), show d + 2 - d = 2 from by omega] at hPd
    obtain ⟨D, rfl⟩ := AltO_two_dnf hPd
    obtain ⟨ρ, hext, hge, hle, hshallow⟩ := hsurv d (le_refl d) (dnf D) σ hbwd hcntd hmcd hsurvσ
    refine ⟨ρ, D, hext, rfl, hle, ?_⟩
    have hsh := (hshallow D (by rw [show bottomGates (dnf D) = [D] from rfl]; simp)).1
    exact lt_of_lt_of_le hsh (le_trans htd hge)

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_altO_wc_seq3
