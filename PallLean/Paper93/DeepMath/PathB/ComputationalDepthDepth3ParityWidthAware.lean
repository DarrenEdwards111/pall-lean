import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RecursiveTowerSurv
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3AltReduce
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRoundBounded

/-!
# Tight switching, step 59: the width-aware general-`d` parity bound — `hterm` eliminated (branch `razborov-recoverRho-wip`)

The payoff of the width-aware machinery (steps 53–58): the terminal oracle `hterm` of the general-`d` capstone
(step 51) is **discharged**, leaving only a single per-round survivor hypothesis `hsurv`.

The recursive tower is run with `Valid i C := (alternation depth `d+2-i`) ∧ BottomWidth w C`.  Each round the
oracle pulls a survivor `ρ` from `hsurv` that shallows every bottom gate of the *current* tower (`Shallows F ρ
s C`), then `collapseRound`: the alternation drops one level (`collapseRound_AltO`, step 50), `EquivOn` holds
(step 47), and the bottom width stays `≤ s ≤ w` (`collapseRound_BottomWidth`, step 58).  After `d` rounds the
tower is a bottom `DNF` `dnf D` (`AltO_two_dnf`) of width `≤ w` — so the *same* `hsurv` applied to `dnf D`
shallows it below `s ≤ stars ρ`, which is exactly the terminal shallowness the parity capstone needs.  No
separate `hterm`, no `hround`: just the per-round subcube survivor (the irreducible Håstad/Razborov content,
itself an instance of `exists_survivor_shallow_extends_uncond` at `G = bottomGates C ∪ map negDNF`).

* `parity_not_altO_width_aware` — `AltO (d+2) C₀ ∧ BottomWidth w C₀ ⟹ ∃ x, eval C₀ x ≠ parity x`, with the
  sole structural input the per-round survivor `hsurv`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **The width-aware general-`d` parity lower bound.**  With the bottom width threaded through the tower, the
terminal switching oracle is discharged from the per-round survivor `hsurv`: a depth-`(d+2)` alternating tower
of bottom width `≤ w` does not compute parity, given only that every reachable tower of width `≤ w` admits a
survivor shallowing all its bottom gates below `s` (with `s ≤ w`). -/
theorem parity_not_altO_width_aware (s w F d : ℕ) (hsw : s ≤ w) (C₀ : Layered n)
    (τ₀ : Fin n → Option Bool) (hC₀ : AltO (d + 2) C₀) (hbw₀ : BottomWidth w C₀)
    (hτ₀ : s ≤ SwitchingCounting.stars τ₀)
    (hsurv : ∀ (C : Layered n) (τ : Fin n → Option Bool), BottomWidth w C →
        s ≤ SwitchingCounting.stars τ →
        ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ s ≤ SwitchingCounting.stars ρ ∧
          SwitchingCounting.stars ρ ≤ F ∧ Shallows F ρ s C) :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x := by
  refine recursive_tower_not_parity_surv
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
      obtain ⟨ρ, hext, hge, hle, hshallow⟩ := hsurv C τ hbw hsurvτ
      refine ⟨collapseRound F ρ C, ρ, hext, hge, collapseRound_EquivOn F hle C, ?_, ?_⟩
      · show (if i + 1 ≤ d then AltO (d + 2 - (i + 1)) (collapseRound F ρ C) else True)
        rw [if_pos (show i + 1 ≤ d from hid)]
        have hk : d + 2 - i = (d - 1 - i) + 3 := by omega
        rw [hk] at hP
        have hred := collapseRound_AltO F ρ hP
        have hk2 : d + 2 - (i + 1) = (d - 1 - i) + 2 := by omega
        rw [hk2]; exact hred
      · exact BottomWidth_mono hsw (collapseRound_BottomWidth F ρ hshallow)
    · refine ⟨C, τ, fun _ _ h => h, hsurvτ, fun _ _ => rfl, ?_, hbw⟩
      show (if i + 1 ≤ d then AltO (d + 2 - (i + 1)) C else True)
      rw [if_neg (by omega : ¬ i + 1 ≤ d)]; trivial
  · -- hterm, discharged from hsurv at the final bottom DNF
    intro Cd σ hVd _hextσ hsurvσ
    obtain ⟨hPd, hbwd⟩ := hVd
    simp only [] at hPd
    rw [if_pos (le_refl d), show d + 2 - d = 2 from by omega] at hPd
    obtain ⟨D, rfl⟩ := AltO_two_dnf hPd
    obtain ⟨ρ, hext, hge, hle, hshallow⟩ := hsurv (dnf D) σ hbwd hsurvσ
    refine ⟨ρ, D, hext, rfl, hle, ?_⟩
    have hsh := (hshallow D (by rw [show bottomGates (dnf D) = [D] from rfl]; simp)).1
    exact lt_of_lt_of_le hsh hge

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_altO_width_aware
