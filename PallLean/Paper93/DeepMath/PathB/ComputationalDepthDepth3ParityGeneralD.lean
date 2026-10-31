import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RecursiveTowerSurv
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseRound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3AltReduce

/-!
# Tight switching, step 51: the general-`d` parity lower bound (branch `razborov-recoverRho-wip`)

The final assembly: a depth-`(d+2)` alternating `AC⁰` tower (top `OR`, `AltO (d+2)`) does not compute parity.
The recursive-tower engine (step 43) is instantiated with `Valid i C := AltO (d+2-i) C` (capped at `True`
past depth 2); each round's oracle is discharged by picking a survivor-extending `ρ` (`hround`, from
`exists_survivor_shallow_extends_uncond`, step 36) and applying the per-round collapse (`collapseRound`, step
47) — `EquivOn` by step 47, `Valid`-decrease (one alternation level) by `collapseRound_AltO` (step 50).  After
`d` rounds the tower is `AltO 2 = dnf` (`AltO_two_dnf`), and the terminal switching (`hterm`) makes that bottom
`DNF` shallow, so the parity capstone fires.

* `parity_not_altO` — `AltO (d+2) C₀ ⟹ ∃ x, eval C₀ x ≠ parity x` (general depth `d`).

This is the fully-general-depth unconditional `parity ∉ AC⁰`, routed through the recursive tower.  `hround`
and `hterm` are the per-instance budgets (the survivor union bound per round, and the terminal switching on
the final `DNF`), discharged by the unconditional collapse/survivor machinery (steps 36/38).  No
`hnf`/`hleaf`/`hpos`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **The general-`d` parity lower bound.**  A depth-`(d+2)` alternating tower (`AltO (d+2)`) does not
compute parity: the recursive tower collapses it `d` rounds to a bottom `DNF` (each round via
`collapseRound`, one alternation level by `collapseRound_AltO`), which the terminal switching `hterm` makes
shallow. -/
theorem parity_not_altO (s F d : ℕ) (C₀ : Layered n) (τ₀ : Fin n → Option Bool)
    (hC₀ : AltO (d + 2) C₀) (hτ₀ : s ≤ SwitchingCounting.stars τ₀)
    (hround : ∀ τ : Fin n → Option Bool, s ≤ SwitchingCounting.stars τ →
      ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ s ≤ SwitchingCounting.stars ρ ∧
        SwitchingCounting.stars ρ ≤ F)
    (hterm : ∀ (cs : List (Clause n)) (σ : Fin n → Option Bool), s ≤ SwitchingCounting.stars σ →
      ∃ σ' : Fin n → Option Bool, Extends σ σ' ∧ SwitchingCounting.stars σ' ≤ F ∧
        (canonicalDT cs F σ').depth < SwitchingCounting.stars σ') :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x := by
  refine recursive_tower_not_parity_surv
    (fun i C => if i ≤ d then AltO (d + 2 - i) C else True) s C₀ τ₀ ?_ hτ₀ ?_ d F ?_
  · -- Valid 0 C₀
    simp only [Nat.zero_le, if_true, Nat.sub_zero]; exact hC₀
  · -- oracle
    intro i C τ hV hsurv
    by_cases hid : i < d
    · simp only [] at hV; rw [if_pos (le_of_lt hid)] at hV
      obtain ⟨ρ, hext, hge, hle⟩ := hround τ hsurv
      refine ⟨collapseRound F ρ C, ρ, hext, hge, collapseRound_EquivOn F hle C, ?_⟩
      show (if i + 1 ≤ d then AltO (d + 2 - (i + 1)) (collapseRound F ρ C) else True)
      rw [if_pos (show i + 1 ≤ d from hid)]
      have hk : d + 2 - i = (d - 1 - i) + 3 := by omega
      rw [hk] at hV
      have hred := collapseRound_AltO F ρ hV
      have hk2 : d + 2 - (i + 1) = (d - 1 - i) + 2 := by omega
      rw [hk2]; exact hred
    · refine ⟨C, τ, fun _ _ h => h, hsurv, fun _ _ => rfl, ?_⟩
      show (if i + 1 ≤ d then AltO (d + 2 - (i + 1)) C else True)
      rw [if_neg (by omega : ¬ i + 1 ≤ d)]; trivial
  · -- hterm
    intro Cd σ hVd _hext hsurv
    simp only [] at hVd
    rw [if_pos (le_refl d), show d + 2 - d = 2 from by omega] at hVd
    obtain ⟨cs, rfl⟩ := AltO_two_dnf hVd
    obtain ⟨σ', hext', hle', hsh'⟩ := hterm cs σ hsurv
    exact ⟨σ', cs, hext', rfl, hle', hsh'⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_altO
