import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ParityGeneralD
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3RecursiveTowerSeqBlock

/-!
# Block-DT model, route-2 step [167]: the general-`d` parity lower bound, BLOCK terminal (option (b))

The block-tree twin of `parity_not_altO`.  Same depth-`(d+2)` alternating tower, same budget-agnostic
oracle (`hround` discharged structurally via `collapseRound`; one alternation level per round by
`collapseRound_AltO`), but routed through the **block** engine [166] so the terminal `hterm` is over
`canonicalDTree` — exactly the shape the m-free route-2 terminal [165] discharges.

* `parity_not_altO_block` — `AltO (d+2) C₀ ⟹ ∃ x, eval C₀ x ≠ parity x`, with the terminal switching
  taken over the block tree `canonicalDTree` (so the per-`DNF` terminal is m-free-dischargeable).

The remaining input is the per-instance terminal budget `hterm` (m-free via [165]) and the trivial
per-round survivor `hround`.  Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- **The general-`d` parity lower bound, block terminal.**  A depth-`(d+2)` alternating tower
(`AltO (d+2)`) does not compute parity, with the terminal switching expressed over the block tree
`canonicalDTree` (width parameter `w`).  Mirrors `parity_not_altO` but drives the block engine
`recursive_tower_not_parity_surv_seq_block`. -/
theorem parity_not_altO_block (s w F d : ℕ) (C₀ : Layered n) (τ₀ : Fin n → Option Bool)
    (hC₀ : AltO (d + 2) C₀) (hτ₀ : s ≤ SwitchingCounting.stars τ₀)
    (hround : ∀ τ : Fin n → Option Bool, s ≤ SwitchingCounting.stars τ →
      ∃ ρ : Fin n → Option Bool, Extends τ ρ ∧ s ≤ SwitchingCounting.stars ρ ∧
        SwitchingCounting.stars ρ ≤ F)
    (hterm : ∀ (cs : List (Clause n)) (σ : Fin n → Option Bool), s ≤ SwitchingCounting.stars σ →
      ∃ σ' : Fin n → Option Bool, Extends σ σ' ∧ SwitchingCounting.stars σ' < F ∧
        (canonicalDTree cs w F σ').depth < SwitchingCounting.stars σ') :
    ∃ x : Fin n → Bool, eval C₀ x ≠ DTree.parity x := by
  refine recursive_tower_not_parity_surv_seq_block
    (fun i C => if i ≤ d then AltO (d + 2 - i) C else True) (fun _ => s) C₀ τ₀ ?_ hτ₀ ?_ d w F ?_
  · -- Valid 0 C₀
    simp only [Nat.zero_le, if_true, Nat.sub_zero]; exact hC₀
  · -- oracle (identical to parity_not_altO: structural collapse, one alternation level per round)
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
  · -- terminal (block): the bottom AltO 2 is a DNF, made shallow by the block terminal `hterm`
    intro Cd σ hVd _hext hsurv
    simp only [] at hVd
    rw [if_pos (le_refl d), show d + 2 - d = 2 from by omega] at hVd
    obtain ⟨cs, rfl⟩ := AltO_two_dnf hVd
    obtain ⟨σ', hext', hltF', hsh'⟩ := hterm cs σ hsurv
    exact ⟨σ', cs, hext', rfl, hltF', hsh'⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.parity_not_altO_block
