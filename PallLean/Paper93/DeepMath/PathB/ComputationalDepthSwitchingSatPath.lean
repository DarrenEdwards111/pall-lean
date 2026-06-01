import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingSatStep

/-!
# The satisfaction-based path fold + replay invariant (recovery)

**STATUS: REAL.  SET-LEVEL RECOVERY/INJECTIVITY ON THE SATISFACTION FOUNDATION.**

Iterating the satisfaction-based step (`satStep`) over a flat clause list: at each
step fix the first free literal of the first unsatisfied clause.  This is the
canonical satisfying process.  Proves the replay invariant at the set level:

* `satStep_eq_outside` / `satPath_eq_outside`: the path changes `σ` only on the
  selected coordinates;
* `satSel_subset_freeVars`: every selected coordinate was free;
* `freeOn_satPath`: freeing the selected coordinates recovers `σ` — the
  `decode_encode_id` for this path;
* `satPath_inj`: `σ ↦ (satPath, satSel)` is injective.

Built on the satisfaction step so the active clause (`firstUnsat`) is recomputable
from the restriction alone — the property the tight `(2w)^s` label replay needs
(the next layer: record the per-step `Fin w` index and recover `satSel` from the
label via `firstUnsat`).
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- The literal chosen at one step: first free literal of the first unsatisfied
clause. -/
def satStepLit (cs : List (Clause n)) (σ : Restriction n) : Option (Rung4Literal n) :=
  match firstUnsat σ cs with
  | none => none
  | some C => (freeLits σ C).head?

/-- One satisfaction step: fix the chosen literal's variable (if any). -/
def satStep (cs : List (Clause n)) (σ : Restriction n) : Restriction n :=
  match satStepLit cs σ with
  | none => σ
  | some ℓ => satFix σ ℓ

/-- The chosen literal is free. -/
theorem satStepLit_free {cs : List (Clause n)} {σ : Restriction n} {ℓ : Rung4Literal n}
    (h : satStepLit cs σ = some ℓ) : Depth3.litFree σ ℓ = true := by
  unfold satStepLit at h
  cases hC : firstUnsat σ cs with
  | none => rw [hC] at h; exact absurd h (by simp)
  | some C =>
    rw [hC] at h
    have hmem : ℓ ∈ freeLits σ C := List.mem_of_mem_head? h
    exact (List.mem_filter.mp hmem).2

/-- The step changes only the chosen variable. -/
theorem satStep_eq_outside (cs : List (Clause n)) (σ : Restriction n) {j : Fin n}
    (hj : ∀ ℓ, satStepLit cs σ = some ℓ → j ≠ litVar ℓ) : satStep cs σ j = σ j := by
  rw [satStep]
  cases h : satStepLit cs σ with
  | none => rfl
  | some ℓ => exact satFix_eq_outside σ ℓ (hj ℓ h)

/-- The step shrinks the free set. -/
theorem freeVars_satStep_subset (cs : List (Clause n)) (σ : Restriction n) :
    freeVars (satStep cs σ) ⊆ freeVars σ := by
  intro j hj
  rw [mem_freeVars] at hj ⊢
  by_cases hc : ∀ ℓ, satStepLit cs σ = some ℓ → j ≠ litVar ℓ
  · rw [satStep_eq_outside cs σ hc] at hj; exact hj
  · push_neg at hc
    obtain ⟨ℓ, hℓ, hjv⟩ := hc
    -- j = litVar ℓ; satStep fixes it to `some _`, contradicting hj : satStep _ j = none
    rw [satStep, hℓ, hjv] at hj
    simp [satFix, Function.update_self] at hj

/-- The accumulated path after `k` steps. -/
def satPath (cs : List (Clause n)) (σ : Restriction n) : ℕ → Restriction n
  | 0 => σ
  | k + 1 => satStep cs (satPath cs σ k)

/-- The selected coordinates after `k` steps. -/
def satSel (cs : List (Clause n)) (σ : Restriction n) : ℕ → Finset (Fin n)
  | 0 => ∅
  | k + 1 => satSel cs σ k ∪
      (match satStepLit cs (satPath cs σ k) with | none => ∅ | some ℓ => {litVar ℓ})

theorem freeVars_satPath_subset (cs : List (Clause n)) (σ : Restriction n) (k : ℕ) :
    freeVars (satPath cs σ k) ⊆ freeVars σ := by
  induction k with
  | zero => exact Finset.Subset.refl _
  | succ k ih =>
    intro j hj
    exact ih (freeVars_satStep_subset cs (satPath cs σ k) hj)

/-- **Path invariant.**  The path changes `σ` only on the selected coordinates. -/
theorem satPath_eq_outside (cs : List (Clause n)) (σ : Restriction n) (k : ℕ) {j : Fin n}
    (hj : j ∉ satSel cs σ k) : satPath cs σ k j = σ j := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [satSel, Finset.mem_union, not_or] at hj
    have hstep : satStep cs (satPath cs σ k) j = satPath cs σ k j := by
      refine satStep_eq_outside cs (satPath cs σ k) (fun ℓ hℓ hjv => ?_)
      apply hj.2
      rw [hℓ, hjv]; exact Finset.mem_singleton_self _
    rw [satPath, hstep]
    exact ih hj.1

/-- Every selected coordinate was free in `σ`. -/
theorem satSel_subset_freeVars (cs : List (Clause n)) (σ : Restriction n) (k : ℕ) :
    satSel cs σ k ⊆ freeVars σ := by
  induction k with
  | zero => simp [satSel]
  | succ k ih =>
    intro j hj
    rw [satSel, Finset.mem_union] at hj
    rcases hj with h | h
    · exact ih h
    · cases hs : satStepLit cs (satPath cs σ k) with
      | none => rw [hs] at h; simp at h
      | some ℓ =>
        rw [hs, Finset.mem_singleton] at h
        subst h
        apply freeVars_satPath_subset cs σ k
        rw [mem_freeVars]
        have := satStepLit_free hs
        rw [litFree_var] at this
        exact Option.isNone_iff_eq_none.mp this

/-- **`decode_encode_id` (set level).**  Freeing the selected coordinates of the path
recovers `σ`. -/
theorem freeOn_satPath (cs : List (Clause n)) (σ : Restriction n) (k : ℕ) :
    freeOn (satPath cs σ k) (satSel cs σ k) = σ := by
  funext j
  simp only [freeOn]
  by_cases hj : j ∈ satSel cs σ k
  · rw [if_pos hj]
    exact (mem_freeVars.mp (satSel_subset_freeVars cs σ k hj)).symm
  · rw [if_neg hj]
    exact satPath_eq_outside cs σ k hj

/-- **Injectivity.**  `σ` is determined by its path together with its selected set. -/
theorem satPath_inj (cs : List (Clause n)) (k : ℕ) {σ τ : Restriction n}
    (hp : satPath cs σ k = satPath cs τ k) (hs : satSel cs σ k = satSel cs τ k) : σ = τ := by
  rw [← freeOn_satPath cs σ k, hp, hs, freeOn_satPath cs τ k]

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.freeOn_satPath
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.satPath_inj
