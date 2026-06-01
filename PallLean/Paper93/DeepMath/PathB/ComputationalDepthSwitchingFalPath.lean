import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingSatPath
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingPolarity

/-!
# The falsification path fold + recovery (correct Håstad polarity)

**STATUS: REAL.  THE FOLD ON THE CORRECT POLARITY, WITH SET-LEVEL RECOVERY.**

The path fold using `falFix` (falsify the chosen literal) — the polarity the
forward decoder needs.  Structurally identical to `satPath`; the literal-selection
`satStepLit` is polarity-independent and reused.  The set-level recovery transfers
verbatim (it depends only on which coordinates are fixed, not their values):

* `falPath_eq_outside`: the path changes `σ` only on selected coordinates;
* `freeOn_falPath`: `freeOn (falPath cs σ k) (falSel cs σ k) = σ`;
* `falPath_inj`: `σ ↦ (falPath, falSel)` injective.

The new content vs `satPath` is the *polarity*: combined with
`clauseSatisfied_falFix` (forward-stability), the active clause stays visible under
`firstUnsat`, so this is the path the forward decoder can replay.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- One falsification step: fix the chosen literal's variable to make it false. -/
def falStep (cs : List (Clause n)) (σ : Restriction n) : Restriction n :=
  match satStepLit cs σ with
  | none => σ
  | some ℓ => falFix σ ℓ

theorem falStep_eq_outside (cs : List (Clause n)) (σ : Restriction n) {j : Fin n}
    (hj : ∀ ℓ, satStepLit cs σ = some ℓ → j ≠ litVar ℓ) : falStep cs σ j = σ j := by
  rw [falStep]
  cases h : satStepLit cs σ with
  | none => rfl
  | some ℓ => exact falFix_eq_outside σ ℓ (hj ℓ h)

theorem freeVars_falStep_subset (cs : List (Clause n)) (σ : Restriction n) :
    freeVars (falStep cs σ) ⊆ freeVars σ := by
  intro j hj
  rw [mem_freeVars] at hj ⊢
  by_cases hc : ∀ ℓ, satStepLit cs σ = some ℓ → j ≠ litVar ℓ
  · rw [falStep_eq_outside cs σ hc] at hj; exact hj
  · push_neg at hc
    obtain ⟨ℓ, hℓ, hjv⟩ := hc
    rw [falStep, hℓ, hjv] at hj
    simp [falFix, Function.update_self] at hj

/-- The path after `k` falsification steps. -/
def falPath (cs : List (Clause n)) (σ : Restriction n) : ℕ → Restriction n
  | 0 => σ
  | k + 1 => falStep cs (falPath cs σ k)

/-- The selected coordinates after `k` steps. -/
def falSel (cs : List (Clause n)) (σ : Restriction n) : ℕ → Finset (Fin n)
  | 0 => ∅
  | k + 1 => falSel cs σ k ∪
      (match satStepLit cs (falPath cs σ k) with | none => ∅ | some ℓ => {litVar ℓ})

theorem freeVars_falPath_subset (cs : List (Clause n)) (σ : Restriction n) (k : ℕ) :
    freeVars (falPath cs σ k) ⊆ freeVars σ := by
  induction k with
  | zero => exact Finset.Subset.refl _
  | succ k ih => intro j hj; exact ih (freeVars_falStep_subset cs (falPath cs σ k) hj)

theorem falPath_eq_outside (cs : List (Clause n)) (σ : Restriction n) (k : ℕ) {j : Fin n}
    (hj : j ∉ falSel cs σ k) : falPath cs σ k j = σ j := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [falSel, Finset.mem_union, not_or] at hj
    have hstep : falStep cs (falPath cs σ k) j = falPath cs σ k j := by
      refine falStep_eq_outside cs (falPath cs σ k) (fun ℓ hℓ hjv => ?_)
      apply hj.2; rw [hℓ, hjv]; exact Finset.mem_singleton_self _
    rw [falPath, hstep]
    exact ih hj.1

theorem falSel_subset_freeVars (cs : List (Clause n)) (σ : Restriction n) (k : ℕ) :
    falSel cs σ k ⊆ freeVars σ := by
  induction k with
  | zero => simp [falSel]
  | succ k ih =>
    intro j hj
    rw [falSel, Finset.mem_union] at hj
    rcases hj with h | h
    · exact ih h
    · cases hs : satStepLit cs (falPath cs σ k) with
      | none => rw [hs] at h; simp at h
      | some ℓ =>
        rw [hs, Finset.mem_singleton] at h
        subst h
        apply freeVars_falPath_subset cs σ k
        rw [mem_freeVars]
        have := satStepLit_free hs
        rw [litFree_var] at this
        exact Option.isNone_iff_eq_none.mp this

/-- **`decode_encode_id` (set level), correct polarity.** -/
theorem freeOn_falPath (cs : List (Clause n)) (σ : Restriction n) (k : ℕ) :
    freeOn (falPath cs σ k) (falSel cs σ k) = σ := by
  funext j
  simp only [freeOn]
  by_cases hj : j ∈ falSel cs σ k
  · rw [if_pos hj]
    exact (mem_freeVars.mp (falSel_subset_freeVars cs σ k hj)).symm
  · rw [if_neg hj]
    exact falPath_eq_outside cs σ k hj

/-- **Injectivity.**  `σ` is determined by its falsification path and selected set. -/
theorem falPath_inj (cs : List (Clause n)) (k : ℕ) {σ τ : Restriction n}
    (hp : falPath cs σ k = falPath cs τ k) (hs : falSel cs σ k = falSel cs τ k) : σ = τ := by
  rw [← freeOn_falPath cs σ k, hp, hs, freeOn_falPath cs τ k]

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.freeOn_falPath
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.falPath_inj
