import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingActive
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingPolarity

/-!
# The faithful canonical path fold (corrected active clause + falsify polarity)

**STATUS: REAL.  THE FAITHFUL FOLD WITH SET-LEVEL RECOVERY.**

The canonical path using the corrected active clause (`activeLit`: first free
literal of the first unsatisfied clause that still has a free literal) and the
falsify polarity (`falFix`).  This is the faithful state machine:

* while the active clause has free literals, keep falsifying them;
* once exhausted (no free literal) it stays unsatisfied but is no longer active;
* move on to the next unsatisfied clause with a free literal.

Set-level recovery transfers (depends only on which coordinates are fixed):

* `actPath_eq_outside`: the path changes `σ` only on selected coordinates;
* `freeOn_actPath`: `freeOn (actPath cs σ k) (actSel cs σ k) = σ`;
* `actPath_inj`: `σ ↦ (actPath, actSel)` injective.

The forward decoder (recover `actSel` from `(actPath, PathLabel)` by replaying
`activeClause`) is the next layer; its invariant tracks the *first unfinished
unsatisfied clause*, which changes exactly when the previous one reaches
`freeLits.length = 0`.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- One faithful canonical step: falsify the first free literal of the active clause. -/
def actStep (cs : List (Clause n)) (σ : Restriction n) : Restriction n :=
  match activeLit cs σ with
  | none => σ
  | some ℓ => falFix σ ℓ

theorem actStep_eq_outside (cs : List (Clause n)) (σ : Restriction n) {j : Fin n}
    (hj : ∀ ℓ, activeLit cs σ = some ℓ → j ≠ litVar ℓ) : actStep cs σ j = σ j := by
  rw [actStep]
  cases h : activeLit cs σ with
  | none => rfl
  | some ℓ => exact falFix_eq_outside σ ℓ (hj ℓ h)

theorem freeVars_actStep_subset (cs : List (Clause n)) (σ : Restriction n) :
    freeVars (actStep cs σ) ⊆ freeVars σ := by
  intro j hj
  rw [mem_freeVars] at hj ⊢
  by_cases hc : ∀ ℓ, activeLit cs σ = some ℓ → j ≠ litVar ℓ
  · rw [actStep_eq_outside cs σ hc] at hj; exact hj
  · push_neg at hc
    obtain ⟨ℓ, hℓ, hjv⟩ := hc
    rw [actStep, hℓ, hjv] at hj
    simp [falFix, Function.update_self] at hj

/-- The faithful path after `k` steps. -/
def actPath (cs : List (Clause n)) (σ : Restriction n) : ℕ → Restriction n
  | 0 => σ
  | k + 1 => actStep cs (actPath cs σ k)

/-- The selected coordinates after `k` steps. -/
def actSel (cs : List (Clause n)) (σ : Restriction n) : ℕ → Finset (Fin n)
  | 0 => ∅
  | k + 1 => actSel cs σ k ∪
      (match activeLit cs (actPath cs σ k) with | none => ∅ | some ℓ => {litVar ℓ})

theorem freeVars_actPath_subset (cs : List (Clause n)) (σ : Restriction n) (k : ℕ) :
    freeVars (actPath cs σ k) ⊆ freeVars σ := by
  induction k with
  | zero => exact Finset.Subset.refl _
  | succ k ih => intro j hj; exact ih (freeVars_actStep_subset cs (actPath cs σ k) hj)

theorem actPath_eq_outside (cs : List (Clause n)) (σ : Restriction n) (k : ℕ) {j : Fin n}
    (hj : j ∉ actSel cs σ k) : actPath cs σ k j = σ j := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [actSel, Finset.mem_union, not_or] at hj
    have hstep : actStep cs (actPath cs σ k) j = actPath cs σ k j := by
      refine actStep_eq_outside cs (actPath cs σ k) (fun ℓ hℓ hjv => ?_)
      apply hj.2; rw [hℓ, hjv]; exact Finset.mem_singleton_self _
    rw [actPath, hstep]
    exact ih hj.1

theorem actSel_subset_freeVars (cs : List (Clause n)) (σ : Restriction n) (k : ℕ) :
    actSel cs σ k ⊆ freeVars σ := by
  induction k with
  | zero => simp [actSel]
  | succ k ih =>
    intro j hj
    rw [actSel, Finset.mem_union] at hj
    rcases hj with h | h
    · exact ih h
    · cases hs : activeLit cs (actPath cs σ k) with
      | none => rw [hs] at h; simp at h
      | some ℓ =>
        rw [hs, Finset.mem_singleton] at h
        subst h
        apply freeVars_actPath_subset cs σ k
        rw [mem_freeVars]
        have := activeLit_free hs
        rw [litFree_var] at this
        exact Option.isNone_iff_eq_none.mp this

/-- **`decode_encode_id` (set level), faithful machine.** -/
theorem freeOn_actPath (cs : List (Clause n)) (σ : Restriction n) (k : ℕ) :
    freeOn (actPath cs σ k) (actSel cs σ k) = σ := by
  funext j
  simp only [freeOn]
  by_cases hj : j ∈ actSel cs σ k
  · rw [if_pos hj]
    exact (mem_freeVars.mp (actSel_subset_freeVars cs σ k hj)).symm
  · rw [if_neg hj]
    exact actPath_eq_outside cs σ k hj

/-- **Injectivity.**  `σ` is determined by its faithful path and selected set. -/
theorem actPath_inj (cs : List (Clause n)) (k : ℕ) {σ τ : Restriction n}
    (hp : actPath cs σ k = actPath cs τ k) (hs : actSel cs σ k = actSel cs τ k) : σ = τ := by
  rw [← freeOn_actPath cs σ k, hp, hs, freeOn_actPath cs τ k]

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.freeOn_actPath
#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.actPath_inj
