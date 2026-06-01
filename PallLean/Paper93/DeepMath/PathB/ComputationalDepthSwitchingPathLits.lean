import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingCompletionRecover
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingActiveCard

/-!
# The real encoder satisfies the completion-recovery hypothesis

**STATUS: REAL.  σ* RECOVERS ρ FOR THE ACTUAL PATH ENCODER.**

`revPeel_complete` recovers `ρ` from the satisfying completion *given* the path's chosen
literals lie on `ρ`-free variables.  Here we discharge that hypothesis for the actual
path: each chosen literal's variable lies in `actSel ⊆ freeVars ρ`, so it is free in `ρ`.

* `pathLits`: the path's chosen literals (the `litVar`-list is `pathVarsRev`);
* `pathLits_litVar_mem_actSel`: each chosen literal's variable is in `actSel`;
* `pathLits_free`: hence free in `ρ` (`actSel ⊆ freeVars ρ`);
* `revPeel_complete_path`: `revPeel (complete ρ (pathLits cs ρ s)) ((pathLits …).map litVar)
  = ρ` — the completion of the real path recovers `ρ`.

This closes the **recovery side** of `decode_encode_id` on the faithful σ* layer for the
concrete encoder.  The remaining half is the forward decoder that *produces* the chosen
literals' variable set from `(cs, σ*, label)` by clause-satisfaction status.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- The path's chosen literals (reverse fixing order; `map litVar` is `pathVarsRev`). -/
def pathLits (cs : List (Clause n)) (ρ : Restriction n) : ℕ → List (Rung4Literal n)
  | 0 => []
  | k + 1 =>
    match activeLit cs (actPath cs ρ k) with
    | none => pathLits cs ρ k
    | some ℓ => ℓ :: pathLits cs ρ k

/-- Each chosen literal's variable is one of the path's selected coordinates. -/
theorem pathLits_litVar_mem_actSel (cs : List (Clause n)) (ρ : Restriction n) :
    ∀ s, ∀ ℓ ∈ pathLits cs ρ s, litVar ℓ ∈ actSel cs ρ s := by
  intro s
  induction s with
  | zero => intro ℓ h; simp [pathLits] at h
  | succ k ih =>
    intro ℓ hℓ
    cases hal : activeLit cs (actPath cs ρ k) with
    | none =>
      rw [actSel_succ_none hal]
      have hpl : pathLits cs ρ (k + 1) = pathLits cs ρ k := by simp only [pathLits, hal]
      rw [hpl] at hℓ
      exact ih ℓ hℓ
    | some ℓ₀ =>
      rw [actSel_succ_some hal]
      have hpl : pathLits cs ρ (k + 1) = ℓ₀ :: pathLits cs ρ k := by simp only [pathLits, hal]
      rw [hpl] at hℓ
      rcases List.mem_cons.mp hℓ with rfl | hℓ'
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (ih ℓ hℓ')

/-- Each chosen literal's variable is free in `ρ`. -/
theorem pathLits_free (cs : List (Clause n)) (ρ : Restriction n) (s : ℕ)
    {ℓ : Rung4Literal n} (h : ℓ ∈ pathLits cs ρ s) : ρ (litVar ℓ) = none := by
  have hmem := actSel_subset_freeVars cs ρ s (pathLits_litVar_mem_actSel cs ρ s ℓ h)
  rwa [mem_freeVars] at hmem

/-- **The completion of the real path recovers `ρ`.**  This closes the recovery side of
`decode_encode_id` on the faithful σ* layer for the concrete encoder. -/
theorem revPeel_complete_path (cs : List (Clause n)) (ρ : Restriction n) (s : ℕ) :
    revPeel (complete ρ (pathLits cs ρ s)) ((pathLits cs ρ s).map litVar) = ρ :=
  revPeel_complete (fun _ h => pathLits_free cs ρ s h)

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.revPeel_complete_path
