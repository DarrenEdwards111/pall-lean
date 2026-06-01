import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingPathLits

/-!
# The path variables are distinct

**STATUS: REAL.  DISTINCT-VARIABLE FACT FOR THE FORWARD-DECODER FOLD.**

`clauseSatisfied_complete_of_mem` (a processed clause is satisfied under σ*) needs the
path's literals to have distinct variables.  They do: each step fixes a *free* variable,
and once fixed it stays fixed, so it cannot be selected again.

* `actStep_fixed` / `actPath_fixed`: a fixed coordinate stays fixed; selected
  coordinates are fixed;
* `pathLits_nodup_litVar`: the path literals have distinct variables.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SwitchingCounting

open Depth3

variable {n : ℕ}

/-- A step preserves fixedness: a coordinate fixed before the step stays fixed. -/
theorem actStep_fixed (cs : List (Clause n)) (σ : Restriction n) {j : Fin n}
    (h : σ j ≠ none) : actStep cs σ j ≠ none := by
  by_cases hc : ∀ ℓ, activeLit cs σ = some ℓ → j ≠ litVar ℓ
  · rw [actStep_eq_outside cs σ hc]; exact h
  · push_neg at hc
    obtain ⟨ℓ, hℓ, hjv⟩ := hc
    rw [actStep, hℓ, hjv]
    simp [falFix, Function.update_self]

/-- Selected coordinates are fixed along the path. -/
theorem actPath_fixed (cs : List (Clause n)) (ρ : Restriction n) :
    ∀ k, ∀ j ∈ actSel cs ρ k, actPath cs ρ k j ≠ none := by
  intro k
  induction k with
  | zero => intro j hj; simp [actSel] at hj
  | succ k ih =>
    intro j hj
    rw [actPath]
    cases hal : activeLit cs (actPath cs ρ k) with
    | none =>
      rw [actSel_succ_none hal] at hj
      rw [actStep, hal]; exact ih j hj
    | some ℓ =>
      rw [actSel_succ_some hal, Finset.mem_insert] at hj
      rcases hj with rfl | hj'
      · rw [actStep, hal]; simp [falFix, Function.update_self]
      · exact actStep_fixed cs (actPath cs ρ k) (ih j hj')

/-- **The path literals have distinct variables.**  A new step's variable is free, hence
not among the already-fixed selected coordinates. -/
theorem pathLits_nodup_litVar (cs : List (Clause n)) (ρ : Restriction n) (s : ℕ) :
    ((pathLits cs ρ s).map litVar).Nodup := by
  induction s with
  | zero => simp [pathLits]
  | succ k ih =>
    cases hal : activeLit cs (actPath cs ρ k) with
    | none =>
      have hpl : pathLits cs ρ (k + 1) = pathLits cs ρ k := by simp only [pathLits, hal]
      rw [hpl]; exact ih
    | some ℓ =>
      have hpl : pathLits cs ρ (k + 1) = ℓ :: pathLits cs ρ k := by simp only [pathLits, hal]
      rw [hpl, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih⟩
      intro hmem
      obtain ⟨ℓ', hℓ', hvar⟩ := List.mem_map.mp hmem
      have h1 : litVar ℓ' ∈ actSel cs ρ k := pathLits_litVar_mem_actSel cs ρ k ℓ' hℓ'
      rw [hvar] at h1
      have hfixed := actPath_fixed cs ρ k (litVar ℓ) h1
      have hfree : Depth3.litFree (actPath cs ρ k) ℓ = true := activeLit_free hal
      rw [litFree_var] at hfree
      exact hfixed (Option.isNone_iff_eq_none.mp hfree)

end SwitchingCounting

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SwitchingCounting.pathLits_nodup_litVar
