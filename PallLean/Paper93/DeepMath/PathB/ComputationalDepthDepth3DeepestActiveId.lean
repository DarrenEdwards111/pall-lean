import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestFalsifyPart
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingReadOnceId

/-!
# General active-clause identification at the deepest leaf (read-once)

Beyond the pure-satisfy regime, the general interleaved branch needs to recover, from the
non-satisfying leaf, *which* clauses were active.  This file proves the structural backbone, the
deepest-branch analog of `SwitchingCounting.falsified_clause_is_active`:

* `deepestEnd_eq_of_fixed` — the deepest branch only fixes *free* variables, so any `ρ`-fixed variable
  keeps its value at the leaf.
* `mem_deepestSel` — every selected variable is the active literal's variable at *some* state reached
  along the branch (each `deepestSel` insertion is the step's active literal).
* `deepest_falsified_clause_active` — **the identification**: under read-once and "ρ falsifies
  nothing", a clause falsified at the deepest leaf was the active clause at some state.  Its false
  literal's variable is path-selected (not `ρ`-fixed), hence some step's active-literal variable, and
  read-once pins the unique clause containing it to be that step's active clause.

So the falsified-at-leaf clauses are exactly the (read-once) active clauses — the enumeration the
general backward decoder needs.  This does **not** yet sequence the satisfy positions within each
clause across the falsify steps (the remaining open core), and is **not** faked.
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **The deepest branch preserves fixed variables.**  Each step fixes the active literal's variable,
which is free; so a variable already fixed in `σ` keeps its value at the leaf. -/
theorem deepestEnd_eq_of_fixed (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (v : Fin n) (b : Bool),
      σ v = some b → deepestEnd cs F σ v = some b := by
  intro F
  induction F with
  | zero => intro σ v b h; exact h
  | succ F ih =>
    intro σ v b h
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => rw [deepestEnd]; simp only [hany, if_true]; exact h
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none => rw [deepestEnd]; simp only [hany, Bool.false_eq_true, if_false, hact]; exact h
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none =>
          rw [deepestEnd]; simp only [hany, Bool.false_eq_true, if_false, hact, hh]; exact h
        | some ℓ =>
          have hatl : SwitchingCounting.activeTermLit cs σ = some ℓ := by
            unfold SwitchingCounting.activeTermLit; rw [hact]; exact hh
          have hfree : σ (litVar ℓ) = none := activeTermLit_var_free hatl
          have hvne : v ≠ litVar ℓ := fun he => by rw [he, hfree] at h; exact absurd h (by simp)
          have hstep : ∀ bit, fixVar σ (litVar ℓ) bit v = some b := fun bit => by
            rw [fixVar, Function.update_of_ne hvne]; exact h
          rw [deepestEnd]
          simp only [hany, Bool.false_eq_true, if_false, hact, hh]
          split
          · exact ih _ v b (hstep false)
          · exact ih _ v b (hstep true)

/-- **Every selected variable is some state's active-literal variable.**  Each `deepestSel` insertion
records the active literal at the current state; so any `v ∈ deepestSel` is `litVar ℓ` for the active
literal `ℓ` of the active clause `C` at some reached state `τ`. -/
theorem mem_deepestSel (cs : List (Clause n)) :
    ∀ (F : ℕ) (σ : Fin n → Option Bool) (v : Fin n),
      v ∈ deepestSel cs F σ →
      ∃ τ C ℓ, SwitchingCounting.activeTerm cs τ = some C ∧
        SwitchingCounting.activeTermLit cs τ = some ℓ ∧ litVar ℓ = v := by
  intro F
  induction F with
  | zero => intro σ v hv; rw [deepestSel] at hv; exact absurd hv (by simp)
  | succ F ih =>
    intro σ v hv
    cases hany : SwitchingCounting.anyTermSat cs σ with
    | true => rw [deepestSel] at hv; simp only [hany, if_true] at hv; exact absurd hv (by simp)
    | false =>
      cases hact : SwitchingCounting.activeTerm cs σ with
      | none =>
        rw [deepestSel] at hv; simp only [hany, Bool.false_eq_true, if_false, hact] at hv
        exact absurd hv (by simp)
      | some T =>
        cases hh : (SwitchingCounting.freeLits σ T).head? with
        | none =>
          rw [deepestSel] at hv
          simp only [hany, Bool.false_eq_true, if_false, hact, hh] at hv
          exact absurd hv (by simp)
        | some ℓ =>
          have hatl : SwitchingCounting.activeTermLit cs σ = some ℓ := by
            unfold SwitchingCounting.activeTermLit; rw [hact]; exact hh
          rw [deepestSel] at hv
          simp only [hany, Bool.false_eq_true, if_false, hact, hh] at hv
          -- both depth-branches insert `litVar ℓ` into the recursive selected set
          have hcase : v = litVar ℓ ∨ ∃ b : Bool, v ∈ deepestSel cs F (fixVar σ (litVar ℓ) b) := by
            split at hv <;> (rw [Finset.mem_insert] at hv; rcases hv with h | h)
            · exact Or.inl h
            · exact Or.inr ⟨false, h⟩
            · exact Or.inl h
            · exact Or.inr ⟨true, h⟩
          rcases hcase with h | ⟨b, h⟩
          · exact ⟨σ, T, ℓ, hact, hatl, h.symm⟩
          · exact ih _ v h

/-- **The identification (read-once).**  Under read-once and "ρ falsifies nothing", a clause falsified
at the deepest leaf was the active clause at some state along the branch. -/
theorem deepest_falsified_clause_active (cs : List (Clause n)) (hro : SwitchingCounting.ReadOnce cs)
    {ρ : Fin n → Option Bool} (hnf : ∀ T ∈ cs, SwitchingCounting.termFalsified ρ T = false)
    {C : Clause n} (hC : C ∈ cs) {F : ℕ}
    (hfals : SwitchingCounting.termFalsified (deepestEnd cs F ρ) C = true) :
    ∃ τ, SwitchingCounting.activeTerm cs τ = some C := by
  rw [SwitchingCounting.termFalsified, List.any_eq_true] at hfals
  obtain ⟨m, hmC, hmf⟩ := hfals
  -- ρ does not fix `litVar m` (else `m` is false under ρ, falsifying C)
  have hρnone : ρ (litVar m) = none := by
    by_contra hne
    obtain ⟨b', hb'⟩ := Option.ne_none_iff_exists'.mp hne
    have hstab : deepestEnd cs F ρ (litVar m) = some b' := deepestEnd_eq_of_fixed cs F ρ _ b' hb'
    have heq : ρ (litVar m) = deepestEnd cs F ρ (litVar m) := by rw [hb', hstab]
    have hfρ : SwitchingCounting.litFalse ρ m = true := by
      rw [SwitchingCounting.litFalse_eq_of_litVar_val heq]; exact hmf
    have hcf : SwitchingCounting.termFalsified ρ C = true := by
      rw [SwitchingCounting.termFalsified, List.any_eq_true]; exact ⟨m, hmC, hfρ⟩
    rw [hnf C hC] at hcf; exact absurd hcf (by simp)
  -- so `litVar m` is path-selected
  have hmem : litVar m ∈ deepestSel cs F ρ := by
    by_contra hnotin
    have hout := deepestEnd_eq_outside cs F ρ hnotin
    rw [hρnone] at hout
    exact litFalse_litVar_fixed hmf hout
  obtain ⟨τ, C', ℓ', hactτ, hatlτ, hℓ'v⟩ := mem_deepestSel cs F ρ (litVar m) hmem
  -- recover ℓ' ∈ C'.lits and C' ∈ cs
  have hℓ'C' : ℓ' ∈ C'.lits := by
    unfold SwitchingCounting.activeTermLit at hatlτ; rw [hactτ] at hatlτ
    exact (List.mem_filter.mp (List.mem_of_mem_head? hatlτ)).1
  have hC'mem : C' ∈ cs := SwitchingCounting.activeTerm_mem hactτ
  -- read-once: `C` and `C'` share variable `litVar m`, so `C = C'`
  have hCC' : C = C' := hro (litVar m) C C' hC hC'mem ⟨m, hmC, rfl⟩ ⟨ℓ', hℓ'C', hℓ'v⟩
  exact ⟨τ, hCC' ▸ hactτ⟩

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestEnd_eq_of_fixed
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.mem_deepestSel
#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepest_falsified_clause_active
