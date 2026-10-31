import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3NonEmptyGates

/-!
# Tight switching, step 89: the merge does not increase the bottom-gate count (branch `razborov-recoverRho-wip`)

The merge half of the gate-count invariant.  On a non-empty-gates tower (step 88), `mergePass` does not
increase the bottom-gate count: a uniform sibling list `gs` (all `cnf` / all `dnf`) collapses to a single
bottom gate (`|gs| → 1`, a reduction since `|gs| ≥ 1`), and internal nodes recurse.

* `bottomGates_length_pos_NEG` — a non-empty-gates tower has a bottom gate.
* `mergePass_count_le` — `count (mergePass C) ≤ count C` on non-empty-gates towers.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- A non-empty-gates tower has at least one bottom gate. -/
theorem bottomGates_length_pos_NEG {C : Layered n} (h : NonEmptyGates C) :
    1 ≤ (bottomGates C).length := by
  induction h with
  | dnf cs => rw [show bottomGates (dnf cs) = [cs] from rfl]; simp
  | cnf cs => rw [show bottomGates (cnf cs) = [cs] from rfl]; simp
  | gAnd gs hne _ ih =>
      obtain ⟨g₀, gs', rfl⟩ := List.exists_cons_of_ne_nil hne
      rw [bottomGates_gAnd, bottomGatesList, List.length_append]
      have := ih g₀ (by simp)
      omega
  | gOr gs hne _ ih =>
      obtain ⟨g₀, gs', rfl⟩ := List.exists_cons_of_ne_nil hne
      rw [bottomGates_gOr, bottomGatesList, List.length_append]
      have := ih g₀ (by simp)
      omega

-- mergePass_count_le: the merge does not increase the bottom-gate count (mutual with the list form).
mutual
theorem mergePass_count_le :
    ∀ {C : Layered n}, NonEmptyGates C → (bottomGates (mergePass C)).length ≤ (bottomGates C).length
  | dnf _, _ => le_refl _
  | cnf _, _ => le_refl _
  | gAnd gs, hC => by
      cases hcnf : allCnf gs with
      | some css =>
          rw [show mergePass (gAnd gs) = cnf css.flatten from by simp only [mergePass, hcnf],
            show bottomGates (cnf css.flatten) = [css.flatten] from rfl, List.length_singleton]
          exact bottomGates_length_pos_NEG hC
      | none =>
          rw [show mergePass (gAnd gs) = gAnd (mergePassList gs) from by simp only [mergePass, hcnf],
            bottomGates_gAnd, bottomGates_gAnd]
          cases hC with
          | gAnd _ _ h => exact mergePassList_count_le gs h
  | gOr gs, hC => by
      cases hdnf : allDnf gs with
      | some dss =>
          rw [show mergePass (gOr gs) = dnf dss.flatten from by simp only [mergePass, hdnf],
            show bottomGates (dnf dss.flatten) = [dss.flatten] from rfl, List.length_singleton]
          exact bottomGates_length_pos_NEG hC
      | none =>
          rw [show mergePass (gOr gs) = gOr (mergePassList gs) from by simp only [mergePass, hdnf],
            bottomGates_gOr, bottomGates_gOr]
          cases hC with
          | gOr _ _ h => exact mergePassList_count_le gs h
theorem mergePassList_count_le :
    ∀ (gs : List (Layered n)), (∀ g ∈ gs, NonEmptyGates g) →
      (bottomGatesList (mergePassList gs)).length ≤ (bottomGatesList gs).length
  | [], _ => le_refl _
  | g :: gs, h => by
      rw [mergePassList, bottomGatesList, bottomGatesList, List.length_append, List.length_append]
      have h1 := mergePass_count_le (h g (by simp))
      have h2 := mergePassList_count_le gs (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
      omega
end

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.mergePass_count_le
