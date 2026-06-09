import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3MergeCount
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LeafTowerCount

/-!
# Tight switching, step 94: the merge multiplies the per-gate clause-count by the gate count (branch `razborov-recoverRho-wip`)

The merge-sum half of the clause-count invariant.  `mergePass` flattens a uniform sibling list into one
bottom gate whose clause-count is the *sum* of the siblings' — so it is bounded by `(gate count)·(per-gate
count)`.  Hence, on a non-empty-gates tower with `≤ M` bottom gates and per-gate clause-count `≤ c`, the merged
tower has per-gate clause-count `≤ M·c`.

* `mergePass_count_mul` — `BottomCount (M·c) (mergePass C)` from the gate count `≤ M` and `BottomCount c C`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

theorem bottomGates_gAnd_map_cnf_length (css : List (List (Clause n))) :
    (bottomGates (gAnd (css.map cnf))).length = css.length := by
  rw [bottomGates_gAnd, bottomGatesList_eq, List.map_map, List.length_flatten, List.map_map,
    show css.map (List.length ∘ bottomGates ∘ cnf) = css.map (fun _ => 1) from
      List.map_congr_left (fun c _ => rfl),
    List.map_const', List.sum_replicate, smul_eq_mul, mul_one]

theorem bottomGates_gOr_map_dnf_length (dss : List (List (Clause n))) :
    (bottomGates (gOr (dss.map dnf))).length = dss.length := by
  rw [bottomGates_gOr, bottomGatesList_eq, List.map_map, List.length_flatten, List.map_map,
    show dss.map (List.length ∘ bottomGates ∘ dnf) = dss.map (fun _ => 1) from
      List.map_congr_left (fun c _ => rfl),
    List.map_const', List.sum_replicate, smul_eq_mul, mul_one]

theorem count_le_of_mem_gAnd {gs : List (Layered n)} {g : Layered n} (hg : g ∈ gs) :
    (bottomGates g).length ≤ (bottomGates (gAnd gs)).length := by
  rw [bottomGates_gAnd, bottomGatesList_eq, List.length_flatten]
  refine List.single_le_sum (fun _ _ => Nat.zero_le _) _ ?_
  rw [List.mem_map]
  exact ⟨bottomGates g, by rw [List.mem_map]; exact ⟨g, hg, rfl⟩, rfl⟩

theorem count_le_of_mem_gOr {gs : List (Layered n)} {g : Layered n} (hg : g ∈ gs) :
    (bottomGates g).length ≤ (bottomGates (gOr gs)).length := by
  rw [bottomGates_gOr, bottomGatesList_eq, List.length_flatten]
  refine List.single_le_sum (fun _ _ => Nat.zero_le _) _ ?_
  rw [List.mem_map]
  exact ⟨bottomGates g, by rw [List.mem_map]; exact ⟨g, hg, rfl⟩, rfl⟩

theorem BottomCount_child_gAnd {c : ℕ} {gs : List (Layered n)} {g : Layered n}
    (h : BottomCount c (gAnd gs)) (hg : g ∈ gs) : BottomCount c g :=
  fun cs hcs => h cs (bottomGates_mem_gAnd hg hcs)

theorem BottomCount_child_gOr {c : ℕ} {gs : List (Layered n)} {g : Layered n}
    (h : BottomCount c (gOr gs)) (hg : g ∈ gs) : BottomCount c g :=
  fun cs hcs => h cs (bottomGates_mem_gOr hg hcs)

-- mergePass_count_mul: the merge bounds the per-gate clause-count by (gate count)·(input per-gate count).
-- Mutual with the list form.
mutual
theorem mergePass_count_mul {M c : ℕ} (hM1 : 1 ≤ M) :
    ∀ {C : Layered n}, NonEmptyGates C → (bottomGates C).length ≤ M → BottomCount c C →
      BottomCount (M * c) (mergePass C)
  | dnf _, _, _, hbc => by
      intro cs' hcs'
      have := hbc cs' hcs'
      calc cs'.length ≤ c := this
        _ ≤ M * c := Nat.le_mul_of_pos_left c hM1
  | cnf _, _, _, hbc => by
      intro cs' hcs'
      have := hbc cs' hcs'
      calc cs'.length ≤ c := this
        _ ≤ M * c := Nat.le_mul_of_pos_left c hM1
  | gAnd gs, hC, hcnt, hbc => by
      cases hcnf : allCnf gs with
      | some css =>
          have hgs := allCnf_some hcnf
          rw [show mergePass (gAnd gs) = cnf css.flatten from by simp only [mergePass, hcnf]]
          intro cs' hcs'
          rw [show bottomGates (cnf css.flatten) = [css.flatten] from rfl, List.mem_singleton] at hcs'
          subst hcs'
          -- |css.flatten| = sum |cᵢ| ≤ |css| · c ≤ M · c
          rw [List.length_flatten]
          have hbnd : ∀ x ∈ css.map List.length, x ≤ c := by
            intro x hx
            rw [List.mem_map] at hx
            obtain ⟨cᵢ, hci, rfl⟩ := hx
            refine hbc cᵢ ?_
            rw [bottomGates_gAnd, bottomGatesList_eq, hgs, List.map_map, List.mem_flatten]
            exact ⟨[cᵢ], by rw [List.mem_map]; exact ⟨cᵢ, hci, rfl⟩, by simp⟩
          have hsum := List.sum_le_card_nsmul (css.map List.length) c hbnd
          rw [List.length_map, smul_eq_mul] at hsum
          have hcsslen : css.length ≤ M := by
            have h := hcnt
            rw [hgs, bottomGates_gAnd_map_cnf_length] at h
            exact h
          calc (css.map List.length).sum ≤ css.length * c := hsum
            _ ≤ M * c := Nat.mul_le_mul_right c hcsslen
      | none =>
          rw [show mergePass (gAnd gs) = gAnd (mergePassList gs) from by simp only [mergePass, hcnf]]
          intro cs' hcs'
          rw [bottomGates_gAnd, bottomGatesList_eq, mergePassList_eq, List.map_map,
            List.mem_flatten] at hcs'
          obtain ⟨l, hl, hcsl⟩ := hcs'
          rw [List.mem_map] at hl
          obtain ⟨g, hg, rfl⟩ := hl
          cases hC with
          | gAnd _ _ hgC =>
            exact mergePassList_count_mul hM1 gs hgC (fun g' hg' => le_trans (count_le_of_mem_gAnd hg') hcnt)
              (fun g' hg' => BottomCount_child_gAnd hbc hg') g hg cs' hcsl
  | gOr gs, hC, hcnt, hbc => by
      cases hdnf : allDnf gs with
      | some dss =>
          have hgs := allDnf_some hdnf
          rw [show mergePass (gOr gs) = dnf dss.flatten from by simp only [mergePass, hdnf]]
          intro cs' hcs'
          rw [show bottomGates (dnf dss.flatten) = [dss.flatten] from rfl, List.mem_singleton] at hcs'
          subst hcs'
          rw [List.length_flatten]
          have hbnd : ∀ x ∈ dss.map List.length, x ≤ c := by
            intro x hx
            rw [List.mem_map] at hx
            obtain ⟨cᵢ, hci, rfl⟩ := hx
            refine hbc cᵢ ?_
            rw [bottomGates_gOr, bottomGatesList_eq, hgs, List.map_map, List.mem_flatten]
            exact ⟨[cᵢ], by rw [List.mem_map]; exact ⟨cᵢ, hci, rfl⟩, by simp⟩
          have hsum := List.sum_le_card_nsmul (dss.map List.length) c hbnd
          rw [List.length_map, smul_eq_mul] at hsum
          have hdsslen : dss.length ≤ M := by
            have h := hcnt
            rw [hgs, bottomGates_gOr_map_dnf_length] at h
            exact h
          calc (dss.map List.length).sum ≤ dss.length * c := hsum
            _ ≤ M * c := Nat.mul_le_mul_right c hdsslen
      | none =>
          rw [show mergePass (gOr gs) = gOr (mergePassList gs) from by simp only [mergePass, hdnf]]
          intro cs' hcs'
          rw [bottomGates_gOr, bottomGatesList_eq, mergePassList_eq, List.map_map,
            List.mem_flatten] at hcs'
          obtain ⟨l, hl, hcsl⟩ := hcs'
          rw [List.mem_map] at hl
          obtain ⟨g, hg, rfl⟩ := hl
          cases hC with
          | gOr _ _ hgC =>
            exact mergePassList_count_mul hM1 gs hgC (fun g' hg' => le_trans (count_le_of_mem_gOr hg') hcnt)
              (fun g' hg' => BottomCount_child_gOr hbc hg') g hg cs' hcsl
theorem mergePassList_count_mul {M c : ℕ} (hM1 : 1 ≤ M) :
    ∀ (gs : List (Layered n)), (∀ g ∈ gs, NonEmptyGates g) →
      (∀ g ∈ gs, (bottomGates g).length ≤ M) → (∀ g ∈ gs, BottomCount c g) →
      ∀ g ∈ gs, BottomCount (M * c) (mergePass g)
  | [], _, _, _ => fun g hg => by simp at hg
  | g₀ :: gs, hC, hcnt, hbc => fun g hg => by
      rcases List.mem_cons.mp hg with rfl | h
      · exact mergePass_count_mul hM1 (hC g (by simp)) (hcnt g (by simp)) (hbc g (by simp))
      · exact mergePassList_count_mul hM1 gs (fun g' hg' => hC g' (List.mem_cons_of_mem _ hg'))
          (fun g' hg' => hcnt g' (List.mem_cons_of_mem _ hg'))
          (fun g' hg' => hbc g' (List.mem_cons_of_mem _ hg')) g h
end

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.mergePass_count_mul
