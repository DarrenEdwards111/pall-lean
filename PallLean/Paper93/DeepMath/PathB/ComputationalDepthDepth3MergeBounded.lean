import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3MergePass
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LeafCollapseBounded

/-!
# Tight switching, step 56: the merge preserves the bottom-gate width (branch `razborov-recoverRho-wip`)

The merge half of the width-aware reduction.  Only the *width* needs threading through the rounds (the
clause-count is read off the final `DNF`, since `hsmall` stays a hypothesis and `p = 1/(8w·count)` makes the
rate `hr1` hold at any count).  `mergePass` flattens a uniform `gAnd`-of-`cnf` (`gOr`-of-`dnf`) into one
bottom gate whose terms are exactly the children's terms — so the width is the max of the children's widths,
hence preserved.  Internal nodes recurse.

* `BottomWidth` — every bottom gate has width `≤ w` (the width projection of `BottomBounded`).
* `mergePass_BottomWidth` — the merge preserves the bottom-gate width bound.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

theorem bottomGates_gAnd (gs : List (Layered n)) : bottomGates (gAnd gs) = bottomGatesList gs := rfl
theorem bottomGates_gOr (gs : List (Layered n)) : bottomGates (gOr gs) = bottomGatesList gs := rfl

/-- **The width invariant.**  Every bottom gate of `C` has width `≤ w` (the width projection of
`BottomBounded`). -/
def BottomWidth (w : ℕ) (C : Layered n) : Prop :=
  ∀ cs ∈ bottomGates C, ∀ T ∈ cs, T.lits.length ≤ w

/-- `BottomBounded` forgets to `BottomWidth`. -/
theorem BottomBounded_BottomWidth {w M : ℕ} {C : Layered n} (h : BottomBounded w M C) :
    BottomWidth w C :=
  fun cs hcs T hT => (h cs hcs).1 T hT

/-- A node's width bound projects to each child. -/
theorem BottomWidth_child_gAnd {w : ℕ} {gs : List (Layered n)} {g : Layered n}
    (h : BottomWidth w (gAnd gs)) (hg : g ∈ gs) : BottomWidth w g := by
  intro cs hcs T hT
  refine h cs ?_ T hT
  rw [bottomGates_gAnd, bottomGatesList_eq, List.mem_flatten]
  exact ⟨bottomGates g, by rw [List.mem_map]; exact ⟨g, hg, rfl⟩, hcs⟩

/-- Dual for `gOr`. -/
theorem BottomWidth_child_gOr {w : ℕ} {gs : List (Layered n)} {g : Layered n}
    (h : BottomWidth w (gOr gs)) (hg : g ∈ gs) : BottomWidth w g := by
  intro cs hcs T hT
  refine h cs ?_ T hT
  rw [bottomGates_gOr, bottomGatesList_eq, List.mem_flatten]
  exact ⟨bottomGates g, by rw [List.mem_map]; exact ⟨g, hg, rfl⟩, hcs⟩

-- mergePass_BottomWidth: the merge preserves the bottom-gate width (flattening keeps every term's width =
-- max of children's; internal nodes recurse). Mutual with the list version.
mutual
theorem mergePass_BottomWidth {w : ℕ} :
    ∀ {C : Layered n}, BottomWidth w C → BottomWidth w (mergePass C)
  | dnf _, h => h
  | cnf _, h => h
  | gAnd gs, h => by
      cases hcnf : allCnf gs with
      | some css =>
          have hgs := allCnf_some hcnf
          have hmp : mergePass (gAnd gs) = cnf css.flatten := by simp only [mergePass, hcnf]
          rw [hmp]
          intro cs' hcs' T hT
          rw [show bottomGates (cnf css.flatten) = [css.flatten] from rfl, List.mem_singleton] at hcs'
          subst hcs'
          obtain ⟨c, hc, hTc⟩ := List.mem_flatten.mp hT
          have hchild : BottomWidth w (cnf c) :=
            BottomWidth_child_gAnd h (by rw [hgs, List.mem_map]; exact ⟨c, hc, rfl⟩)
          exact hchild c (by rw [show bottomGates (cnf c) = [c] from rfl]; simp) T hTc
      | none =>
          have hmp : mergePass (gAnd gs) = gAnd (mergePassList gs) := by simp only [mergePass, hcnf]
          rw [hmp]
          intro cs' hcs' T hT
          rw [bottomGates_gAnd, bottomGatesList_eq, mergePassList_eq, List.map_map,
            List.mem_flatten] at hcs'
          obtain ⟨l, hl, hcsl⟩ := hcs'
          rw [List.mem_map] at hl
          obtain ⟨g, hg, rfl⟩ := hl
          exact mergePassList_BottomWidth gs (fun g' hg' => BottomWidth_child_gAnd h hg') g hg
            cs' hcsl T hT
  | gOr gs, h => by
      cases hdnf : allDnf gs with
      | some dss =>
          have hgs := allDnf_some hdnf
          have hmp : mergePass (gOr gs) = dnf dss.flatten := by simp only [mergePass, hdnf]
          rw [hmp]
          intro cs' hcs' T hT
          rw [show bottomGates (dnf dss.flatten) = [dss.flatten] from rfl, List.mem_singleton] at hcs'
          subst hcs'
          obtain ⟨c, hc, hTc⟩ := List.mem_flatten.mp hT
          have hchild : BottomWidth w (dnf c) :=
            BottomWidth_child_gOr h (by rw [hgs, List.mem_map]; exact ⟨c, hc, rfl⟩)
          exact hchild c (by rw [show bottomGates (dnf c) = [c] from rfl]; simp) T hTc
      | none =>
          have hmp : mergePass (gOr gs) = gOr (mergePassList gs) := by simp only [mergePass, hdnf]
          rw [hmp]
          intro cs' hcs' T hT
          rw [bottomGates_gOr, bottomGatesList_eq, mergePassList_eq, List.map_map,
            List.mem_flatten] at hcs'
          obtain ⟨l, hl, hcsl⟩ := hcs'
          rw [List.mem_map] at hl
          obtain ⟨g, hg, rfl⟩ := hl
          exact mergePassList_BottomWidth gs (fun g' hg' => BottomWidth_child_gOr h hg') g hg
            cs' hcsl T hT
theorem mergePassList_BottomWidth {w : ℕ} :
    ∀ (gs : List (Layered n)), (∀ g ∈ gs, BottomWidth w g) →
      ∀ g ∈ gs, BottomWidth w (mergePass g)
  | [], _ => fun g hg => by simp at hg
  | g₀ :: gs, hall => fun g hg => by
      rcases List.mem_cons.mp hg with rfl | h
      · exact mergePass_BottomWidth (hall g (by simp))
      · exact mergePassList_BottomWidth gs (fun g' hg' => hall g' (List.mem_cons_of_mem _ hg')) g h
end

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.mergePass_BottomWidth
