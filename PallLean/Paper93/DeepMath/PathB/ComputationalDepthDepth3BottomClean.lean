import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3MergeBounded
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SatEncode
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonicalTree

/-!
# Tight switching, step 75: the consistency/nodup bottom-gate invariant (branch `razborov-recoverRho-wip`)

The relative survivor budget (`descent_switching_le_extends`, step 74) carries two extra per-gate hypotheses
beyond width: each bottom clause must be `Consistent` (no `v` and `¬v`) and variable-`Nodup`.  These are
exactly the shape the switched bottom gates have (`dtreeToDNF`/`dtreeToCNF` of the *fresh* canonical trees:
`dtreeToDNF_consistent`/`dtreeToDNF_nodup`), so they are an invariant to thread, just like `BottomWidth`.

We abstract the pattern: a per-clause predicate `P` lifted to all bottom gates (`BottomPred P`) is preserved by
the merge pass (flattening keeps the clauses themselves), and `BottomClean` is the conjunction of
`Consistent` and variable-`Nodup`.

* `BottomPred` / `mergePass_BottomPred` — any per-clause invariant survives the merge.
* `BottomClean` / `mergePass_BottomClean` — the consistency + nodup invariant survives the merge.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

/-- A per-clause predicate `P` holding on every bottom gate of `C`. -/
def BottomPred (P : Clause n → Prop) (C : Layered n) : Prop :=
  ∀ cs ∈ bottomGates C, ∀ T ∈ cs, P T

theorem BottomPred_child_gAnd {P : Clause n → Prop} {gs : List (Layered n)} {g : Layered n}
    (h : BottomPred P (gAnd gs)) (hg : g ∈ gs) : BottomPred P g := by
  intro cs hcs T hT
  refine h cs ?_ T hT
  rw [bottomGates_gAnd, bottomGatesList_eq, List.mem_flatten]
  exact ⟨bottomGates g, by rw [List.mem_map]; exact ⟨g, hg, rfl⟩, hcs⟩

theorem BottomPred_child_gOr {P : Clause n → Prop} {gs : List (Layered n)} {g : Layered n}
    (h : BottomPred P (gOr gs)) (hg : g ∈ gs) : BottomPred P g := by
  intro cs hcs T hT
  refine h cs ?_ T hT
  rw [bottomGates_gOr, bottomGatesList_eq, List.mem_flatten]
  exact ⟨bottomGates g, by rw [List.mem_map]; exact ⟨g, hg, rfl⟩, hcs⟩

-- mergePass_BottomPred: any per-clause invariant P survives the merge (flatten keeps the clauses). Mutual.
mutual
theorem mergePass_BottomPred {P : Clause n → Prop} :
    ∀ {C : Layered n}, BottomPred P C → BottomPred P (mergePass C)
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
          have hchild : BottomPred P (cnf c) :=
            BottomPred_child_gAnd h (by rw [hgs, List.mem_map]; exact ⟨c, hc, rfl⟩)
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
          exact mergePassList_BottomPred gs (fun g' hg' => BottomPred_child_gAnd h hg') g hg
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
          have hchild : BottomPred P (dnf c) :=
            BottomPred_child_gOr h (by rw [hgs, List.mem_map]; exact ⟨c, hc, rfl⟩)
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
          exact mergePassList_BottomPred gs (fun g' hg' => BottomPred_child_gOr h hg') g hg
            cs' hcsl T hT
theorem mergePassList_BottomPred {P : Clause n → Prop} :
    ∀ (gs : List (Layered n)), (∀ g ∈ gs, BottomPred P g) →
      ∀ g ∈ gs, BottomPred P (mergePass g)
  | [], _ => fun g hg => by simp at hg
  | g₀ :: gs, hall => fun g hg => by
      rcases List.mem_cons.mp hg with rfl | h
      · exact mergePass_BottomPred (hall g (by simp))
      · exact mergePassList_BottomPred gs (fun g' hg' => hall g' (List.mem_cons_of_mem _ hg')) g h
end

/-- **The consistency/nodup bottom-gate invariant.**  Every bottom clause is `Consistent` and has
variable-`Nodup` literals — the extra per-gate hypotheses the relative switching budget needs. -/
def BottomClean (C : Layered n) : Prop :=
  BottomPred Consistent C ∧ BottomPred (fun T => (T.lits.map litVarOf).Nodup) C

/-- **The merge preserves the consistency/nodup invariant.** -/
theorem mergePass_BottomClean {C : Layered n} (h : BottomClean C) : BottomClean (mergePass C) :=
  ⟨mergePass_BottomPred h.1, mergePass_BottomPred h.2⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.mergePass_BottomClean
