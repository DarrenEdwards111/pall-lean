import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3BottomClean
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonicalDTFresh
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DnfFresh
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FreshClauses

/-!
# Tight switching, step 77: the leafCollapse-tower BottomClean setter (branch `razborov-recoverRho-wip`)

`leafCollapse` switches every bottom gate into the clauses of a canonical decision tree, which — being on a
*fresh* tree (step 76) — are automatically `Consistent` and variable-`Nodup` (`dtreeToCNF_consistent/_nodup`,
`dtreeToDNF_consistent/_nodup`).  So a leaf-collapse **sets** the `BottomClean` invariant *unconditionally*: no
hypothesis on the input tower is needed, because the switched gates are clean by construction.  (Contrast
`BottomWidth`, which the switch only sets below the survivor threshold.)

* `leafCollapse_BottomPred` — any per-clause predicate holding on both switched-gate shapes propagates through
  the tower.
* `leafCollapse_BottomClean` — `BottomClean (leafCollapse F ρ C)` for every `C`.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

-- leafCollapse_BottomPred: a per-clause P holding on both switched-gate shapes propagates through the tower.
-- Mutual with the list version.
mutual
theorem leafCollapse_BottomPred {P : Clause n → Prop} (F : ℕ) (ρ : Fin n → Option Bool)
    (hdnf : ∀ (cs : List (Clause n)), ∀ T ∈ dtreeToCNF (toDTree (canonicalDT cs F ρ)), P T)
    (hcnf : ∀ (cs : List (Clause n)),
      ∀ T ∈ dtreeToDNF (DTree.negTree (toDTree (canonicalDT (negDNF cs) F ρ))), P T) :
    ∀ C : Layered n, BottomPred P (leafCollapse F ρ C)
  | dnf cs => by
      intro cs' hcs' T hT
      rw [show leafCollapse F ρ (dnf cs) = cnf (dtreeToCNF (toDTree (canonicalDT cs F ρ))) from rfl,
        show bottomGates (cnf (dtreeToCNF (toDTree (canonicalDT cs F ρ))))
            = [dtreeToCNF (toDTree (canonicalDT cs F ρ))] from rfl, List.mem_singleton] at hcs'
      subst hcs'
      exact hdnf cs T hT
  | cnf cs => by
      intro cs' hcs' T hT
      rw [show leafCollapse F ρ (cnf cs)
            = dnf (dtreeToDNF (DTree.negTree (toDTree (canonicalDT (negDNF cs) F ρ)))) from rfl,
        show bottomGates (dnf (dtreeToDNF (DTree.negTree (toDTree (canonicalDT (negDNF cs) F ρ)))))
            = [dtreeToDNF (DTree.negTree (toDTree (canonicalDT (negDNF cs) F ρ)))] from rfl,
        List.mem_singleton] at hcs'
      subst hcs'
      exact hcnf cs T hT
  | gAnd gs => by
      show BottomPred P (gAnd (leafCollapseList F ρ gs))
      intro cs' hcs' T hT
      rw [bottomGates_gAnd, bottomGatesList_eq, leafCollapseList_eq, List.map_map,
        List.mem_flatten] at hcs'
      obtain ⟨l, hl, hcsl⟩ := hcs'
      rw [List.mem_map] at hl
      obtain ⟨g, hg, rfl⟩ := hl
      exact leafCollapseList_BottomPred F ρ hdnf hcnf gs g hg cs' hcsl T hT
  | gOr gs => by
      show BottomPred P (gOr (leafCollapseList F ρ gs))
      intro cs' hcs' T hT
      rw [bottomGates_gOr, bottomGatesList_eq, leafCollapseList_eq, List.map_map,
        List.mem_flatten] at hcs'
      obtain ⟨l, hl, hcsl⟩ := hcs'
      rw [List.mem_map] at hl
      obtain ⟨g, hg, rfl⟩ := hl
      exact leafCollapseList_BottomPred F ρ hdnf hcnf gs g hg cs' hcsl T hT
theorem leafCollapseList_BottomPred {P : Clause n → Prop} (F : ℕ) (ρ : Fin n → Option Bool)
    (hdnf : ∀ (cs : List (Clause n)), ∀ T ∈ dtreeToCNF (toDTree (canonicalDT cs F ρ)), P T)
    (hcnf : ∀ (cs : List (Clause n)),
      ∀ T ∈ dtreeToDNF (DTree.negTree (toDTree (canonicalDT (negDNF cs) F ρ))), P T) :
    ∀ (gs : List (Layered n)), ∀ g ∈ gs, BottomPred P (leafCollapse F ρ g)
  | [], g, hg => by simp at hg
  | g₀ :: gs, g, hg => by
      rcases List.mem_cons.mp hg with rfl | h
      · exact leafCollapse_BottomPred F ρ hdnf hcnf g
      · exact leafCollapseList_BottomPred F ρ hdnf hcnf gs g h
end

/-- **The leafCollapse-tower `BottomClean` setter.**  After a leaf collapse, every bottom gate is `Consistent`
and variable-`Nodup` — the switched gates are clauses of fresh canonical trees.  No hypothesis on the input. -/
theorem leafCollapse_BottomClean (F : ℕ) (ρ : Fin n → Option Bool) (C : Layered n) :
    BottomClean (leafCollapse F ρ C) :=
  ⟨leafCollapse_BottomPred F ρ
      (fun cs T hT => dtreeToCNF_consistent _ (toDTree_canonicalDT_fresh cs F ρ) T hT)
      (fun cs T hT => dtreeToDNF_consistent _
        (DTree.negTree_fresh _ (toDTree_canonicalDT_fresh (negDNF cs) F ρ)) T hT) C,
   leafCollapse_BottomPred F ρ
      (fun cs T hT => dtreeToCNF_nodup _ (toDTree_canonicalDT_fresh cs F ρ) T hT)
      (fun cs T hT => dtreeToDNF_nodup _
        (DTree.negTree_fresh _ (toDTree_canonicalDT_fresh (negDNF cs) F ρ)) T hT) C⟩

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.leafCollapse_BottomClean
