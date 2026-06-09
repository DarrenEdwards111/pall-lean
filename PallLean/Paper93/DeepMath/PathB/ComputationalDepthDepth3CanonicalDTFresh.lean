import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseAdapter
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TreeBridge
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FreshClauses
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3StarShell
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DepthReplayTie

/-!
# Tight switching, step 76: freshness of the canonical binary tree (branch `razborov-recoverRho-wip`)

`leafCollapse` switches a bottom gate by `toDTree (canonicalDT cs F ρ)` — the *binary* canonical tree (queries
one variable at a time), distinct from the `DTree`-valued `canonicalDTree` (queries a whole term at once).  The
freshness machinery (`canonicalDTree_fresh`) covers only the latter, so we prove freshness for the binary tree
directly: `canonicalDT` never re-queries a fixed variable (`canonicalDT_queriedVars_subset_free`), so along any
path each query variable is fixed thereafter — hence `toDTree (canonicalDT cs F ρ)` is `fresh`.  This is the
input the switched-gate consistency/nodup lemmas (`dtreeToDNF_consistent`/`_nodup`,
`dtreeToCNF_consistent`/`_nodup`) need, so it sets the `BottomClean` invariant.

* `toDTree_queriedVars` — `toDTree` preserves the queried-variable set.
* `toDTree_canonicalDT_fresh` — the canonical binary tree is fresh.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting

variable {n : ℕ}

/-- `toDTree` preserves the queried-variable set. -/
theorem toDTree_queriedVars (t : BoolDecisionTree n) :
    DTree.queriedVars (toDTree t) = queriedVars t := by
  induction t with
  | leaf b => rfl
  | query i lo hi ihlo ihhi =>
    simp only [toDTree, DTree.queriedVars, queriedVars, ihlo, ihhi]

/-- **The canonical binary tree is fresh.**  `canonicalDT` never re-queries a variable already fixed, so no
variable is queried twice along any path. -/
theorem toDTree_canonicalDT_fresh (cs : List (Clause n)) :
    ∀ (fuel : ℕ) (σ : Fin n → Option Bool), (toDTree (canonicalDT cs fuel σ)).fresh := by
  intro fuel
  induction fuel with
  | zero =>
    intro σ
    rw [canonicalDT]
    split <;> trivial
  | succ fuel ih =>
    intro σ
    rw [canonicalDT]
    by_cases hany : SwitchingCounting.anyTermSat cs σ = true
    · rw [if_pos hany]; trivial
    · rw [if_neg hany]
      split
      · trivial
      · split
        · trivial
        · simp only [toDTree]
          refine ⟨?_, ?_, ih _, ih _⟩
          · rw [toDTree_queriedVars]
            intro hmem
            have hsub := canonicalDT_queriedVars_subset_free cs fuel _ hmem
            rw [freeVars_fixVar] at hsub
            exact (Finset.mem_erase.mp hsub).1 rfl
          · rw [toDTree_queriedVars]
            intro hmem
            have hsub := canonicalDT_queriedVars_subset_free cs fuel _ hmem
            rw [freeVars_fixVar] at hsub
            exact (Finset.mem_erase.mp hsub).1 rfl

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.toDTree_canonicalDT_fresh
