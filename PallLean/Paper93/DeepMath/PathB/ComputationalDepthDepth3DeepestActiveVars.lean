import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DeepestActiveId
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PureSatisfyConfine

/-!
# General confinement: selected variables live in the active clauses

The pure-satisfy confinement (`deepestSatSel_subset_clauseVars`) pinned the selected set inside one
constant clause.  The general analog, proved here: **every** selected variable lies in a clause that
is active at *some* state along the branch.

Combined with `deepest_falsified_clause_active` (a clause falsified at the leaf was active at some
state), this is the general structural picture the backward decoder works with: the selected
variables are distributed across the active clauses, and the active clauses that get *completed* are
exactly the clauses falsified at the leaf — both ends readable from the end-state.

* `deepestSel_mem_active_clause` — every `v ∈ deepestSel` lies in `clauseVars C` for some clause `C`
  active at a reached state.

(The complementary direction — that an active clause *not* falsified at the leaf is precisely the
leaf's own active clause — needs step-indexed branch states and is **not** proved here; not faked.)
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace Depth3

open SwitchingCounting

variable {n : ℕ}

/-- **General confinement.**  Every selected variable lies in `clauseVars C` for some clause `C` that
is active at a reached state `τ`.  (From `mem_deepestSel`: the variable is the active literal's
variable there, and that literal lies in the active clause.)  This is the general analog of the
pure-satisfy single-clause confinement `deepestSatSel_subset_clauseVars`. -/
theorem deepestSel_mem_active_clause (cs : List (Clause n)) (F : ℕ) (σ : Fin n → Option Bool)
    {v : Fin n} (hv : v ∈ deepestSel cs F σ) :
    ∃ C, (∃ τ, SwitchingCounting.activeTerm cs τ = some C) ∧ v ∈ clauseVars C := by
  obtain ⟨τ, C, ℓ, hactτ, hatlτ, hℓv⟩ := mem_deepestSel cs F σ v hv
  have hℓC : ℓ ∈ C.lits := by
    unfold SwitchingCounting.activeTermLit at hatlτ; rw [hactτ] at hatlτ
    exact (List.mem_filter.mp (List.mem_of_mem_head? hatlτ)).1
  exact ⟨C, ⟨τ, hactτ⟩, hℓv ▸ mem_clauseVars hℓC⟩

end Depth3

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.deepestSel_mem_active_clause
