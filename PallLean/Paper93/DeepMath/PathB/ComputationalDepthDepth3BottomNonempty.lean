import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3AltReduce
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3MergeBounded

/-!
# Tight switching, step 87: an alternating tower has a bottom gate (branch `razborov-recoverRho-wip`)

The gate-count reduction (the merge half of step 86) needs the `gAnd []`/`gOr []` degeneracy excluded — for a
proper alternating tower (`AltO`/`AltA`, whose gates are non-empty) the bottom-gate list is non-empty, so the
merge's collapse `|gs| → 1` is a genuine *reduction* (`1 ≤ |gs|`).  Here that foundation: every `AltO`/`AltA`
tower has at least one bottom gate.

* `bottomGates_length_pos_AltO` / `_AltA` — `1 ≤ (bottomGates C).length` for alternating towers.

Clean, no `sorry`, no `native_decide`.  AC⁰ ceiling; not P≠NP-strength.
-/

namespace PallLean.Paper93.DeepMath.PathB.Depth3

open SwitchingCounting Layered

variable {n : ℕ}

-- bottomGates_length_pos: an alternating tower has at least one bottom gate (mutual AltO/AltA induction).
mutual
theorem bottomGates_length_pos_AltO :
    ∀ {k : ℕ} {C : Layered n}, AltO k C → 1 ≤ (bottomGates C).length
  | _, _, AltO.dnf cs => by rw [show bottomGates (dnf cs) = [cs] from rfl]; simp
  | _, _, AltO.gOr k gs hne h => by
      obtain ⟨g₀, gs', rfl⟩ := List.exists_cons_of_ne_nil hne
      rw [bottomGates_gOr, bottomGatesList, List.length_append]
      have := bottomGates_length_pos_AltA (h g₀ (by simp))
      omega
theorem bottomGates_length_pos_AltA :
    ∀ {k : ℕ} {C : Layered n}, AltA k C → 1 ≤ (bottomGates C).length
  | _, _, AltA.cnf cs => by rw [show bottomGates (cnf cs) = [cs] from rfl]; simp
  | _, _, AltA.gAnd k gs hne h => by
      obtain ⟨g₀, gs', rfl⟩ := List.exists_cons_of_ne_nil hne
      rw [bottomGates_gAnd, bottomGatesList, List.length_append]
      have := bottomGates_length_pos_AltO (h g₀ (by simp))
      omega
end

end PallLean.Paper93.DeepMath.PathB.Depth3

#print axioms PallLean.Paper93.DeepMath.PathB.Depth3.bottomGates_length_pos_AltO
