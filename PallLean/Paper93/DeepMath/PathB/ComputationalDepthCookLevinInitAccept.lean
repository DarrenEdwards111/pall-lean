import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCookLevinAssembly

/-!
# Cook–Levin M2 — the init and accept clauses, and the full-formula `⇐` soundness

The last clause families of the tableau:

* **init** — the `t=0` row is the forced initial config: `state[0] = start`, `head[0] = 0`, `cell[0][p] = x[p]`.
  A conjunction of unit `fixBits`.
* **accept** — the final row `t=B` is halting-and-accepting: `⋁_{q accepting∧halting} state[B][q]`.  One
  `atLeastOne` clause.

With the transition families (`CookLevinAssembly`), this closes the **`⇐` half** of `Satisfiable ⟺ accepting`: if the
real run halts-and-accepts by step `B` (with the head bounded by `P`), the real-run assignment satisfies the whole
tableau formula `fullFormula`, so it is satisfiable.  The `⇒` converse and the poly emitter remain the deferred
research-scale remainder.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.CookLevinInitAccept

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.CookLevinReduction
open PallLean.Paper93.DeepMath.PathB.CookLevinCNFEncode
open PallLean.Paper93.DeepMath.PathB.CookLevinVarIndex
open PallLean.Paper93.DeepMath.PathB.CookLevinOneHotWindow
open PallLean.Paper93.DeepMath.PathB.CookLevinDynamics
open PallLean.Paper93.DeepMath.PathB.CookLevinAssembly

/-! ## The init clauses -/

/-- The init clauses: fix `state[0] = start`, `head[0] = 0`, and `cell[0][p] = x[p]` for `p ≤ P`. -/
noncomputable def initFormula (M : Machine) (x : List Bool) (P : ℕ) : Formula :=
  fixBits ((stateVar 0 (Fintype.equivFin M.State M.start).val, true) :: (headVar 0 0, true) ::
    (List.range (P + 1)).map (fun p => (cellVar 0 p, x.getD p false)))

theorem init_state_sat (M : Machine) (x : List Bool) :
    fullAssign M x (stateVar 0 (Fintype.equivFin M.State M.start).val) = true := by
  rw [fullAssign_state, stateBit, dif_pos (Fin.isLt _), run_zero]
  simp only [init, decide_eq_true_eq, Fin.eta, Equiv.symm_apply_apply]

theorem init_head_sat (M : Machine) (x : List Bool) : fullAssign M x (headVar 0 0) = true := by
  rw [fullAssign_head, run_zero]; simp [init]

theorem init_cell_sat (M : Machine) (x : List Bool) (p : ℕ) :
    fullAssign M x (cellVar 0 p) = x.getD p false := by
  rw [fullAssign_cell, run_zero]; simp [init]

/-- **Init soundness.**  The real-run assignment satisfies the init clauses (the `t=0` row *is* the initial config). -/
theorem initFormula_sound (M : Machine) (x : List Bool) (P : ℕ) :
    evalFormula (fullAssign M x) (initFormula M x P) = true := by
  rw [initFormula, fixBits_iff]
  intro pr hpr
  simp only [List.mem_cons, List.mem_map, List.mem_range] at hpr
  rcases hpr with rfl | rfl | ⟨p, _, rfl⟩
  · exact init_state_sat M x
  · exact init_head_sat M x
  · exact init_cell_sat M x p

/-! ## The accept clause -/

/-- The accepting-and-halting state indices. -/
noncomputable def acceptStates (M : Machine) : List (Fin (Fintype.card M.State)) :=
  (List.finRange (Fintype.card M.State)).filter
    (fun q => M.accept ((Fintype.equivFin M.State).symm q) && M.halt ((Fintype.equivFin M.State).symm q))

/-- The accept clause at time `B`: at least one accepting-halting state is on. -/
noncomputable def acceptFormula (M : Machine) (B : ℕ) : Formula :=
  [atLeastOne ((acceptStates M).map (fun q => stateVar B q.val))]

/-- **Accept soundness.**  If the real run halts-and-accepts by step `B`, the real-run assignment satisfies the
accept clause (the run's actual — accepting, halting — state is on at `t=B`). -/
theorem acceptFormula_sound (M : Machine) (x : List Bool) (B : ℕ)
    (hhalt : M.halt (run M B (init M x)).st = true) (hacc : M.accept (run M B (init M x)).st = true) :
    evalFormula (fullAssign M x) (acceptFormula M B) = true := by
  rw [acceptFormula, evalFormula, List.all_cons, List.all_nil, Bool.and_true, atLeastOne_iff]
  refine ⟨stateVar B (Fintype.equivFin M.State (run M B (init M x)).st).val, ?_, ?_⟩
  · refine List.mem_map.mpr ⟨Fintype.equivFin M.State (run M B (init M x)).st, ?_, rfl⟩
    rw [acceptStates, List.mem_filter]
    refine ⟨List.mem_finRange _, ?_⟩
    simp only [Equiv.symm_apply_apply, hacc, hhalt, Bool.and_self]
  · rw [fullAssign_state, stateBit, dif_pos (Fin.isLt _), decide_eq_true_eq, Fin.eta, Equiv.symm_apply_apply]

/-! ## The full tableau formula and the `⇐` soundness -/

/-- The full tableau formula: init, the transition families, and accept. -/
noncomputable def fullFormula (M : Machine) (x : List Bool) (P B : ℕ) : Formula :=
  initFormula M x P ++ assembledFormula M P B ++ acceptFormula M B

/-- **The reduction is sound (`⇐`).**  If the real run halts-and-accepts by step `B` and the head stays within `P`
over `[0,B]`, then the full tableau formula is **satisfiable** — witnessed by the real-run assignment. -/
theorem fullFormula_satisfiable (M : Machine) (x : List Bool) (P B : ℕ)
    (hb : ∀ t, t ≤ B → (run M t (init M x)).hd ≤ P)
    (hhalt : M.halt (run M B (init M x)).st = true) (hacc : M.accept (run M B (init M x)).st = true) :
    Satisfiable (fullFormula M x P B) := by
  refine ⟨fullAssign M x, ?_⟩
  rw [fullFormula, evalFormula_append, evalFormula_append, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨initFormula_sound M x P, assembledFormula_sound M x P B hb⟩, acceptFormula_sound M x B hhalt hacc⟩

end PallLean.Paper93.DeepMath.PathB.CookLevinInitAccept
