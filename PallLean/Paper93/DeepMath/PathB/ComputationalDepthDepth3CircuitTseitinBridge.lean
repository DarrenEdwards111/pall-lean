import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3AssignmentBijection

/-!
# Bridging the circuit construction to the Tseitin CNF axioms

The circuit construction yields a refuting `DTRef` over `tautAx (dualDNF Ax)` (the De Morgan dual
axioms, in the Tseitin literal model); the width lower bound (`dtRef_refuting_depth_ge`) needs those
axioms to be **implied by vertex constraints** (`hAxiom`).  This file connects the two.

The key identity: `tautAx (dualDNF Ax) = Ax.map (·.image rlitToTlit)` — re-negating the dual term
recovers the clause (`negTermClause_clauseToDualTerm`), so the circuit's dual axioms are exactly the
`rlitToTlit`-images of the chosen `RLit` clause family `Ax`.  Hence if each image clause is implied by
a vertex constraint (e.g. each is a `tseitinClause`, via `implies_tseitinClause`), the whole axiom
list satisfies the width LB's `hAxiom`.

* `tautAx_dualDNF_eq` — `tautAx (dualDNF Ax) = Ax.map (·.image rlitToTlit)`.
* `tautAx_dualDNF_implies` — per-clause constraint-implication transfers to the full axiom list (the
  `hAxiom` hypothesis of `dtRef_refuting_depth_ge` / `depth3_tseitin_lower_bound`).

With `circuit_refutation_of_tlit_unsat` (the unsat side) this leaves only the concrete instantiation
(choosing `Ax` as the `rlitToTlit`-preimages of the explicit `tseitinClause`s, with `Edge = Fin n`)
to feed the explicit Tseitin width/size lower bound.  AC⁰/depth-3; `Depth3CollapseModel.collapse` and
P vs NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.TseitinResolution
open PallLean.Paper93.DeepMath.PathB.SemanticMeasure

namespace SearchDischarge

open Depth3

variable {n : ℕ}

/-- **The circuit's dual axioms are the `rlitToTlit`-images of `Ax`.**  Re-negating each dual term
recovers the clause (`negTermClause_clauseToDualTerm`), so `tautAx (dualDNF Ax)` is exactly
`Ax.map (·.image rlitToTlit)`. -/
theorem tautAx_dualDNF_eq (Ax : List (ResolutionClause (RLit n))) :
    tautAx (dualDNF Ax) = Ax.map (fun C => C.image rlitToTlit) := by
  unfold tautAx dualDNF
  rw [List.map_map]
  apply List.map_congr_left
  intro C _
  rw [Function.comp_apply, negTermClause_clauseToDualTerm]

/-- **`hAxiom` transfer.**  If every clause `C` of `Ax` has its `rlitToTlit`-image implied by a vertex
constraint, then every clause of `tautAx (dualDNF Ax)` is implied by a vertex constraint — exactly the
`hAxiom` hypothesis the expander-Tseitin width lower bound consumes. -/
theorem tautAx_dualDNF_implies {V : Type*} [Fintype V] [DecidableEq V]
    (G : TseitinGraph V (Fin n)) (charge : V → ZMod 2)
    {Ax : List (ResolutionClause (RLit n))}
    (h : ∀ C ∈ Ax, ∃ v : V, Implies TSat (TConstr G charge) {v} (C.image rlitToTlit)) :
    ∀ C' ∈ tautAx (dualDNF Ax), ∃ v : V, Implies TSat (TConstr G charge) {v} C' := by
  intro C' hC'
  rw [tautAx_dualDNF_eq] at hC'
  obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hC'
  exact h C hC

end SearchDischarge

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SearchDischarge.tautAx_dualDNF_eq
#print axioms PallLean.Paper93.DeepMath.PathB.SearchDischarge.tautAx_dualDNF_implies
