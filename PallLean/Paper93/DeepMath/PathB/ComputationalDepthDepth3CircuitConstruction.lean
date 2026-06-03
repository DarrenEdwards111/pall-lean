import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SearchCoupling

/-!
# The concrete circuit construction: `AxiomOf cs = (· ∈ Ax)`

The last obligation of the depth-3 pipeline is to exhibit a DNF `cs` whose De Morgan–dual axioms are
a *given* resolution-clause family `Ax` (over the `Fin n × Bool` literal model `RLit n`).  This is
the "circuit" whose negation is `cs`: the dual of the CNF `Ax`.

It holds for **any** `Ax`, because `litNeg`/`resLit` compose to an involution.  Define `litFromRLit`
(`(i,true) ↦ neg i`, `(i,false) ↦ pos i`) so that `resLit ∘ litNeg ∘ litFromRLit = id`; turn each
clause of `Ax` into a DNF term by mapping its literals through `litFromRLit`; then re-negating
recovers the clause:

* `resLit_litNeg_litFromRLit` — the involution `resLit (litNeg (litFromRLit p)) = p`;
* `negTermClause_clauseToDualTerm` — `negTermClause (clauseToDualTerm C) = C`;
* `axiomOf_dualDNF` — **the discharge**: `AxiomOf (dualDNF Ax) = (· ∈ Ax)`.

So with `cs := dualDNF Ax`, `AxiomOf cs = (· ∈ Ax)` exactly.  For expander Tseitin, take `Ax` to be
the Tseitin vertex-constraint clauses pulled back to `RLit n` along the literal bijection
(`LDeriv.mapLit`); `cs` is then the concrete depth-3 object whose collapse the whole pipeline bounds.

(The structural side conditions `hwidth`/`hcs` for `cs = dualDNF Ax` transfer under mild conditions
on `Ax`: `width (clauseToDualTerm C) = C.card`, and the per-clause `litVar`-nodup holds when no `Ax`
clause carries both polarities of a variable — true for Tseitin's non-tautological constraints.)
-/

namespace PallLean.Paper93.DeepMath.PathB

namespace SearchDischarge

open Depth3

variable {n : ℕ}

/-- Turn a resolution literal into the `Rung4Literal` whose De Morgan dual `resLit`s back to it. -/
def litFromRLit : RLit n → Rung4Literal n
  | (i, true) => .neg i
  | (i, false) => .pos i

/-- **The involution.**  `resLit (litNeg (litFromRLit p)) = p`. -/
theorem resLit_litNeg_litFromRLit (p : RLit n) :
    resLit (Depth3.litNeg (litFromRLit p)) = p := by
  obtain ⟨i, b⟩ := p
  cases b <;> rfl

/-- The DNF term dual to a resolution clause: its literals mapped through `litFromRLit`. -/
noncomputable def clauseToDualTerm (C : ResolutionClause (RLit n)) : Clause n :=
  ⟨C.toList.map litFromRLit⟩

/-- The dual DNF of a CNF (clause family): one dual term per clause. -/
noncomputable def dualDNF (Ax : List (ResolutionClause (RLit n))) : List (Clause n) :=
  Ax.map clauseToDualTerm

/-- **Re-negating the dual term recovers the clause.** -/
theorem negTermClause_clauseToDualTerm (C : ResolutionClause (RLit n)) :
    negTermClause (clauseToDualTerm C) = C := by
  have hmap : ((C.toList.map litFromRLit).map Depth3.litNeg).map resLit = C.toList := by
    rw [List.map_map, List.map_map]
    simp only [Function.comp_def, resLit_litNeg_litFromRLit, List.map_id']
  show resClause ((clauseToDualTerm C).lits.map Depth3.litNeg) = C
  rw [clauseToDualTerm, resClause, hmap, Finset.toList_toFinset]

/-- **The discharge.**  The dual DNF `cs = dualDNF Ax` has `AxiomOf cs = (· ∈ Ax)`: its De Morgan
duals are exactly the clauses of `Ax`. -/
theorem axiomOf_dualDNF (Ax : List (ResolutionClause (RLit n))) :
    AxiomOf (dualDNF Ax) = (· ∈ Ax) := by
  funext A
  apply propext
  constructor
  · rintro ⟨T, hT, hAT⟩
    rw [dualDNF, List.mem_map] at hT
    obtain ⟨C, hC, rfl⟩ := hT
    rw [hAT, negTermClause_clauseToDualTerm]; exact hC
  · intro hA
    exact ⟨clauseToDualTerm A, by rw [dualDNF, List.mem_map]; exact ⟨A, hA, rfl⟩,
      (negTermClause_clauseToDualTerm A).symm⟩

/-- Width transfer: each dual term has width equal to its clause's cardinality. -/
theorem width_clauseToDualTerm (C : ResolutionClause (RLit n)) :
    (clauseToDualTerm C).lits.length = C.card := by
  rw [clauseToDualTerm, List.length_map, Finset.length_toList]

end SearchDischarge

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SearchDischarge.negTermClause_clauseToDualTerm
#print axioms PallLean.Paper93.DeepMath.PathB.SearchDischarge.axiomOf_dualDNF
