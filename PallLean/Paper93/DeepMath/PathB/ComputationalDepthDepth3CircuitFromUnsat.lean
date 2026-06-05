import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CircuitConstruction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3LiteralBijection

/-!
# The circuit-construction obligation: unsatisfiable CNF ⟹ refuting tree over its dual axioms

The pipeline's remaining concrete obligation was to *exhibit* the circuit `cs` whose De Morgan dual
axioms are the target clause family, and whose tautology drives `tautDNF_to_dtRef`.  Both halves are
discharged here, for the circuit `cs := dualDNF Ax` (the negation of the CNF `Ax`):

* `axiomOf_dualDNF` (elsewhere) already gives `AxiomOf cs = (· ∈ Ax)`.
* this file supplies the tautology: **the dual DNF of an *unsatisfiable* CNF is a tautology.**

The semantic key: `dnfEval (dualDNF Ax) x = true` iff `x` *falsifies* some clause of `Ax` (a dual
term `clauseToDualTerm C` is all-true exactly when every literal of `C` is De Morgan–false under `x`).
So if every assignment falsifies some clause — i.e. `Ax` (as a CNF) is unsatisfiable — then `dualDNF
Ax` is true everywhere, and `tautDNF_to_dtRef_tautAx` yields a refuting `DTRef` over `tautAx cs` in
the Tseitin literal model.

* `rFalsifies` — `x` falsifies a clause: every literal's dual is true under `x`.
* `dualDNF_taut_of_unsat` — unsatisfiability (`∀ x, ∃ C ∈ Ax, rFalsifies x C`) ⟹ `dualDNF Ax` is a
  tautology.
* `circuit_refutation_of_unsat` — hence the concrete circuit `dualDNF Ax` yields a refuting `DTRef`
  over `TLit (Fin n)` labeled by `tautAx (dualDNF Ax)`, of `depth ≤ fuel`.

This closes the circuit-construction obligation (Obligation 2): an unsatisfiable CNF `Ax` over the
`RLit n` model is realised by the concrete depth-3 circuit `dualDNF Ax`, whose canonical-tree
collapse the rest of the pipeline bounds.  The remaining tie — that the *specific* expander-Tseitin
constraint clauses are unsatisfiable in this `rFalsifies` sense under the assignment bijection
`(Fin n → Bool) ↔ (Edge → ZMod 2)` — is the concrete instantiation, separate from this construction.
AC⁰/depth-3; `Depth3CollapseModel.collapse` and P vs NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.TseitinResolution

namespace SearchDischarge

open Depth3

variable {n : ℕ}

/-- `x` **falsifies** a resolution clause `C` over `RLit n`: every literal's De Morgan dual literal
(`litFromRLit`) evaluates true under `x` (equivalently, no literal of `C` is satisfied by `x`). -/
def rFalsifies (x : Fin n → Bool) (C : ResolutionClause (RLit n)) : Prop :=
  ∀ p ∈ C, (litFromRLit p).eval x = true

/-- **The dual DNF of an unsatisfiable CNF is a tautology.**  If every assignment `x` falsifies some
clause of `Ax`, then `dualDNF Ax` evaluates true everywhere: the falsified clause's dual term is
all-true under `x`. -/
theorem dualDNF_taut_of_unsat {Ax : List (ResolutionClause (RLit n))}
    (hunsat : ∀ x : Fin n → Bool, ∃ C ∈ Ax, rFalsifies x C) :
    ∀ x, Depth3.dnfEval (dualDNF Ax) x = true := by
  intro x
  obtain ⟨C, hC, hfals⟩ := hunsat x
  rw [Depth3.dnfEval, List.any_eq_true]
  refine ⟨clauseToDualTerm C, List.mem_map.mpr ⟨C, hC, rfl⟩, ?_⟩
  apply Depth3.evalLits_eq_true_of_all
  intro ℓ hℓ
  simp only [clauseToDualTerm] at hℓ
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hℓ
  exact hfals p (Finset.mem_toList.mp hp)

/-- **Circuit construction (Obligation 2), discharged.**  For an unsatisfiable CNF `Ax` over `RLit n`,
the concrete depth-3 circuit `dualDNF Ax` (its negation) yields a refuting decision-tree `DTRef` over
`TLit (Fin n)`, labeled by the dual axioms `tautAx (dualDNF Ax)`, of `depth ≤ fuel`.  Combined with
`axiomOf_dualDNF` (`AxiomOf (dualDNF Ax) = (· ∈ Ax)`), this is the circuit whose collapse the pipeline
bounds. -/
theorem circuit_refutation_of_unsat {Ax : List (ResolutionClause (RLit n))}
    (hunsat : ∀ x : Fin n → Bool, ∃ C ∈ Ax, rFalsifies x C)
    (fuel : ℕ)
    (hfuel : SwitchingCounting.stars (fun _ : Fin n => (none : Option Bool)) ≤ fuel) :
    ∃ T : DTRef (TLit (Fin n)),
      DTRef.Labeled (· ∈ tautAx (dualDNF Ax)) T ∧
      DTRef.Refutes tcompl T (∅ : ResolutionClause (TLit (Fin n))) ∧
      T.depth ≤ fuel :=
  tautDNF_to_dtRef_tautAx (dualDNF Ax) (dualDNF_taut_of_unsat hunsat) fuel hfuel

/-- The circuit's axioms are exactly `Ax` (recording the De Morgan-dual identity for completeness). -/
theorem axiomOf_circuit {Ax : List (ResolutionClause (RLit n))} :
    AxiomOf (dualDNF Ax) = (· ∈ Ax) :=
  axiomOf_dualDNF Ax

end SearchDischarge

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SearchDischarge.dualDNF_taut_of_unsat
#print axioms PallLean.Paper93.DeepMath.PathB.SearchDischarge.circuit_refutation_of_unsat
