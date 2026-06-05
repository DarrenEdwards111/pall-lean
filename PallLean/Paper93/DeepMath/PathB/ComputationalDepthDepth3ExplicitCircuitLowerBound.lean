import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SizeRouteEndToEnd
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TseitinInstantiation

/-!
# The explicit depth-3 circuit admits no shallow refutation (size route, fully concrete)

The size-route end-to-end (`depth3_size_route_modulo_collapse`) is stated over `TseitinCNF`.  The
explicit circuit construction produces decision trees labeled over the circuit's *dual axioms*
`tautAx (dualDNF (tseitinAxList G charge))`.  This file bridges the two — those dual axioms are
exactly `TseitinCNF` clauses — and states the lower bound for the explicit circuit.

* `mem_tautAx_imp_tseitinCNF` — every dual axiom of the explicit circuit is a `TseitinCNF` clause
  (`tautAx_dualDNF_eq` + `mem_tseitinAxList` + `tseitinClause_image`).
* `Labeled_mono` — `Labeled` is monotone in the axiom predicate.
* `depth3_explicit_circuit_no_shallow_refutation` — for the explicit circuit
  `dualDNF (tseitinAxList G charge)`, a refuting decision tree over its dual axioms with
  `depth + 1 ≤ c·t − w₀ − 1` yields `False`.

So the depth-3 lower bound is now stated for a **fully explicit** circuit, with the sole remaining
hypothesis the shallow refuting tree (the switching collapse = the fenced Obligation 1).  AC⁰/depth-3;
`Depth3CollapseModel.collapse` and P vs NP untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.TseitinResolution

/-- **`Labeled` is monotone in the axiom predicate.** -/
theorem Labeled_mono {Lit : Type*} {Ax Ax' : ResolutionClause Lit → Prop}
    (h : ∀ C, Ax C → Ax' C) :
    ∀ t : DTRef Lit, DTRef.Labeled Ax t → DTRef.Labeled Ax' t
  | DTRef.leaf C, hl => h C hl
  | DTRef.node _ t0 t1, hl => ⟨Labeled_mono h t0 hl.1, Labeled_mono h t1 hl.2⟩

namespace SearchDischarge

open Depth3

variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- **Every dual axiom of the explicit circuit is a `TseitinCNF` clause.**  A clause of
`tautAx (dualDNF (tseitinAxList G charge))` is the `rlitToTlit`-image of a wrong-parity preimage
clause, i.e. a `tseitinClause v α` with `parity ≠ charge`. -/
theorem mem_tautAx_imp_tseitinCNF (G : TseitinGraph V (Fin n)) (charge : V → ZMod 2)
    {C : ResolutionClause (TLit (Fin n))}
    (hC : C ∈ tautAx (dualDNF (tseitinAxList G charge))) :
    TseitinCNF G charge C := by
  rw [tautAx_dualDNF_eq] at hC
  obtain ⟨C0, hC0, rfl⟩ := List.mem_map.mp hC
  obtain ⟨v, α, hwrong, rfl⟩ := mem_tseitinAxList hC0
  exact ⟨v, α, hwrong, tseitinClause_image G v α⟩

/-- **The explicit circuit admits no shallow refutation.**  For the explicit depth-3 circuit
`dualDNF (tseitinAxList G charge)` over an expander Tseitin graph with odd charge, a refuting decision
tree over its dual axioms with `depth + 1 ≤ c·t − w₀ − 1` is impossible — via the size route, with
the dual axioms recognised as `TseitinCNF` clauses.  The sole input is the shallow tree (the switching
collapse = the fenced Obligation 1). -/
theorem depth3_explicit_circuit_no_shallow_refutation (G : TseitinGraph V (Fin n))
    (charge : V → ZMod 2) (hodd : ∑ v : V, charge v = 1) {c t w₀ : ℕ} (hc : 1 ≤ c)
    (hexp : G.HasExpansion c) (ht1 : 1 ≤ t) (hcard : 4 * t ≤ Fintype.card V)
    (hdeg : ∀ v, (incident G v).card ≤ w₀) (hgap : w₀ < c * t)
    (T : DTRef (TLit (Fin n)))
    (hlab : DTRef.Labeled (· ∈ tautAx (dualDNF (tseitinAxList G charge))) T)
    (href : DTRef.Refutes tcompl T (∅ : ResolutionClause (TLit (Fin n))))
    (hshallow : T.depth + 1 ≤ c * t - w₀ - 1) :
    False :=
  depth3_size_route_modulo_collapse G charge hodd hc hexp ht1 hcard hdeg hgap T
    (Labeled_mono (fun _ => mem_tautAx_imp_tseitinCNF G charge) T hlab) href hshallow

end SearchDischarge

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.SearchDischarge.mem_tautAx_imp_tseitinCNF
#print axioms PallLean.Paper93.DeepMath.PathB.SearchDischarge.depth3_explicit_circuit_no_shallow_refutation
