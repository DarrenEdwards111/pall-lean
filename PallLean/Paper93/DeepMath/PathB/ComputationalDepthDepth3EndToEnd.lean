import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3TseitinInstantiation
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FinalInstantiation

/-!
# The depth-3 lower bound, end-to-end modulo Obligation 1

Every link of the depth-3 switching → width pipeline is now concrete except the single fenced
**Obligation 1** — the good-restriction collapse that makes the canonical tree *shallow*.  This file
composes the rest into one statement whose **only** remaining hypothesis (beyond the explicit expander
setup) is that collapse, expressed as a shallow refuting tree over the explicit circuit's axioms.

`depth3_lower_bound_modulo_collapse`: for an expander Tseitin graph `G` over `Fin n` edges with odd
charge, the explicit depth-3 circuit `dualDNF (tseitinAxList G charge)` cannot collapse to a shallow
refuting tree: if a refuting `DTRef` over its dual axioms has depth `≤ D < c·t`, that is **impossible**.

The proof discharges, *concretely*, both hypotheses of the expander-Tseitin width lower bound
(`depth3_tseitin_lower_bound`):

* unsatisfiability — `tseitin_unsat` (from `∑ charge = 1`);
* the axioms are implied by vertex constraints — `tseitinAxList_implies` (the circuit-construction
  chain: dual-axiom identity + `implies_tseitinClause`).

So the *only* input left is `(T, hlab, href, hdepth, hshallow)`: a shallow refuting tree over the
circuit's axioms.  Producing it from a small circuit is exactly the switching collapse — proved
unconditionally in the falsify-deepest regime, and reduced to the fenced satisfy-step core
(Obligation 1) in general.  Everything else in the depth-3 lower bound is now proved and assembled
here.  Ceiling: **AC⁰/depth-3** — `Depth3CollapseModel.collapse` and P vs NP are untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.TseitinResolution

variable {n : ℕ} {V : Type*} [Fintype V] [DecidableEq V] [Nonempty (Fin n)]

/-- **The depth-3 lower bound, modulo Obligation 1.**  For an expander Tseitin graph `G` over `Fin n`
edges with odd charge `∑ charge = 1` and expansion `c`, the explicit depth-3 circuit
`dualDNF (tseitinAxList G charge)` admits **no** shallow refuting decision tree: a refuting `DTRef`
over its dual axioms of depth `≤ D < c·t` yields `False`.

Both width-LB hypotheses are discharged concretely (`tseitin_unsat`, `SearchDischarge.tseitinAxList_implies`);
the lone remaining input is the shallow refuting tree `T` — the good-restriction collapse (the fenced
Obligation 1). -/
theorem depth3_lower_bound_modulo_collapse (G : TseitinGraph V (Fin n)) (charge : V → ZMod 2)
    (hodd : ∑ v : V, charge v = 1)
    {c t : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c) (ht2 : 2 ≤ t)
    (hcard : 4 * t ≤ Fintype.card V)
    (T : DTRef (TLit (Fin n)))
    (hlab : DTRef.Labeled
      (· ∈ SearchDischarge.tautAx (SearchDischarge.dualDNF (SearchDischarge.tseitinAxList G charge))) T)
    (href : DTRef.Refutes tcompl T (∅ : ResolutionClause (TLit (Fin n))))
    {D : ℕ} (hdepth : T.depth ≤ D) (hshallow : D < c * t) :
    False :=
  depth3_tseitin_lower_bound G charge (tseitin_unsat G charge hodd)
    (SearchDischarge.tautAx (SearchDischarge.dualDNF (SearchDischarge.tseitinAxList G charge)))
    (SearchDischarge.tseitinAxList_implies G charge)
    hc hexp ht2 hcard T hlab href hdepth hshallow

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.depth3_lower_bound_modulo_collapse
