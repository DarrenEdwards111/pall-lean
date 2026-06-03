import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FinalInstantiation
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3Hypercube

/-!
# Concrete expander instantiation: hypercube-Tseitin

The squeeze (`depth3_tseitin_lower_bound`) needs a *concrete* expander graph with proven expansion
and unsatisfiability.  The ladder already has one: the **hypercube** `Q_k` (vertices `Fin k → ZMod 2`,
edges `HCEdge k`), with

* `Hypercube.hypercube_hasExpansion k : (hypercubeGraph k).HasExpansion 1` (expansion `c = 1`);
* `tseitin_unsat … (hypercubeCharge_odd k)` (unsatisfiability of the odd charge);
* `hypercube_card_V : |V| = 2^k`.

Instantiating the squeeze at this concrete graph:

`hypercube_no_shallow_refutation` — **a refuting decision tree over the hypercube-Tseitin axioms
cannot be shallow**: with `2 ≤ t` and `4t ≤ 2^k`, any clause-labelled refutation tree `T` over a
Tseitin-implied axiom set `Ax` with `T.depth ≤ D < t` is impossible (`c·t = 1·t = t`).

This is the concrete realisation of the width side of the depth-3 lower bound: at the explicit
expander `Q_k`, no shallow tree refutes its Tseitin axioms.  Composed with the collapse (a small
circuit's good restriction gives a *shallow* tree) and the binomial regime, it is the contradiction —
at a fully concrete, proven-expanding instance.  Everything proved, no `sorry`/custom axioms.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.TseitinResolution

/-- **Concrete expander instantiation.**  No refuting decision tree over the hypercube-Tseitin
axioms can have depth `< t` (for `2 ≤ t`, `4t ≤ 2^k`).  The hypercube is a proven `c=1` expander
with an unsatisfiable odd charge. -/
theorem hypercube_no_shallow_refutation (k : ℕ) [Nonempty (Hypercube.HCEdge k)]
    (Ax : List (ResolutionClause (TLit (Hypercube.HCEdge k))))
    (hAxiom : ∀ C, C ∈ Ax → ∃ v : (Fin k → ZMod 2),
      SemanticMeasure.Implies TSat
        (TConstr (Hypercube.hypercubeGraph k) (hypercubeCharge k)) {v} C)
    {t : ℕ} (ht2 : 2 ≤ t) (hcard : 4 * t ≤ 2 ^ k)
    (T : DTRef (TLit (Hypercube.HCEdge k)))
    (hlab : DTRef.Labeled (· ∈ Ax) T)
    (href : DTRef.Refutes tcompl T (∅ : ResolutionClause (TLit (Hypercube.HCEdge k))))
    {D : ℕ} (hdepth : T.depth ≤ D) (hshallow : D < t) : False := by
  refine depth3_tseitin_lower_bound (Hypercube.hypercubeGraph k) (hypercubeCharge k)
    (tseitin_unsat (Hypercube.hypercubeGraph k) (hypercubeCharge k) (hypercubeCharge_odd k))
    Ax hAxiom (le_refl 1) (Hypercube.hypercube_hasExpansion k) ht2
    (by rw [hypercube_card_V]; exact hcard) T hlab href hdepth ?_
  omega

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.hypercube_no_shallow_refutation
