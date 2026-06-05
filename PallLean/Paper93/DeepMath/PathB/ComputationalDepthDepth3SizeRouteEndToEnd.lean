import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3SizeRouteContradiction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DTRefToResolution

/-!
# The size-route depth-3 lower bound, end-to-end modulo Obligation 1

This assembles the full **size route** into one theorem: a shallow refuting decision tree over the
explicit Tseitin CNF is impossible.  The chain, all proved:

  shallow refuting `DTRef` over `TseitinCNF`  (Obligation 1: the collapse output)
    →  `dtRef_resolution_size_le`   :  `ResolutionDerivation` of `∅`, size `≤ 2^(depth+1)`
    →  `tseitin_no_small_refutation`:  size `> 2^(c·t−w₀−1)`  (BSW size LB, restriction internal)
    →  `False`.

`depth3_size_route_modulo_collapse` is the composition.  Unlike the width route
(`depth3_lower_bound_modulo_collapse`), no restriction-composition appears — it is internalized in the
Ben–Sasson–Wigderson size lower bound.  The **only** remaining hypothesis (beyond the explicit
expander setup) is the shallow refuting tree `(T, hlab, href, hshallow)` — the switching collapse,
i.e. the fenced **Obligation 1** (unconditional in the falsify-deepest regime, fenced in the
satisfy-step regime).

Everything else in the depth-3 lower bound is now proved and assembled.  Ceiling: **AC⁰/depth-3** —
`Depth3CollapseModel.collapse` and P vs NP are untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.TseitinResolution

variable {V Edge : Type*} [Fintype V] [DecidableEq V] [Fintype Edge] [DecidableEq Edge]

/-- **The size-route depth-3 lower bound, modulo Obligation 1.**  For an expander Tseitin graph `G`
with odd charge, no shallow refuting decision tree over `TseitinCNF G charge` exists: a `DTRef`
labeled by the Tseitin clauses, refuting `∅`, with `depth + 1 ≤ c·t − w₀ − 1`, yields `False`.

The proof composes the tree → resolution size conversion (`dtRef_resolution_size_le`: size
`≤ 2^(depth+1)`) with the BSW size lower bound (`tseitin_no_small_refutation`).  No
restriction-composition — it is internal to the size lower bound.  The lone input is the shallow
refuting tree `T` (the switching collapse = the fenced Obligation 1). -/
theorem depth3_size_route_modulo_collapse (G : TseitinGraph V Edge) (charge : V → ZMod 2)
    (hodd : ∑ v : V, charge v = 1) {c t w₀ : ℕ} (hc : 1 ≤ c) (hexp : G.HasExpansion c)
    (ht1 : 1 ≤ t) (hcard : 4 * t ≤ Fintype.card V) (hdeg : ∀ v, (incident G v).card ≤ w₀)
    (hgap : w₀ < c * t)
    (T : DTRef (TLit Edge))
    (hlab : DTRef.Labeled (TseitinCNF G charge) T)
    (href : DTRef.Refutes tcompl T (∅ : ResolutionClause (TLit Edge)))
    (hshallow : T.depth + 1 ≤ c * t - w₀ - 1) :
    False := by
  obtain ⟨Der, hsize⟩ := dtRef_resolution_size_le hlab href
  exact tseitin_no_small_refutation G charge hodd hc hexp ht1 hcard hdeg hgap Der hsize hshallow

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.depth3_size_route_modulo_collapse
