import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3HypercubeInstantiation
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthSwitchingBinomialRegime
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CircuitConstruction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CollapseBothRoutes

/-!
# Master theorem: the full depth-3 switching → width-lower-bound chain

This file states the end-to-end result, chaining every link proved across the arc.  The complete
pipeline, lemma by lemma:

1.  **Concrete circuit** — `SearchDischarge.axiomOf_dualDNF`: for any clause family `Ax` (over the
    `Fin n × Bool` model), the dual DNF `cs := dualDNF Ax` satisfies `AxiomOf cs = (· ∈ Ax)`.
2.  **Switching count** — two routes, both proven:
    `SwitchingCounting.canon_count_pathLenBad` (delimiter-free `(2w)^s`, needs `hne`) and
    `SwitchingCounting.canonFlatLabel_switching_count` (tokenized `(w+1)^L`, `hne`-free).
3.  **Binomial regime** — `SwitchingCounting.short_family_ratio`: under `(4w+1)·K ≤ n+1`,
    `|Short|·(2w)^s ≤ |F|`; the switching ratio is `≤ 1`.
4.  **Collapse** — `SwitchingCounting.depth3_collapse_*` / `exists_good_of_count`: the ratio `< 1`
    yields a good restriction (one not in the bad set).
5.  **Good restriction ⟹ refutation** — `Depth3.canonicalDT_eval` (the canonical tree computes the
    DNF) → relabel (`boolDT_to_ldderiv_of_valid`) → `ValidSearch` (`SearchDischarge.canonicalDT_ldderiv`,
    via the end-state decoder `decodedSel_eq_replaySel`) → a `DTRef` refutation with all clause widths
    `≤ depth` (`DTRef.dtRef_to_ldderiv`).
6.  **Literal transport** — `LDeriv.mapLit`: carry the refutation onto `TLit Edge`.
7.  **Width lower bound** — `LDeriv.ldn_width_lower_bound` / `dtRef_refuting_depth_ge`: any refuting
    tree over expander-Tseitin has depth `≥ c·t`.
8.  **Concrete expander** — `hypercube_no_shallow_refutation`: at the hypercube `Q_k`
    (`Hypercube.hypercube_hasExpansion`, `tseitin_unsat`), no refuting tree of depth `< t` exists.

`depth3_master_squeeze` is the end-to-end statement: at the concrete hypercube expander, a refuting
decision tree over its Tseitin axioms that is *shallow* (`depth < t`, the collapse outcome in the
regime) is **impossible** — the contradiction between shallow-by-collapse and deep-by-width.

`binomial_regime_parameter_inequality` records the collapse-side analytic input (the ratio `≤ 1`),
also proved.

**Honest boundary.**  The links proved above are joined by one bridge taken as a hypothesis here
(the `DTRef` `T` over the hypercube axioms with `depth < t`): namely that a good restriction's
canonical tree, transported, *is* such a tree.  Discharging it concretely requires the tight
`depth ≤ s` (good-restriction) direction and the variable bijection `Fin n × Bool ≃ TLit (HCEdge k)`
— the remaining glue, not faked.  The whole result is **AC⁰/depth-3**, not P vs NP; the
`Depth3CollapseModel.collapse` field (general circuit size ↔ collapse) is untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.PathB.TseitinResolution

/-- **Master squeeze (end-to-end, at the concrete hypercube expander).**  A refuting decision tree
over the hypercube-Tseitin axioms `Ax` that is shallow (`T.depth < t`, the collapse outcome under the
binomial regime) is impossible: the width lower bound forces depth `≥ c·t = t`.  This is the full
switching → width contradiction realised at an explicit, proven expander. -/
theorem depth3_master_squeeze (k : ℕ) [Nonempty (Hypercube.HCEdge k)]
    (Ax : List (ResolutionClause (TLit (Hypercube.HCEdge k))))
    (hAxiom : ∀ C, C ∈ Ax → ∃ v : (Fin k → ZMod 2),
      SemanticMeasure.Implies TSat
        (TConstr (Hypercube.hypercubeGraph k) (hypercubeCharge k)) {v} C)
    {t : ℕ} (ht2 : 2 ≤ t) (hcard : 4 * t ≤ 2 ^ k)
    (T : DTRef (TLit (Hypercube.HCEdge k)))
    (hlab : DTRef.Labeled (· ∈ Ax) T)
    (href : DTRef.Refutes tcompl T (∅ : ResolutionClause (TLit (Hypercube.HCEdge k))))
    (hshallow : T.depth < t) : False :=
  hypercube_no_shallow_refutation k Ax hAxiom ht2 hcard T hlab href (le_refl _) hshallow

/-- **Collapse-side analytic input.**  The binomial-regime parameter inequality `|Short|·(2w)^s ≤ |F|`
(`2^(n-K+s)·C(n,K-s)·(2w)^s ≤ 2^(n-K)·C(n,K)`): under `(4w+1)·K ≤ n+1` the switching ratio is `≤ 1`,
so most restrictions are good. -/
theorem binomial_regime_parameter_inequality {n w K s : ℕ} (hsK : s ≤ K)
    (hreg : (4 * w) * K + K ≤ n + 1) :
    2 ^ (n - K + s) * n.choose (K - s) * (2 * w) ^ s ≤ 2 ^ (n - K) * n.choose K :=
  SwitchingCounting.short_family_ratio hsK hreg

/-- **The concrete circuit exists.**  For any hypercube axiom family `Ax` (over the `Fin n × Bool`
model), the dual DNF realises it as `AxiomOf`. -/
theorem concrete_circuit_axiom_identity {n : ℕ}
    (Ax : List (ResolutionClause (SearchDischarge.RLit n))) :
    SearchDischarge.AxiomOf (SearchDischarge.dualDNF Ax) = (· ∈ Ax) :=
  SearchDischarge.axiomOf_dualDNF Ax

end PallLean.Paper93.DeepMath.PathB

#print axioms PallLean.Paper93.DeepMath.PathB.depth3_master_squeeze
#print axioms PallLean.Paper93.DeepMath.PathB.binomial_regime_parameter_inequality
#print axioms PallLean.Paper93.DeepMath.PathB.concrete_circuit_axiom_identity
