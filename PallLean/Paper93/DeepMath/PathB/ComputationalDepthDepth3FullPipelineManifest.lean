import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3ExplicitCircuitLowerBound
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3StarBoundWiring
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonLabelDepthGap
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3EmptySkipWall
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3EndToEnd
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FalsifyDeepestCollapse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukHardFunctionLB
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukHardFunctionExplicit
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthNeciporukHardFunctionConcrete

/-!
# Depth-3 lower bound: the full assembled pipeline (definitive index)

A machine-checked index of the **entire** depth-3 switching → Tseitin lower-bound pipeline as now
assembled.  Every `#check` is a proved theorem (clean axioms, no `sorry`, no `native_decide`).  The
pipeline reduces the depth-3 (AC⁰) lower bound to a *single* fenced core (Obligation 1).

## The end-to-end statements (three, all modulo Obligation 1)

* `SearchDischarge.depth3_explicit_circuit_no_shallow_refutation` — the **explicit** circuit
  `dualDNF (tseitinAxList G charge)` admits no shallow refuting tree over its dual axioms.
* `depth3_size_route_modulo_collapse` — size route over `TseitinCNF` (BSW-internal, no
  restriction-composition).
* `depth3_lower_bound_modulo_collapse` — width route over the circuit's dual axioms.

## The discharged components

* **Circuit construction.**  `circuit_refutation_of_unsat`, `dualDNF_taut_of_unsat`, `axiomOf_circuit`
  — the explicit circuit (negation of the Tseitin CNF) and its tautology from unsatisfiability.
* **Bijections.**  `tseitinClause_image` (literal), `rFalsifies_unsat_of_tlit_unsat` (assignment).
* **Tseitin instantiation.**  `tseitinAxList_implies` (`hAxiom`), `tseitinAxList_unsat`,
  `mem_tautAx_imp_tseitinCNF` (dual axioms are `TseitinCNF` clauses).
* **Size route.**  `dtRef_resolution_size_le` (tree → resolution, size `≤ 2^(d+1)`),
  `tseitin_no_small_refutation` (BSW size LB `tseitinCNF_exp_size`).
* **Falsify-deepest extraction.**  `exists_good_falsify_deepest` (count unconditional),
  `tseitin_circuit_validSearch_shallow` (residual refutation), `exists_good_star_K` /
  `tseitin_circuit_good_shallow` (star-bound pinned to `K`).

## The single remaining core (fenced, NOT faked)

**Obligation 1** — the switching depth bound: from a good restriction, a *shallow* `∅`-refuting tree
over the (Tseitin) axioms.  Fenced on both sides:
* `encLits_length_lt_depth` — `canonLabelLen < depth` pointwise (the satisfying-path measure is below
  the max-depth);
* `tight_pack_skip_invariant` — the tight `(2w)^s` label cannot record the skip-alignment (empty-skip
  wall).

The falsify-deepest *count* and *extraction* are unconditional; the residual refutation is from
`falseSet ρ` (depth `≤ K`), and lifting it to a small `∅`-refutation over the full Tseitin CNF (the
restricted-Tseitin-is-expander step) plus the general satisfy-step switching are what remain.
Everything else above is proved and assembled.  Ceiling: **AC⁰/depth-3** — `Depth3CollapseModel.collapse`
and P vs NP untouched.

## A second, fully-discharged route: Nečiporuk formula-size lower bound (no obligations)

Independent of the depth-3 switching route, the Nečiporuk combinatorial-counting route is assembled
**end-to-end with no fenced core** on a concrete explicit function (`NecHard.hardF`, a XOR of `m`
table-lookups into a shared `2^b`-cell data region).  Every statement below is proved (clean axioms,
no `sorry`):

* `neciporuk_formula_lower_bound` — the method: `∑ᵢ log₂ #blockResiduals(Sᵢ,F) ≤ 2·clog₂(|Tok|+1)·
  litCount F + 2·#blocks` for any block partition.
* `card_blockResiduals_ge` — the reusable lower-bound bridge (injective parameter family ⇒ many
  subfunctions).
* `NecHard.hardF_merge` — the explicit function's subfunction reads the addressed cell.
* `NecHard.card_blockResiduals_hardF_ge` + `NecHard.filter_c0_false_card` — per address block,
  `#blockResiduals ≥ 2^{2^b − 1}` distinct subfunctions.
* `NecHard.hardF_litCount_lower` — **the deliverable**: `m·(2^b − 1) ≤ 2·clog₂(|Tok|+1)·litCount F +
  2·(m + 1)` for *any* `B₂` formula `F` computing `hardF`.  With `b ≈ log m`, `m ≈ n/b`, this is
  `litCount ≳ n²/log²n`.
* `NF.card_Tok_eq` — the serialization alphabet has `16 + 2n` tokens (resolves the abstract `|Tok|`).
* `NecHard.hardF_litCount_lower_div` — **the headline, fully explicit**:
  `litCount F ≥ (m·(2^b − 1) − 2(m+1)) / (2·clog₂(2·nn + 17))`.
* `NecHard.hardF_litCount_lower_concrete` — a **witnessed numeric instance**: at `b=10`, `m=1024`
  (`N=11264` variables), any formula computing `hardF` has `litCount F ≥ 34850 > 3·N`.

Ceiling here: **`n²/log²n` formula size** (classic Nečiporuk) — a genuine *restricted* lower bound,
fully proved with no carried hypothesis, but still **not** P vs NP.
-/

namespace PallLean.Paper93.DeepMath.PathB

-- End-to-end statements (three, modulo Obligation 1).
#check @SearchDischarge.depth3_explicit_circuit_no_shallow_refutation
#check @depth3_size_route_modulo_collapse
#check @depth3_lower_bound_modulo_collapse

-- Circuit construction.
#check @SearchDischarge.circuit_refutation_of_unsat
#check @SearchDischarge.dualDNF_taut_of_unsat
#check @SearchDischarge.axiomOf_circuit

-- Bijections + Tseitin instantiation.
#check @SearchDischarge.tseitinClause_image
#check @SearchDischarge.rFalsifies_unsat_of_tlit_unsat
#check @SearchDischarge.tseitinAxList_implies
#check @SearchDischarge.tseitinAxList_unsat
#check @SearchDischarge.mem_tautAx_imp_tseitinCNF

-- Size route.
#check @dtRef_resolution_size_le
#check @TseitinResolution.tseitin_no_small_refutation
#check @TseitinResolution.tseitinCNF_exp_size

-- Falsify-deepest extraction (count + residual + star bound).
#check @Depth3.exists_good_falsify_deepest
#check @SearchDischarge.tseitin_circuit_validSearch_shallow
#check @SwitchingCounting.exists_good_star_K
#check @SearchDischarge.tseitin_circuit_good_shallow

-- Obligation 1 fenced on both sides.
#check @Depth3.encLits_length_lt_depth
#check @Depth3.tight_pack_skip_invariant

-- Second route: Nečiporuk formula-size lower bound (no obligations, n²/log²n ceiling).
#check @neciporuk_formula_lower_bound
#check @card_blockResiduals_ge
#check @NecHard.hardF_merge
#check @NecHard.card_blockResiduals_hardF_ge
#check @NecHard.filter_c0_false_card
#check @NecHard.log_card_blockResiduals_hardF_ge
#check @NecHard.hardF_litCount_lower
#check @NF.card_Tok_eq
#check @NecHard.hardF_litCount_lower_explicit
#check @NecHard.hardF_litCount_lower_div
#check @NecHard.hardF_litCount_lower_concrete

end PallLean.Paper93.DeepMath.PathB
