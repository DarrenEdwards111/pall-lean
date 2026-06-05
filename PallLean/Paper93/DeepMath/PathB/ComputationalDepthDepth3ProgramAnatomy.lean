import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3MasterTheorem
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FinalInstantiation
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3FalsifyDeepestCollapse
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3CanonLabelDepthGap
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3EmptySkipWall
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3NoSkipReconstruction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3PureFalsifyReconstruction
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthDepth3DepthBadViaEncLits

/-!
# Depth-3 switching → width lower bound: program anatomy

A single machine-checked index of the **entire** depth-3 pipeline, zoomed out from the switching
sub-arc to the end-to-end squeeze.  Every `#check` is a proved theorem (clean axioms, no `sorry`, no
`native_decide`).  The pipeline and its exact status:

## The end-to-end squeeze (PROVED, given a shallow refuting tree)

* `depth3_master_squeeze` — at the concrete hypercube expander, a refuting decision tree over the
  Tseitin axioms that is shallow (`depth < t`) is impossible.
* `depth3_tseitin_lower_bound` — the width side: a refuting `DTRef` over expander-Tseitin has depth
  `≥ c·t` (`dtRef_refuting_depth_ge`).
* `LDeriv.mapLit` — the literal transport carrying the refutation onto the Tseitin model.
* `hypercube_no_shallow_refutation` — the concrete expander instance.

## The collapse side (PROVED unconditionally in the falsify-deepest regime)

* `exists_good_falsify_deepest` — in the falsify-deepest regime the tight count is proved (label-free
  via `decodedSel`), so the pigeonhole yields a good restriction unconditionally.
* `binomial_regime_parameter_inequality` — the analytic input `|Short|·(2w)^s ≤ |F|`.
* `canonicalDT_ldderiv` / `boolDT_to_ldderiv_of_valid` / `DTRef.dtRef_to_ldderiv` — good restriction
  ⟹ canonical tree ⟹ width-`≤depth` resolution refutation.
* `concrete_circuit_axiom_identity` (`axiomOf_dualDNF`) — the dual-DNF realises the axiom family.

## ReconstructionCorrect (the max-depth count) — discharged in three regimes

* pure-falsify: `reconstruction_pure_falsify`, `deepest_pure_falsify_count`;
* interleaved no-skip: `reconstruction_no_skip`, `deepest_no_skip_reconstruction_count`;
* (pure-satisfy elsewhere).

## The TWO remaining obligations (precisely fenced, NOT faked)

**Obligation 1 — the satisfy-step tight count** (the max-depth switching count for branches with
satisfy steps).  Fenced on both sides:
* `encLits_length_lt_depth` / `depth_gt_satpath_witness` — the encLits route's `canonLabelLen` is
  *provably* below the max-depth (pointwise no-go), so it cannot certify a shallow tree.
* `tight_pack_skip_invariant` / `tight_decode_replayLabel` — the deepest-branch tight `(2w)^s` label
  cannot record the skip-alignment (empty-skip wall, information loss).
The encLits route is nonetheless complete for its own measure and yields a good restriction
(`exists_good_canonLabelLen`); the gap to the tree-depth measure is the irreducible Håstad core.

**Obligation 2 — the circuit construction** `AxiomOf cs = (· ∈ Ax)` under the variable bijection
`Fin n × Bool ≃ TLit Edge` (choosing the DNF as the dual of the Tseitin constraints) — concrete
combinatorial glue, separate from Obligation 1.

Everything else in the chain is proved.  Ceiling: **AC⁰/depth-3** — `Depth3CollapseModel.collapse`
(general circuit size ↔ collapse) and P vs NP are untouched.
-/

namespace PallLean.Paper93.DeepMath.PathB

-- End-to-end squeeze (proved, given a shallow refuting tree).
#check @depth3_master_squeeze
#check @depth3_tseitin_lower_bound
#check @LDeriv.mapLit
#check @hypercube_no_shallow_refutation
#check @dtRef_refuting_depth_ge

-- Collapse side (unconditional in the falsify-deepest regime).
#check @Depth3.exists_good_falsify_deepest
#check @binomial_regime_parameter_inequality
#check @SearchDischarge.canonicalDT_ldderiv
#check @DTRef.dtRef_to_ldderiv
#check @concrete_circuit_axiom_identity

-- ReconstructionCorrect (max-depth count) discharged in three regimes.
#check @Depth3.reconstruction_pure_falsify
#check @Depth3.deepest_pure_falsify_count
#check @Depth3.reconstruction_no_skip
#check @Depth3.deepest_no_skip_reconstruction_count

-- Obligation 1: the satisfy-step tight count, fenced on both sides.
#check @Depth3.encLits_length_lt_depth
#check @Depth3.depth_gt_satpath_witness
#check @Depth3.tight_pack_skip_invariant
#check @Depth3.tight_decode_replayLabel
#check @SwitchingCounting.exists_good_canonLabelLen

end PallLean.Paper93.DeepMath.PathB
