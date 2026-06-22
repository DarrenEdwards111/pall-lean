import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ToBTNormalForm
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModmSymAndDepth2
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModGateComposition
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModGateCrossLayer
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0ModCRTFusion
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0MiniBTSize
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0RSDepthComposition
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SymTopCrossLayer
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PrimeApproxToExact
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0PrimeExactExists
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0IntegerDepth3Speedup
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0SymmetricEscapesNoGo
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthACC0MultiCountCollapse

/-!
# ACC⁰ integer/exact arc — machine-checked manifest

A single verified entry point for the ACC⁰ Beigel–Tarui integer/exact-`SYM∘AND` arc built this session:
a `#check` index of every load-bearing theorem, confirming the whole arc composes and is clean
(`[propext, Classical.choice, Quot.sound]`, no `sorry`, no custom axioms).  Mirrors the codebase's other
manifests.

## Structure of the arc

**Normal form + base:**
* `acc0_to_bt_normal_form` — any constant-depth ACC⁰[p] circuit → explicit sparse SYM∘AND (RS
  approximant), degree `≤ L^D`, quasipoly support `≤ (n+1)^{L^D}`.
* `modm_depth2_symAnd_repr`, `modLayer_reads_single_count` — exact depth-2 MOD-layer base, all moduli;
  a MOD-layer over a shared bottom reads one integer count.

**Exact composition closure (all exact, no approximation):**
* `hasSymAndRep_modGate_sharedLayer` — shared-layer MOD closure (completes NOT/AND/OR/MOD).
* `hasMultiSymRep_modGate_crossLayer`, `topGate_crossLayer_hasMultiSymRep` — cross-layer: any symmetric
  top over `k` distinct-layer SYM∘AND subcircuits is `HasMultiSymRep` (count dimension = #layers).
* `mod_crt_fuse`, `hasSymAndRep_modpq_sharedLayer` — composite moduli cost **no** count dimension (CRT).
* `miniBT_collapse_size`, `merge_size_ge_mul` — the two-count collapse, with its multiplicative size.
* `multiCount_factors`, `hasMultiSymRep_collapses` — **the k-count collapse**: any cross-layer
  multi-count function is *exactly* a single-count SYM∘AND.

**Approximate (RS) route — quasipoly but lossy:**
* `toAgree_rs_depth_composition` — one oracle: degree `≤ L^D` ∧ quasipoly support ∧ bounded error.
* `exists_exact_toAgree` — prime exact via union bound (forces large `t`, high degree).
* `exact_hasMultiSymRep_of_majorityCorrect`, `majorityDecode_hasMultiSymRep` — prime approx→exact decode.
* `modModAnd_depth3_sat_speedup` — integer/CRT route at depth 3 (composite, exact, `< 2^n` cells).

**The wall, both sides proved:**
* `or_eq_symmetric` / `or_cells_le` vs `ACC0ExactDegreeNoGo.or_exact_degree_full` — the symmetric count
  (`≤ n+1` cells) escapes the exact-polynomial-degree no-go (degree `n`).
* Exact collapse exists (`hasMultiSymRep_collapses`) but at **tower** size (`merge_size_ge_mul`);
  quasipoly needs RS approximation (`toAgree_rs_depth_composition`) or the open BT integer construction.

## The wall

Every constant-depth ACC⁰ structure over `AND` bottoms collapses **exactly** to a single-count
`SYM∘AND` (`multiCount_factors` + `hasMultiSymRep_collapses`).  The single open quantity is the
**collapsed layer size**: exact ⇒ iterated mixed-radix **tower**; quasipoly ⇒ only RS-approximate.
Keeping it quasipoly across unbounded depth is the Beigel–Tarui integer construction
(`MixedACCDepthReductionSocket` / `composite_BT_degree`), Williams-strength.  Composite-modulus
amplification is the Razborov–Smolensky barrier.  Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.ACC0IntegerExactArcManifest

-- Normal form + base
#check @ACC0ToBTNormalForm.acc0_to_bt_normal_form
#check @ACC0ModmSymAndDepth2.modm_depth2_symAnd_repr
#check @ACC0ModmSymAndDepth2.modLayer_reads_single_count
#check @ACC0ModmSymAndDepth2.modm_depth2_countMod

-- Exact composition closure
#check @ACC0ModGateComposition.hasSymAndRep_modGate_sharedLayer
#check @ACC0ModGateCrossLayer.hasBinarySymRep_modGate2
#check @ACC0ModGateCrossLayer.hasMultiSymRep_modGate_crossLayer
#check @ACC0SymTopCrossLayer.topGate_crossLayer_hasMultiSymRep
#check @ACC0SymTopCrossLayer.majorityDecode_hasMultiSymRep
#check @ACC0ModCRTFusion.mod_crt_fuse
#check @ACC0ModCRTFusion.hasSymAndRep_modpq_sharedLayer
#check @ACC0MiniBTSize.miniBT_collapse_size
#check @ACC0MiniBTSize.merge_size_ge_mul
#check @ACC0MultiCountCollapse.multiCount_factors
#check @ACC0MultiCountCollapse.hasMultiSymRep_collapses

-- Approximate (RS) route
#check @ACC0RSDepthComposition.toAgree_rs_depth_composition
#check @ACC0PrimeExactExists.exists_exact_toAgree
#check @ACC0PrimeApproxToExact.exact_hasMultiSymRep_of_majorityCorrect
#check @ACC0IntegerDepth3Speedup.modModAnd_depth3_sat_speedup

-- The wall, both sides
#check @ACC0SymmetricEscapesNoGo.or_eq_symmetric
#check @ACC0SymmetricEscapesNoGo.or_cells_le
#check @ACC0ExactDegreeNoGo.or_exact_degree_full

-- Clean-axiom confirmation of the two exact-collapse headlines
#print axioms ACC0MultiCountCollapse.multiCount_factors
#print axioms ACC0MultiCountCollapse.hasMultiSymRep_collapses
#print axioms ACC0RSDepthComposition.toAgree_rs_depth_composition

end PallLean.Paper93.DeepMath.PathB.ACC0IntegerExactArcManifest
