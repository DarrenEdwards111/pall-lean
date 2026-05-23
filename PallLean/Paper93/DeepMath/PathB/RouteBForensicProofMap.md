# Route B Forensic Proof Map (Paper-Faithful Audit)

## Goal
Pinpoint exactly where current Route-B closure chains:
1. import Lemma-22/profile-cover style assumptions,
2. collide with NP identity-minor lower bounds,
3. remain salvageable vs. dead.

---

## A. Core strict-target chain (current incompatibility)

### A1) Target identity (same object)
- `PallLean/Paper93/Paper283/RouteBPaperFaithfulTPhiExtraction.lean`
- theorem: `routeBPaperFaithfulTPhiTarget_coupledPoly_eq`
- role: identifies `T_Φ(P_{M',n})` with the strict extracted target object used downstream.

### A2) NP-side same-target lower bound
- `PallLean/Step4Compiler.lean` (namespace `Step252`)
- theorem: `cookLevinStrictFOBTarget_same_target_lower`
- role: `GodMoveSameTargetStrongNPLower` on that exact strict target.

### A3) Arithmetic contradiction core
- `PallLean/PaperFaithfulSeparation.lean`
- theorem: `no_rank_sandwich_at_large_n`
- role: forbids `choose(n/3, log n) ≤ r ≤ n^200` at `n ≥ 2^804`.

### A4) P-side strict transport from template-collapse
- `PallLean/Step4Compiler.lean` (namespace `Step252`)
- theorem: `cookLevinQ_rank_le_from_templateCollapse`
- theorem: `cookLevinQ_rank_le_from_templateCollapse_at_B_total`
- theorem: `DirectRankPackage_cookLevin_strictFOB_source_transport_false_from_templateCollapse`
- role: template-collapse hypothesis drives strict-target contradiction.

### A5) Uniform no-decider consequence
- `PallLean/Paper93/Paper283/RouteBPaperFaithfulTPhiExtraction.lean`
- theorem: `noBoundedSATDeciderAtPaperScale_of_routeBPaperFaithfulTPhi_templateCollapse`
- role: globally packages A4.

### A6) Canonical compatibility endpoint (new)
- `PallLean/Paper93/DeepMath/PathB/Theorem207CompatibilityAudit.lean`
- theorem: `theorem207_strict_target_incompatibility`
- theorem: `theorem207_uniform_incompatibility_strict_target`
- status: **kernel-clean**, proves incompatibility in current strict-target formulation.

---

## B. Where Lemma-22/profile-cover style assumptions enter

### B1) Template-collapse socket (current Bridge-A seam)
- `WithinProfileBound.CookLevinProfileTemplateCollapseLemma` (imported in Step252 chain)
- feeds `ProfileCompression.p_side_rank_bound_for_cook_levin_of_templateCollapse`
- then feeds `cookLevinQ_rank_le_from_templateCollapse*`

### B2) Legacy false-axiom route (explicitly unsafe)
- `SymmetricPower.spdp_profile_generators`
- inconsistent endpoint already present in repo (`...inconsistent_with_np_side : False`)
- archived strict closeout wrappers moved to:
  - `PallLean/Archive/Paper93Unsafe/RouteBExtractionLayerCloseout.lean`
  - `PallLean/Archive/Paper93Unsafe/RouteBRouteCStrictExtractionCloseout.lean`

---

## C. Salvageability classification

## Dead in current strict-target regime
- Any route requiring same-target transported upper bound `Γ(target) ≤ n^200` at paper scale.
- Reason: A1 + A2 + A3 already forbid it.

## Conditionally meaningful (interface only)
- `NFrameGodMoveBridgeA` (`PathB/NFrameGodMoveSeam.lean`): clean proposition interface.
- `routeB_positive_closure_from_nframe_godmove_bridgeA`: clean conditional implication.
- But currently refuted under paper bundle:
  - `not_nframe_godmove_bridgeA_of_PeqNP`
  - `peqnp_false_of_nframe_godmove_bridgeA`

## Honest stable artifacts
- `RouteBPaperInconsistency.lean`
- `GodMoveFrontier.lean`
- `Theorem207CompatibilityAudit.lean`
- `PaperFaithfulRouteBStatus.lean`
- `Paper93FinalReadout.lean` (status readout wired)

---

## D. Concrete next target to reopen positive closure

A positive Route-B closure requires **breaking at least one** strict-chain lock:

1. strict same-target identification lock (A1), or
2. same-target NP-lower applicability lock (A2), or
3. strict transport object/parameter lock in Step252 (A4).

If none of these move, positive closure is blocked by theorem, not by missing engineering.

---

## E. Quick audit commands

```bash
# strict incompatibility (clean)
~/.elan/bin/lake env lean PallLean/Paper93/DeepMath/PathB/Theorem207CompatibilityAudit.lean

# seam impossibility (clean)
~/.elan/bin/lake env lean PallLean/Paper93/DeepMath/PathB/GodMoveFrontier.lean

# bridge-A interface + refutation under paper bundle (clean)
~/.elan/bin/lake env lean PallLean/Paper93/DeepMath/PathB/NFrameGodMoveSeam.lean
```
