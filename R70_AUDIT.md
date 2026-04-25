# R70 PathB / DeepMath Axiom Audit

Date: 2026-04-25

Lean audit file: `PallLean/Paper93/DeepMath/PathB/R70AxiomAudit.lean`

## Classification Rule

`kernel-only` means `#print axioms` reports only:

```text
[propext, Classical.choice, Quot.sound]
```

`custom-dependent` means a project axiom appears in addition to the Lean
kernel axioms.

## Current Findings

| Theorem / wrapper | Status | Custom dependency |
| --- | --- | --- |
| `PallLean.Paper93.DeepMath.paper93_master_statement` | kernel-only | none |
| `PallLean.Paper93.DeepMath.CookLevin.paper_theorem_207` | kernel-only | none |
| `PallLean.Paper93.DeepMath.CookLevin.paper_final_P_ne_NP_via_rank` | kernel-only | none |
| `PallLean.Paper93.DeepMath.CookLevin.paper_theorem_207_concludes_P_ne_NP_hypothesis` | kernel-only | none |
| `PallLean.Paper93.DeepMath.PathB.identity_isAmplituhedronGauge_any` | kernel-only | none |
| `PallLean.Paper93.DeepMath.PathB.gauge_implies_rank` | kernel-only | none |
| `PallLean.Paper93.DeepMath.CookLevin.theorem_207_rank_chain` | kernel-only | none |
| `PallLean.Paper93.DeepMath.PathB.Positroid.all_rounds_r70_final_kernel` | kernel-only | none |
| `PallLean.Paper93.DeepMath.PathB.Positroid.path_b_r70_master_summary` | kernel-only | none |
| `PallLean.Paper93.DeepMath.PathB.Positroid.cumulative_summary_r70_universal_gauge` | kernel-only | none |
| `PallLean.Paper93.DeepMath.PathB.Positroid.cumulative_summary_r70_identity_gauge` | kernel-only | none |
| `PallLean.Paper93.DeepMath.PathB.Positroid.honest_status_r70` | kernel-only | none |
| `PallLean.Paper93.DeepMath.PathB.Positroid.upstream_axiom_remains_r70` | kernel-only | none |
| `PallLean.Paper93.DeepMath.PathB.Positroid.nonIdentity_gauge_bundle_r70` | kernel-only | none |
| `PallLean.Paper93.DeepMath.PathB.Positroid.path_B_positroid_all_rounds_kernel_only` | kernel-only | none |
| `PallLean.Paper93.DeepMath.PathB.path_B_closed_form` | custom-dependent | `GlobalGodMoveGauge.exists_amplituhedron_gauge_for_sat_decider` |
| `PallLean.Paper93.DeepMath.PathB.path_B_concludes_no_PeqNP_Paper` | custom-dependent | `GlobalGodMoveGauge.exists_amplituhedron_gauge_for_sat_decider` |
| `PallLean.Paper93.DeepMath.PathB.path_B_master` | custom-dependent | `GlobalGodMoveGauge.exists_amplituhedron_gauge_for_sat_decider` |
| `PallLean.Paper93.DeepMath.PathB.SATDecider_implies_False` | custom-dependent | `GlobalGodMoveGauge.exists_amplituhedron_gauge_for_sat_decider` |
| `PallLean.Paper93.DeepMath.PathB.SAT_path_B_chain` | custom-dependent | `GlobalGodMoveGauge.exists_amplituhedron_gauge_for_sat_decider` |
| `PallLean.Paper93.DeepMath.PathB.path_B_full_chain` | custom-dependent | `GlobalGodMoveGauge.exists_amplituhedron_gauge_for_sat_decider` |
| `PallLean.Paper93.DeepMath.CookLevin.accesses_paper_unconditional` | custom-dependent | `GlobalGodMoveGauge.exists_amplituhedron_gauge_for_sat_decider` |
| `PaperFaithfulSeparation.P_ne_NP_unconditional` | custom-dependent | `GlobalGodMoveGauge.exists_amplituhedron_gauge_for_sat_decider` |
| `PaperFaithfulSeparation.P_ne_NP_via_rank_sandwich` | custom-dependent | `GlobalGodMoveGauge.exists_amplituhedron_gauge_for_sat_decider` |
| `GlobalGodMoveGauge.exists_rank_sandwich_for_sat_decider` | custom-dependent theorem | `GlobalGodMoveGauge.exists_amplituhedron_gauge_for_sat_decider` |

## Notes

`path_B_closed_form` is mixed: its identity-gauge and rank-chain components
are kernel-only, but the full theorem includes the `PeqNP_Paper -> False`
conjunct, which routes through the current paper-faithful P != NP wrapper.

Historical / alternate custom axioms remain visible in the audit file:

```text
GlobalGodMoveGauge.exists_amplituhedron_gauge
GlobalGodMoveGauge.exists_theorem207_witness
GlobalGodMoveGauge.exists_theorem207_bounds_on_some_poly
```

The current wrapper chain does not print those historical axioms; it prints
`GlobalGodMoveGauge.exists_amplituhedron_gauge_for_sat_decider`.
