/-
  PallLean/Paper93/DeepMath/PathB/R70AxiomAudit.lean
  =====================================================

  Round-70 axiom audit for the current PathB / DeepMath headline
  theorems.

  This file is intentionally diagnostic: it introduces only trivial audit
  markers and a set of `#print axioms` commands.  The commands are the
  source of truth; comments below record the classification observed at
  creation time.

  Classification rule:

  * Kernel-only means Lean prints only
      [propext, Classical.choice, Quot.sound].

  * Custom-dependent means Lean prints at least one project axiom.  The
    current PathB/PaperFaithful P != NP wrappers expose the single custom
    frontier
      GlobalGodMoveGauge.exists_amplituhedron_gauge_for_sat_decider.

  Current findings:

  * Kernel-only:
      - paper93_master_statement
      - CookLevin.paper_theorem_207
      - CookLevin.paper_final_P_ne_NP_via_rank
      - CookLevin.paper_theorem_207_concludes_P_ne_NP_hypothesis
      - theorem_207_rank_chain and PathB.gauge_implies_rank
      - identity_isAmplituhedronGauge_any
      - all round-70 Positroid summaries printed below
      - zero-gauge non-SAT-decider discharge theorems in GlobalGodMoveGauge

  * Custom-dependent:
      - PathB.path_B_closed_form, because its third conjunct uses the
        paper-faithful `PeqNP_Paper -> False` route.
      - PathB.path_B_concludes_no_PeqNP_Paper and PathB.path_B_master.
      - PathB.SATDecider_implies_False, PathB.SAT_path_B_chain, and
        PathB.path_B_full_chain.
      - CookLevin namespace wrappers around
        PaperFaithfulSeparation.P_ne_NP_unconditional.
      - PaperFaithfulSeparation.P_ne_NP_unconditional and
        P_ne_NP_via_rank_sandwich.
      - GlobalGodMoveGauge.exists_rank_sandwich_for_sat_decider, which is
        now a theorem, not an axiom, but its proof depends on the narrow
        SAT-decider gauge axiom above.

  * Historical / alternate custom axioms are also printed for visibility:
      - GlobalGodMoveGauge.exists_amplituhedron_gauge
      - GlobalGodMoveGauge.exists_theorem207_witness
      - GlobalGodMoveGauge.exists_theorem207_bounds_on_some_poly

  No new axiom declarations, no `sorry`, and no proof content are introduced
  here.
-/

import PallLean.Paper93.DeepMath.PathB.PathBClosedFormFinOne
import PallLean.Paper93.DeepMath.PathB.PathBMasterTheorem
import PallLean.Paper93.DeepMath.Paper93MasterTheorem
import PallLean.Paper93.DeepMath.CookLevin.Theorem207Statement
import PallLean.Paper93.DeepMath.CookLevin.PaperFinalP_ne_NP
import PallLean.Paper93.DeepMath.CookLevin.PaperTheorem207Named
import PallLean.Paper93.DeepMath.CookLevin.Final_P_ne_NP_Wrapper
import PallLean.Paper93.DeepMath.CookLevin.UnconditionalPaperWrapper
import PallLean.Paper93.DeepMath.PathB.SATPathBChain
import PallLean.Paper93.DeepMath.PathB.RankPathBComposer
import PallLean.Paper93.DeepMath.PathB.Positroid.AllRoundsR70FinalKernel
import PallLean.Paper93.DeepMath.PathB.Positroid.PathBR70MasterSummary
import PallLean.Paper93.DeepMath.PathB.Positroid.CumulativeSummaryR70
import PallLean.Paper93.DeepMath.PathB.Positroid.HonestStatusR70
import PallLean.Paper93.DeepMath.PathB.Positroid.NonIdentityGaugeBundleR70
import PallLean.Paper93.DeepMath.PathB.Positroid.RoundsSummary
import PallLean.GlobalGodMoveGauge
import PallLean.PaperFaithfulSeparation

namespace PallLean.Paper93.DeepMath.PathB

/-! ### Audit anchors -/

/-- The audit file itself is kernel-only by construction. -/
theorem r70_axiom_audit_file_kernel_only : True := trivial

/-- Marker for the current custom frontier recorded by this audit. -/
theorem r70_custom_frontier_is_narrow_sat_decider_gauge : True := trivial

end PallLean.Paper93.DeepMath.PathB

/-!
### Component split for `path_B_closed_form`

The first two ingredients of `path_B_closed_form` are kernel-only: identity
gauge existence and the rank chain.  The full theorem becomes
custom-dependent only because it also contains the final
`PeqNP_Paper -> False` conjunct.
-/

#print axioms PallLean.Paper93.DeepMath.PathB.r70_axiom_audit_file_kernel_only
#print axioms PallLean.Paper93.DeepMath.PathB.identity_isAmplituhedronGauge_any
#print axioms PallLean.Paper93.DeepMath.PathB.gauge_implies_rank
#print axioms PallLean.Paper93.DeepMath.CookLevin.theorem_207_rank_chain
#print axioms PallLean.Paper93.DeepMath.PathB.path_B_concludes_no_PeqNP_Paper

/-! ### Required PathB / DeepMath headline theorems -/

#print axioms PallLean.Paper93.DeepMath.PathB.path_B_closed_form
#print axioms PallLean.Paper93.DeepMath.paper93_master_statement
#print axioms PallLean.Paper93.DeepMath.CookLevin.paper_theorem_207
#print axioms PallLean.Paper93.DeepMath.CookLevin.paper_final_P_ne_NP_via_rank
#print axioms PallLean.Paper93.DeepMath.CookLevin.paper_theorem_207_concludes_P_ne_NP_hypothesis

/-! ### Latest round-70 all-rounds and summary layer -/

#print axioms PallLean.Paper93.DeepMath.PathB.Positroid.all_rounds_r70_final_kernel
#print axioms PallLean.Paper93.DeepMath.PathB.Positroid.path_b_r70_master_summary
#print axioms PallLean.Paper93.DeepMath.PathB.Positroid.cumulative_summary_r70_universal_gauge
#print axioms PallLean.Paper93.DeepMath.PathB.Positroid.cumulative_summary_r70_identity_gauge
#print axioms PallLean.Paper93.DeepMath.PathB.Positroid.honest_status_r70
#print axioms PallLean.Paper93.DeepMath.PathB.Positroid.upstream_axiom_remains_r70
#print axioms PallLean.Paper93.DeepMath.PathB.Positroid.nonIdentity_gauge_bundle_r70
#print axioms PallLean.Paper93.DeepMath.PathB.Positroid.path_B_positroid_all_rounds_kernel_only

/-! ### Upstream gauge-dependent wrappers -/

#print axioms PallLean.Paper93.DeepMath.PathB.path_B_master
#print axioms PallLean.Paper93.DeepMath.PathB.SATDecider_implies_False
#print axioms PallLean.Paper93.DeepMath.PathB.SAT_path_B_chain
#print axioms PallLean.Paper93.DeepMath.PathB.path_B_full_chain
#print axioms PallLean.Paper93.DeepMath.CookLevin.accesses_paper_unconditional
#print axioms PallLean.Paper93.DeepMath.CookLevin.PeqNP_Paper_False_via_rank_chain
#print axioms PallLean.Paper93.DeepMath.CookLevin.paper_faithful_unconditional_accessible
#print axioms PallLean.Paper93.DeepMath.CookLevin.paper_faithful_unconditional_arrow
#print axioms PallLean.Paper93.DeepMath.CookLevin.paper_faithful_unconditional_imp
#print axioms PallLean.Paper93.DeepMath.CookLevin.isEmpty_PeqNP_Paper
#print axioms PallLean.Paper93.DeepMath.CookLevin.exists_PeqNP_Paper_elim
#print axioms PaperFaithfulSeparation.P_ne_NP_unconditional
#print axioms PaperFaithfulSeparation.P_ne_NP_via_rank_sandwich

/-! ### Custom frontier and alternate historical axioms -/

#print axioms GlobalGodMoveGauge.exists_rank_sandwich_for_sat_decider
#print axioms GlobalGodMoveGauge.exists_amplituhedron_gauge_for_sat_decider
#print axioms GlobalGodMoveGauge.exists_amplituhedron_gauge
#print axioms GlobalGodMoveGauge.exists_theorem207_witness
#print axioms GlobalGodMoveGauge.exists_theorem207_bounds_on_some_poly

/-! ### Kernel-only discharge checks around the gauge frontier -/

#print axioms GlobalGodMoveGauge.zeroGauge_isAmplituhedronGauge_of_not_decidesSAT
#print axioms GlobalGodMoveGauge.exists_amplituhedron_gauge_of_not_decidesSAT
#print axioms GlobalGodMoveGauge.exists_amplituhedron_gauge_via_narrow_axiom
#print axioms GlobalGodMoveGauge.exists_theorem207_bounds_on_some_poly_from_narrow_gauge
