import PallLean.Paper93.DeepMath.PathB.PathBSummary
import PallLean.Paper93.DeepMath.PathB.SATDeciderRankStatement
import PallLean.Paper93.DeepMath.PathB.SATBridgeN2Strengthened
import PallLean.Paper93.DeepMath.PathB.Positroid.PathBR70MasterSummary
import PallLean.Paper93.DeepMath.PathB.Positroid.R70DetGeneral
import PallLean.Paper93.DeepMath.PathB.Positroid.NonIdentityGaugeAllN
import PallLean.Paper93.DeepMath.CookLevin.Final_P_ne_NP_Wrapper
import PallLean.GlobalGodMoveGauge
import PallLean.BinomialBound2
import Mathlib.Tactic

set_option exponentiation.threshold 1024

/-!
# Path B R70 final theorem surface

This module is only a wrapper.  It names the exact theorem surfaces that are
currently available and keeps the trust boundary visible:

* `pathB_kernel_only_structural_surface` packages the Path B facts proved
  without custom axioms.
* `pathB_p_ne_np_via_current_upstream_axiom_surface` forwards to the current
  paper-faithful `PeqNP_Paper -> False` theorem, so it carries the current
  upstream separation axiom surface.
* `pathB_if_sat_decider_specific_gauge_discharge` states the remaining
  SAT-decider-specific gauge discharge as an explicit hypothesis and closes the
  same `PeqNP_Paper -> False` conclusion from that hypothesis.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.BridgeB
open PallLean.Paper93.DeepMath.NFrame
open PaperFaithfulSeparation
open MultilinearSPDP
open TuringMachine

/-- The kernel-only Path B structural facts exposed by this final wrapper.

This is deliberately structural: it includes the `n = 2` N-frame minimizer
  surface, the Cook-Levin rank lower-bound surface, the universal identity-gauge
  surface, the non-trivial `n = 2` compiled-gadget SAT-family gauge, and the
  general closed-form determinant identity for every nonempty dimension.
-/
def PathBKernelOnlyStructuralSurface : Prop :=
  (∃ (n : Nat), 0 < n ∧
    (∀ phi : Fin n → Real, ∑ i, phi i = 0 →
      S_NF_alpha 1 (PallLean.Paper93.DeepMath.LPS.completeAdj n) 0 ≤
        S_NF_alpha 1 (PallLean.Paper93.DeepMath.LPS.completeAdj n) phi)) ∧
  (∀ (α : Real) (κ n : Nat), 0 < α → 2 ≤ n → κ ≤ (pocketFamily α κ n).rank) ∧
  (∀ (n : Nat) (𝒥 : Finset (Finset (Fin n))),
    IsAmplituhedronGauge (1 : Matrix (Fin n) (Fin n) Real) 𝒥) ∧
  (∃ α : Real, 0 < α ∧
    IsAmplituhedronGauge (compiledGadget α 2) (satFamily 2) ∧
    compiledGadget α 2 ≠ (1 : Matrix (Fin 2) (Fin 2) Real) ∧
    α = Real.sqrt 2 - 1) ∧
  (∀ n : Nat, 2 ≤ n →
    ∃ A : Matrix (Fin n) (Fin n) Real,
      IsAmplituhedronGauge A (satFamily n) ∧
        A ≠ (1 : Matrix (Fin n) (Fin n) Real)) ∧
  (∀ (α : Real) (n : Nat), 1 ≤ n →
    (compiledGadget α n).det = α * (α + (n : Real)) ^ (n - 1)) ∧
  (∀ α : Real, (compiledGadget α 5).det = α * (α + 5)^4) ∧
  (∀ α : Real, (compiledGadget α 6).det = α * (α + 6)^5)

/-- Kernel-only Path B structural theorem surface.

Axiom expectation: Lean kernel axioms only (`propext`, `Classical.choice`,
`Quot.sound`), with no `GlobalGodMoveGauge.exists_*` custom axiom.
-/
theorem pathB_kernel_only_structural_surface :
    PathBKernelOnlyStructuralSurface := by
  refine ⟨path_B_summary, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun α κ n hα hn => rank_for_SAT_decider_compilation α κ n hα hn
  · exact fun n 𝒥 => identity_isAmplituhedronGauge_any 𝒥
  · exact sat_bridge_n2_strengthened
  · exact fun n hn => Positroid.nonIdentity_gauge_all_n n hn
  · exact fun α n hn => Positroid.compiledGadget_det_general α n hn
  · exact fun α => Positroid.compiledGadget_5x5_det α
  · exact fun α => Positroid.compiledGadget_6x6_det α

/-- The current paper-faithful P != NP theorem shape. -/
def PathBUpstreamAxiomPNESurface : Prop :=
  ∀ (_ : PaperFaithfulSeparation.PeqNP_Paper), False

/-- Current P != NP surface, forwarded through the existing upstream-backed
paper-faithful chain.

Axiom expectation: this is not kernel-only.  It carries the current upstream
custom axiom surface of `PaperFaithfulSeparation.P_ne_NP_unconditional`
(currently routed through the `GlobalGodMoveGauge` SAT-decider gauge/rank
frontier).
-/
theorem pathB_p_ne_np_via_current_upstream_axiom_surface :
    PathBUpstreamAxiomPNESurface :=
  PallLean.Paper93.DeepMath.CookLevin.accesses_paper_unconditional

/-- The still-open SAT-decider-specific gauge discharge, isolated as a
hypothesis.

This is the narrow gauge statement used by the `P_ne_NP_via_narrow_axiom`
route: for a bounded SAT-deciding DTM, construct a linear gauge satisfying
the three fields of `GlobalGodMoveGauge.IsAmplituhedronGauge`.  The wrapper
below does not assert this proposition; it only states what would be enough.
-/
def SATDeciderSpecificGaugeDischarge : Prop :=
  ∀ (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_hdec : DecidesSAT M),
    ∃ (gauge :
        MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) Rat →ₗ[Rat]
          MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) Rat),
      GlobalGodMoveGauge.IsAmplituhedronGauge M n hn hn2 htb hns gauge

/-- Conditional closure from a SAT-decider-specific gauge discharge.

Axiom expectation: kernel-only as a conditional theorem.  The remaining
mathematical work is exactly the explicit hypothesis
`SATDeciderSpecificGaugeDischarge`; the proof below does not call
`GlobalGodMoveGauge.exists_amplituhedron_gauge_for_sat_decider` or the
upstream `P_ne_NP_unconditional` wrapper.
-/
theorem pathB_if_sat_decider_specific_gauge_discharge
    (hGauge : SATDeciderSpecificGaugeDischarge) :
    PathBUpstreamAxiomPNESurface := by
  dsimp [SATDeciderSpecificGaugeDischarge] at hGauge
  intro hPeqNP
  set n := 2 ^ 804 with hn_def
  have hn₀ : n ≥ 2 ^ 804 := le_refl _
  have hn2 : n ≥ 2 := by
    calc
      2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
  have hns_n : hPeqNP.decider.numStates ≤ n :=
    le_trans hPeqNP.numStates_bound (le_refl _)
  obtain ⟨gauge, hgauge⟩ :=
    hGauge hPeqNP.decider n hn₀ hn2 hPeqNP.timeBound_le hns_n
      hPeqNP.decides_3sat
  have hP : mlBlockedSpdpRank
      (cook_levin_compilation hPeqNP.decider n hn2 hPeqNP.timeBound_le hns_n).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (gauge (compiledPoly (cook_levin_compilation hPeqNP.decider n hn2
        hPeqNP.timeBound_le hns_n))) ≤ n ^ 200 :=
    hgauge.p_side_bound
  have hNP : Nat.choose (n / 3) (Nat.log 2 n) ≤
      mlBlockedSpdpRank
        (cook_levin_compilation hPeqNP.decider n hn2 hPeqNP.timeBound_le hns_n).partition
        (Nat.log 2 n) (Nat.log 2 n)
        (gauge (compiledPoly (cook_levin_compilation hPeqNP.decider n hn2
          hPeqNP.timeBound_le hns_n))) :=
    hgauge.preserves_identity_minor_for_sat_deciders hPeqNP.decides_3sat
  have hn20 : n ≥ 2 ^ 20 :=
    le_trans (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 20 ≤ 804)) hn₀
  have hbin : n ^ (Nat.log 2 n / 4) ≤ Nat.choose (n / 30) (Nat.log 2 n) :=
    BinomialBound.binomial_lower_bound_concrete n hn20
  have hmono : Nat.choose (n / 30) (Nat.log 2 n) ≤ Nat.choose (n / 3) (Nat.log 2 n) :=
    Nat.choose_le_choose (Nat.log 2 n) (by omega : n / 30 ≤ n / 3)
  have hchain : n ^ (Nat.log 2 n / 4) ≤ n ^ 200 :=
    le_trans (le_trans (le_trans hbin hmono) hNP) hP
  have hlog : 804 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hn₀
  have hdiv : 201 ≤ Nat.log 2 n / 4 := by omega
  have hcontra : n ^ 201 ≤ n ^ 200 :=
    le_trans (Nat.pow_le_pow_right (by omega : 1 ≤ n) hdiv) hchain
  exact absurd hcontra
    (not_le_of_gt (Nat.pow_lt_pow_right (by omega : 1 < n) (by omega : 200 < 201)))

/-!
## Axiom audit anchors

The expected surfaces are:

* `pathB_kernel_only_structural_surface`: no custom axioms.
* `pathB_p_ne_np_via_current_upstream_axiom_surface`: current upstream
  `GlobalGodMoveGauge` custom axiom surface.
* `pathB_if_sat_decider_specific_gauge_discharge`: no custom axiom; the missing
  gauge construction is an explicit theorem hypothesis.
-/
#print axioms pathB_kernel_only_structural_surface
#print axioms pathB_p_ne_np_via_current_upstream_axiom_surface
#print axioms pathB_if_sat_decider_specific_gauge_discharge

end PallLean.Paper93.DeepMath.PathB
