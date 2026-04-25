import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeFinalTarget
import PallLean.Paper93.TruZeroArg

set_option exponentiation.threshold 1000

/-!
# SAT-decider gauge bridge from honest per-type spanning

This file connects the honest `CookLevinPerTypeSpanning_universal` frontier to
the PathB SAT-decider discharge surface.  It routes through the existing
concrete `W_σ` / F5-G4 template-collapse infrastructure and then reuses the
already landed equivalence between the rich projection discharge and
`NoBoundedSATDeciderAtPaperScale`.

No legacy `spdp_profile_generators` route is imported or used.
-/

namespace PallLean.Paper93.DeepMath.PathB

open TuringMachine
open PaperFaithfulSeparation
open SymmetricPowerBound
open WithinProfileBound
open PallLean.Paper93.Spanning
open PallLean.Paper93.Wiring

private theorem ge_four_of_ge_two_pow_804 {n : Nat} (hn : n ≥ 2 ^ 804) :
    n ≥ 4 := by
  have hfour : (4 : Nat) ≤ 2 ^ 804 := by
    calc
      (4 : Nat) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ 804 := Nat.pow_le_pow_right (by omega) (by omega)
  exact le_trans hfour hn

/-- The universal per-type spanning frontier supplies a uniform bounded-profile
template collapse for every Cook-Levin SAT-decider instance at the paper scale,
after specializing the existing F5/G4 bridge to the concrete `W_σ` family. -/
theorem cookLevinBoundedProfileTemplateCollapse_of_perTypeSpanning_universal
    (hSpan_univ : CookLevinPerTypeSpanning_universal) :
    ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
      (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
      CookLevinProfileTemplateCollapseLemmaBoundedProfile M n hn2 htb hns := by
  intro M n hn hn2 htb hns
  let hn4 : n ≥ 4 := ge_four_of_ge_two_pow_804 hn
  let σ : Fin 4 ↪ Fin n := Fin.castLEEmb hn4
  let W : ConstraintType → Submodule Rat (MvPolynomial (Fin n) Rat) :=
    fun τ => concreteW n hn4 σ τ
  have hW_fin : ∀ τ, Module.Finite Rat ↥(W τ) := by
    intro τ
    exact concreteW_finite n hn4 σ τ
  have hW_dim : ∀ τ, Module.finrank Rat ↥(W τ) ≤ 3 := by
    intro τ
    exact concreteW_finrank_le_three n hn4 σ τ
  exact cookLevinProfileTemplateCollapseLemmaBoundedProfile_from_perTypeSpanning
    M n hn2 htb hns W hW_fin hW_dim
    (hSpan_univ M n hn2 htb hns W)

/-- Honest per-type spanning rules out bounded SAT deciders at the paper scale
through the existing PathB bounded-profile template-collapse bridge. -/
theorem noBoundedSATDeciderAtPaperScale_of_perTypeSpanning_universal
    (hSpan_univ : CookLevinPerTypeSpanning_universal) :
    NoBoundedSATDeciderAtPaperScale :=
  noBoundedSATDeciderAtPaperScale_of_cookLevinBoundedProfileTemplateCollapse
    (cookLevinBoundedProfileTemplateCollapse_of_perTypeSpanning_universal hSpan_univ)

/-- Honest per-type spanning discharges the explicit three-field SAT-decider
gauge subgoal frontier, via the no-bounded-decider equivalence. -/
theorem satDeciderSpecificGaugeSubgoalDischarge_of_perTypeSpanning_universal
    (hSpan_univ : CookLevinPerTypeSpanning_universal) :
    SATDeciderSpecificGaugeSubgoalDischarge :=
  satDeciderSpecificGaugeSubgoalDischarge_of_no_bounded_sat_decider
    (noBoundedSATDeciderAtPaperScale_of_perTypeSpanning_universal hSpan_univ)

/-- Honest per-type spanning discharges the integrated rich projection target
for the Cook-Levin SAT-decider branch. -/
theorem cookLevinRichProjectionDischarge_of_perTypeSpanning_universal
    (hSpan_univ : CookLevinPerTypeSpanning_universal) :
    CookLevinRichProjectionDischarge :=
  cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.mpr
    (noBoundedSATDeciderAtPaperScale_of_perTypeSpanning_universal hSpan_univ)

/-- The same residual spanning hypothesis also feeds the existing TruZeroArg
headline `P ≠ NP` theorem, recording that this file uses the same final
composition spine rather than a legacy profile-generator route. -/
theorem p_ne_np_of_perTypeSpanning_universal
    (hSpan_univ : CookLevinPerTypeSpanning_universal) :
    Step4Compiler.P ≠ Step4Compiler.NP :=
  PallLean.Paper93.P_ne_NP_truly_zero hSpan_univ

/-! ## Axiom audit anchors -/

#print axioms cookLevinBoundedProfileTemplateCollapse_of_perTypeSpanning_universal
#print axioms noBoundedSATDeciderAtPaperScale_of_perTypeSpanning_universal
#print axioms satDeciderSpecificGaugeSubgoalDischarge_of_perTypeSpanning_universal
#print axioms cookLevinRichProjectionDischarge_of_perTypeSpanning_universal
#print axioms p_ne_np_of_perTypeSpanning_universal

end PallLean.Paper93.DeepMath.PathB
