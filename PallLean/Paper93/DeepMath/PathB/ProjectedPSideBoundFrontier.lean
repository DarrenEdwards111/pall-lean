import PallLean.Paper93.DeepMath.PathB.SATDeciderGaugeFinalTarget

/-!
# Projected P-side bound frontier

This file names the alternate paper-faithful remaining theorem for the
Step247 Cook-Levin output.  The load-bearing P-side statement is the uniform
`ProjectedIdentityMinorConcrete.CookLevinProjectedPSideBound`; its SAT-decider
restriction is equivalent to the existing no-bounded-decider and rich
projection discharge frontiers.

No flat `SATDeciderGaugeMap` witness is constructed here.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation
open TuringMachine

/-- The uniform projected P-side theorem for the concrete Step247 Cook-Levin
output at the paper scale.  The `hn` argument is retained so the theorem has
the same quantifier spine as the final paper-scale SAT-decider frontier. -/
def Step247UniformProjectedPSideTheorem : Prop :=
  ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
    ProjectedIdentityMinorConcrete.CookLevinProjectedPSideBound
      M n hn2 htb hns

/-- The named frontier is definitionally the uniform
`CookLevinProjectedPSideBound` theorem. -/
theorem step247UniformProjectedPSideTheorem_iff_uniformCookLevinProjectedPSideBound :
    Step247UniformProjectedPSideTheorem ↔
      ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
        (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n),
        ProjectedIdentityMinorConcrete.CookLevinProjectedPSideBound
          M n hn2 htb hns := by
  rfl

/-- The same Step247 projected P-side theorem, restricted to the
SAT-decider branch consumed by the final discharge. -/
def Step247SATDeciderProjectedPSideTheorem : Prop :=
  ∀ (M : DTM) (n : Nat) (_hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (_hdec : DecidesSAT M),
    ProjectedIdentityMinorConcrete.CookLevinProjectedPSideBound
      M n hn2 htb hns

/-- A uniform Step247 projected P-side theorem immediately gives the
SAT-decider-restricted version. -/
theorem step247SATDeciderProjectedPSideTheorem_of_uniform
    (hP : Step247UniformProjectedPSideTheorem) :
    Step247SATDeciderProjectedPSideTheorem := by
  intro M n hn hn2 htb hns _hdec
  exact hP M n hn hn2 htb hns

/-- On the SAT-decider branch, the Step247 projected P-side theorem is exactly
the already named no-bounded-SAT-decider frontier.  The forward direction uses
the concrete projected contradiction package; the reverse direction is
vacuous under the contradiction supplied by `NoBoundedSATDeciderAtPaperScale`.
-/
theorem step247SATDeciderProjectedPSideTheorem_iff_noBoundedSATDeciderAtPaperScale :
    Step247SATDeciderProjectedPSideTheorem ↔
      NoBoundedSATDeciderAtPaperScale := by
  constructor
  · intro hP M n hn hn2 htb hns hdec
    exact ProjectedIdentityMinorConcrete.false_of_cookLevinProjectedPSideBound
      M n hn htb hns hn2 (hP M n hn hn2 htb hns hdec)
  · intro hNoBound M n hn hn2 htb hns hdec
    exact False.elim (hNoBound M n hn hn2 htb hns hdec)

/-- Therefore the SAT-decider restriction of the Step247 projected P-side
theorem is equivalent to the rich-projection discharge frontier, without
constructing a flat gauge witness. -/
theorem step247SATDeciderProjectedPSideTheorem_iff_cookLevinRichProjectionDischarge :
    Step247SATDeciderProjectedPSideTheorem ↔
      CookLevinRichProjectionDischarge :=
  step247SATDeciderProjectedPSideTheorem_iff_noBoundedSATDeciderAtPaperScale.trans
    cookLevinRichProjectionDischarge_iff_no_bounded_sat_decider.symm

/-- The uniform Step247 projected P-side theorem rules out bounded
SAT deciders at the paper scale. -/
theorem noBoundedSATDeciderAtPaperScale_of_step247UniformProjectedPSideTheorem
    (hP : Step247UniformProjectedPSideTheorem) :
    NoBoundedSATDeciderAtPaperScale :=
  step247SATDeciderProjectedPSideTheorem_iff_noBoundedSATDeciderAtPaperScale.mp
    (step247SATDeciderProjectedPSideTheorem_of_uniform hP)

/-- The uniform Step247 projected P-side theorem feeds the existing
rich-projection discharge only through the no-decider equivalence, so this
bridge does not assert or build a `SATDeciderGaugeMap`. -/
theorem cookLevinRichProjectionDischarge_of_step247UniformProjectedPSideTheorem
    (hP : Step247UniformProjectedPSideTheorem) :
    CookLevinRichProjectionDischarge :=
  step247SATDeciderProjectedPSideTheorem_iff_cookLevinRichProjectionDischarge.mp
    (step247SATDeciderProjectedPSideTheorem_of_uniform hP)

/-! ## Axiom audit anchors -/

#print axioms step247UniformProjectedPSideTheorem_iff_uniformCookLevinProjectedPSideBound
#print axioms step247SATDeciderProjectedPSideTheorem_of_uniform
#print axioms step247SATDeciderProjectedPSideTheorem_iff_noBoundedSATDeciderAtPaperScale
#print axioms step247SATDeciderProjectedPSideTheorem_iff_cookLevinRichProjectionDischarge
#print axioms noBoundedSATDeciderAtPaperScale_of_step247UniformProjectedPSideTheorem
#print axioms cookLevinRichProjectionDischarge_of_step247UniformProjectedPSideTheorem

end PallLean.Paper93.DeepMath.PathB
