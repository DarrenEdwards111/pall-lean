import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedFrontier

/-!
# Transport bridge for Boolean-projected Pi+

This file attacks the remaining Route-C rank blocker.  The Boolean-projected
map

`Pi+ᵦ = booleanNormalize ∘ Pi+`

is not injective, but every SPDP generator row on the target side is
multilinear because it is wrapped in `mlProj`.  Hence Boolean normalization fixes
that row.  Since raw `Pi+` is an equivalence, the target row is the projected
image of its raw `Pi+` pullback.

Therefore the remaining mathematical task can be stated as a clean pullback
membership condition: the raw `Pi+⁻¹` pullback of every target generator row
must lie in the original SPDP subspace.  This bridge proves that this condition
implies the actual Boolean-projected backward transport theorem consumed by the
rank criterion.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-- The raw-pullback membership condition sufficient for Boolean-projected
backward transport.

For every SPDP generator row of `Pi+ᵦ p`, pull it back through the raw invertible
`Pi+`.  The condition says this pullback already belongs to the SPDP subspace of
`p`.  Boolean normalization then maps it back to the target row because the row
is multilinear (`mlProj`). -/
def PiPlusBooleanProjectedRawPullbackGeneratorMembership
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  ∀ (κ ℓ : Nat) (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (m : SATDeciderGaugeSpace M n hn2 htb hns),
      S.length = κ →
      m.totalDegree ≤ ℓ →
      m.vars ⊆ S.toFinset →
      isBlockAdmissible (cook_levin_compilation M n hn2 htb hns).partition S →
      piP.equiv.symm
        (mlProj (m * iterDerivList S
          (piPlusBooleanProjectedGauge M n hn2 htb hns piP p))) ∈
        mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition κ ℓ p

/-- Boolean-projected target rows are in the image of their raw `Pi+` pullback.
This is where the Boolean quotient repair is used: `mlProj` makes the target row
multilinear, so `zeroProfileBooleanNormalize` fixes it. -/
theorem piPlusBooleanProjectedGauge_rawPullback_targetGenerator
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (p : SATDeciderGaugeSpace M n hn2 htb hns)
    (S : List (Fin (cook_levin_compilation M n hn2 htb hns).numVars))
    (m : SATDeciderGaugeSpace M n hn2 htb hns) :
    piPlusBooleanProjectedGauge M n hn2 htb hns piP
      (piP.equiv.symm
        (mlProj (m * iterDerivList S
          (piPlusBooleanProjectedGauge M n hn2 htb hns piP p)))) =
      mlProj (m * iterDerivList S
        (piPlusBooleanProjectedGauge M n hn2 htb hns piP p)) := by
  let target : SATDeciderGaugeSpace M n hn2 htb hns :=
    mlProj (m * iterDerivList S
      (piPlusBooleanProjectedGauge M n hn2 htb hns piP p))
  calc
    piPlusBooleanProjectedGauge M n hn2 htb hns piP (piP.equiv.symm target)
        = zeroProfileBooleanNormalize (piP.gauge (piP.equiv.symm target)) := by
          rfl
    _ = zeroProfileBooleanNormalize target := by
          simp [PiPlusSATTransform.gauge, target]
    _ = target := by
          exact zeroProfileBooleanNormalize_mlProj
            (m * iterDerivList S
              (piPlusBooleanProjectedGauge M n hn2 htb hns piP p))

/-- Raw-pullback generator membership implies the actual Boolean-projected
backward transport theorem. -/
theorem piPlusBooleanProjectedBackwardGeneratorTransport_of_rawPullbackGeneratorMembership
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hpull : PiPlusBooleanProjectedRawPullbackGeneratorMembership
      M n hn2 htb hns piP) :
    PiPlusBooleanProjectedBackwardGeneratorTransport M n hn2 htb hns piP := by
  intro κ ℓ p S m hSlen hmdeg hmvars hadm
  refine ⟨piP.equiv.symm
      (mlProj (m * iterDerivList S
        (piPlusBooleanProjectedGauge M n hn2 htb hns piP p))),
    hpull κ ℓ p S m hSlen hmdeg hmvars hadm, ?_⟩
  exact piPlusBooleanProjectedGauge_rawPullback_targetGenerator
    M n hn2 htb hns piP p S m

/-- Paper-scale raw-pullback membership condition for the concrete
Boolean-projected `Pi+` action. -/
abbrev PaperScalePiPlusBooleanProjectedRawPullbackGeneratorMembership
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedRawPullbackGeneratorMembership M (2 ^ 804)
    paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- At paper scale, raw-pullback membership discharges the projected backward
transport blocker. -/
theorem paperScalePiPlusBooleanProjectedBackwardGeneratorTransport_of_rawPullbackGeneratorMembership
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpull : PaperScalePiPlusBooleanProjectedRawPullbackGeneratorMembership
      M htb hns) :
    PaperScalePiPlusBooleanProjectedBackwardGeneratorTransport M htb hns :=
  piPlusBooleanProjectedBackwardGeneratorTransport_of_rawPullbackGeneratorMembership
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hpull

/-- Paper-scale raw-pullback membership gives rank monotonicity for the concrete
Boolean-projected `Pi+` gauge. -/
theorem cookLevinPiPlusBooleanProjected_rankMonotonicity_paperScale_of_rawPullbackGeneratorMembership
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hpull : PaperScalePiPlusBooleanProjectedRawPullbackGeneratorMembership
      M htb hns) :
    SATDeciderGaugeRankMonotonicity M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns) :=
  cookLevinPiPlusBooleanProjected_rankMonotonicity_paperScale_of_backwardGeneratorTransport
    M htb hns
    (paperScalePiPlusBooleanProjectedBackwardGeneratorTransport_of_rawPullbackGeneratorMembership
      M htb hns hpull)

/-! ## Axiom audit anchors -/

#print axioms piPlusBooleanProjectedGauge_rawPullback_targetGenerator
#print axioms piPlusBooleanProjectedBackwardGeneratorTransport_of_rawPullbackGeneratorMembership
#print axioms paperScalePiPlusBooleanProjectedBackwardGeneratorTransport_of_rawPullbackGeneratorMembership
#print axioms cookLevinPiPlusBooleanProjected_rankMonotonicity_paperScale_of_rawPullbackGeneratorMembership

end PallLean.Paper93.DeepMath.PathC
