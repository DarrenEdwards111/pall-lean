import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedClosureBridge

/-!
# Row-level criterion for Boolean-projected Pi+ raw pullback membership

The corrected Route-C rank blocker is

`PaperScalePiPlusBooleanProjectedRawPullbackGeneratorMembership`.

This file reduces that membership statement to the concrete row identity that
must be proved next: every raw `Pi+⁻¹` pullback of a projected target SPDP row is
itself an ordinary SPDP generator row for the source polynomial `p`.

This is now the sharp algebraic commutation target: it asks for an explicit
source shift witnessing the pulled-back row, with the same degree/support/block
admissibility budget.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Paper283
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-- Exact row-level raw-pullback certificate for Boolean-projected `Pi+`.

For every SPDP generator row of `Pi+ᵦ p`, its raw `Pi+⁻¹` pullback is required
to be a source SPDP generator row of `p`, for some shift `m'` with the same
`ℓ`-degree budget and support inside the same derivative list `S`. -/
def PiPlusBooleanProjectedRawPullbackRowCertificate
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
      ∃ m' : SATDeciderGaugeSpace M n hn2 htb hns,
        m'.totalDegree ≤ ℓ ∧
          m'.vars ⊆ S.toFinset ∧
            piP.equiv.symm
              (mlProj (m * iterDerivList S
                (piPlusBooleanProjectedGauge M n hn2 htb hns piP p))) =
              mlProj (m' * iterDerivList S p)

/-- The row-level certificate implies raw-pullback membership in the source SPDP
subspace. -/
theorem piPlusBooleanProjectedRawPullbackGeneratorMembership_of_rowCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hrow : PiPlusBooleanProjectedRawPullbackRowCertificate
      M n hn2 htb hns piP) :
    PiPlusBooleanProjectedRawPullbackGeneratorMembership M n hn2 htb hns piP := by
  intro κ ℓ p S m hSlen hmdeg hmvars hadm
  rcases hrow κ ℓ p S m hSlen hmdeg hmvars hadm with
    ⟨m', hmdeg', hmvars', hroweq⟩
  rw [hroweq]
  exact Submodule.subset_span
    ⟨S, m', hSlen, hmdeg', hmvars', hadm, rfl⟩

/-- Therefore the row-level certificate implies Boolean-projected backward
transport. -/
theorem piPlusBooleanProjectedBackwardGeneratorTransport_of_rowCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hrow : PiPlusBooleanProjectedRawPullbackRowCertificate
      M n hn2 htb hns piP) :
    PiPlusBooleanProjectedBackwardGeneratorTransport M n hn2 htb hns piP :=
  piPlusBooleanProjectedBackwardGeneratorTransport_of_rawPullbackGeneratorMembership
    M n hn2 htb hns piP
    (piPlusBooleanProjectedRawPullbackGeneratorMembership_of_rowCertificate
      M n hn2 htb hns piP hrow)

/-- Therefore the row-level certificate implies rank monotonicity for the
Boolean-projected `Pi+` gauge. -/
theorem piPlusBooleanProjected_rankMonotonicity_of_rowCertificate
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hrow : PiPlusBooleanProjectedRawPullbackRowCertificate
      M n hn2 htb hns piP) :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns
      (piPlusBooleanProjectedGauge M n hn2 htb hns piP) :=
  piPlusBooleanProjected_rankMonotonicity_of_backwardGeneratorTransport
    M n hn2 htb hns piP
    (piPlusBooleanProjectedBackwardGeneratorTransport_of_rowCertificate
      M n hn2 htb hns piP hrow)

/-- Paper-scale row-level certificate for the concrete Boolean-projected `Pi+`
transform. -/
abbrev PaperScalePiPlusBooleanProjectedRawPullbackRowCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedRawPullbackRowCertificate M (2 ^ 804)
    paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- Paper-scale row certificate implies the current paper-scale raw-pullback
membership blocker. -/
theorem paperScalePiPlusBooleanProjectedRawPullbackGeneratorMembership_of_rowCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hrow : PaperScalePiPlusBooleanProjectedRawPullbackRowCertificate
      M htb hns) :
    PaperScalePiPlusBooleanProjectedRawPullbackGeneratorMembership M htb hns :=
  piPlusBooleanProjectedRawPullbackGeneratorMembership_of_rowCertificate
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hrow

/-- Paper-scale row certificate plus the already-wired Route-B outputs closes
the corrected Boolean-projected Route-C frontier. -/
theorem paperScalePiPlusBooleanProjected_frontier_of_rowCertificate_unprojectedPSide_projectedNP
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hrow : PaperScalePiPlusBooleanProjectedRawPullbackRowCertificate
      M htb hns)
    (hpside : RouteBSATUnprojectedPSideRankBound M (2 ^ 804)
      paperScale_ge_two htb hns)
    (hlower : RouteBSATProjectedNPIdentityMinorLowerBound M (2 ^ 804)
      paperScale_ge_two htb hns
      (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns)) :
    PaperScalePiPlusBooleanProjectedSATGaugeFrontier M htb hns :=
  paperScalePiPlusBooleanProjected_frontier_of_rawPullback_unprojectedPSide_projectedNP
    M htb hns
    (paperScalePiPlusBooleanProjectedRawPullbackGeneratorMembership_of_rowCertificate
      M htb hns hrow)
    hpside hlower

/-- Paper-scale row certificate plus active-template P-side blockers and the
projected NP lower bound closes the corrected Route-C frontier. -/
theorem paperScalePiPlusBooleanProjected_frontier_of_rowCertificate_activeTemplateBlockers_projectedNP
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hrow : PaperScalePiPlusBooleanProjectedRawPullbackRowCertificate
      M htb hns)
    (hblock : CookLevinActiveProfileTemplateCollapseBlockers M (2 ^ 804)
      paperScale_ge_two htb hns)
    (hlower : RouteBSATProjectedNPIdentityMinorLowerBound M (2 ^ 804)
      paperScale_ge_two htb hns
      (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns)) :
    PaperScalePiPlusBooleanProjectedSATGaugeFrontier M htb hns :=
  paperScalePiPlusBooleanProjected_frontier_of_rawPullback_activeTemplateBlockers_projectedNP
    M htb hns
    (paperScalePiPlusBooleanProjectedRawPullbackGeneratorMembership_of_rowCertificate
      M htb hns hrow)
    hblock hlower

/-! ## Axiom audit anchors -/

#print axioms piPlusBooleanProjectedRawPullbackGeneratorMembership_of_rowCertificate
#print axioms piPlusBooleanProjectedBackwardGeneratorTransport_of_rowCertificate
#print axioms piPlusBooleanProjected_rankMonotonicity_of_rowCertificate
#print axioms paperScalePiPlusBooleanProjectedRawPullbackGeneratorMembership_of_rowCertificate
#print axioms paperScalePiPlusBooleanProjected_frontier_of_rowCertificate_unprojectedPSide_projectedNP
#print axioms paperScalePiPlusBooleanProjected_frontier_of_rowCertificate_activeTemplateBlockers_projectedNP

end PallLean.Paper93.DeepMath.PathC
