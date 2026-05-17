import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedRowObstruction

/-!
# Windowed rank bridge for Boolean-projected Pi+

The exact same-window row certificate is too strong (see
`PiPlusBooleanProjectedRowObstruction`).  This file wires the corrected
windowed certificate into a usable rank statement: target rows at `(κ,ℓ)` are
controlled by source inclusive-SPDP rows at `(κ + extraK, ℓ + extraL)`.

This is not yet the final paper-scale `SATDeciderGaugeRankMonotonicity` socket;
it is the honest intermediate theorem needed after discovering the local
same-window obstruction.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-- Windowed raw-pullback membership: the raw inverse `Pi+` pullback of each
projected target generator at `(κ,ℓ)` lies in the *inclusive* source SPDP
subspace with enlarged window `(κ + extraK, ℓ + extraL)`. -/
def PiPlusBooleanProjectedWindowedRawPullbackGeneratorMembership
    (extraK extraL : Nat)
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
        mlBlockedSpdpSubspaceInc
          (cook_levin_compilation M n hn2 htb hns).partition
          (κ + extraK) (ℓ + extraL) p

/-- The corrected windowed row certificate implies windowed raw-pullback
membership. -/
theorem piPlusBooleanProjectedWindowedRawPullbackGeneratorMembership_of_windowedRowCertificate
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hrow : PiPlusBooleanProjectedWindowedRawPullbackRowCertificate
      extraK extraL M n hn2 htb hns piP) :
    PiPlusBooleanProjectedWindowedRawPullbackGeneratorMembership
      extraK extraL M n hn2 htb hns piP := by
  intro κ ℓ p S m hSlen hmdeg hmvars hadm
  rcases hrow κ ℓ p S m hSlen hmdeg hmvars hadm with
    ⟨κ', ℓ', S', m', hκ', hℓ', hSlen', hmdeg', hmvars', hadm', hroweq⟩
  rw [hroweq]
  have hSle : S'.length ≤ κ + extraK := by
    rw [hSlen']
    exact hκ'
  have hmle : m'.totalDegree ≤ ℓ + extraL := le_trans hmdeg' hℓ'
  exact Submodule.subset_span
    ⟨S', m', hSle, hmle, hmvars', hadm', rfl⟩

/-- Windowed pullback membership gives the target subspace inclusion into the
Boolean-projected image of the enlarged inclusive source SPDP subspace. -/
theorem piPlusBooleanProjectedSubspace_le_map_inc_of_windowedRawPullbackMembership
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hpull : PiPlusBooleanProjectedWindowedRawPullbackGeneratorMembership
      extraK extraL M n hn2 htb hns piP)
    (κ ℓ : Nat) (p : SATDeciderGaugeSpace M n hn2 htb hns) :
      mlBlockedSpdpSubspace
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ
        (piPlusBooleanProjectedGauge M n hn2 htb hns piP p) ≤
    Submodule.map (piPlusBooleanProjectedGauge M n hn2 htb hns piP)
        (mlBlockedSpdpSubspaceInc
          (cook_levin_compilation M n hn2 htb hns).partition
          (κ + extraK) (ℓ + extraL) p) := by
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨S, m, hlen, hdeg, hvars, hadm, hq⟩
  rw [hq]
  refine ⟨piP.equiv.symm
      (mlProj (m * iterDerivList S
        (piPlusBooleanProjectedGauge M n hn2 htb hns piP p))),
    hpull κ ℓ p S m hlen hdeg hvars hadm, ?_⟩
  exact piPlusBooleanProjectedGauge_rawPullback_targetGenerator
    M n hn2 htb hns piP p S m

/-- Windowed pullback membership yields the honest inflated-rank inequality:
the projected target strict rank at `(κ,ℓ)` is bounded by the source inclusive
rank at `(κ + extraK, ℓ + extraL)`. -/
theorem piPlusBooleanProjected_rank_le_rankInc_of_windowedRawPullbackMembership
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hpull : PiPlusBooleanProjectedWindowedRawPullbackGeneratorMembership
      extraK extraL M n hn2 htb hns piP)
    (κ ℓ : Nat) (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ
        (piPlusBooleanProjectedGauge M n hn2 htb hns piP p) ≤
      mlBlockedSpdpRankInc
        (cook_levin_compilation M n hn2 htb hns).partition
        (κ + extraK) (ℓ + extraL) p := by
  unfold mlBlockedSpdpRank mlBlockedSpdpRankInc
  calc
    Module.finrank ℚ
        (mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition κ ℓ
          (piPlusBooleanProjectedGauge M n hn2 htb hns piP p))
        ≤ Module.finrank ℚ
            (Submodule.map (piPlusBooleanProjectedGauge M n hn2 htb hns piP)
              (mlBlockedSpdpSubspaceInc
                (cook_levin_compilation M n hn2 htb hns).partition
                (κ + extraK) (ℓ + extraL) p)) :=
          Submodule.finrank_mono
            (piPlusBooleanProjectedSubspace_le_map_inc_of_windowedRawPullbackMembership
              extraK extraL M n hn2 htb hns piP hpull κ ℓ p)
    _ ≤ Module.finrank ℚ
          (mlBlockedSpdpSubspaceInc
            (cook_levin_compilation M n hn2 htb hns).partition
            (κ + extraK) (ℓ + extraL) p) :=
          Submodule.finrank_map_le _ _

/-- Windowed row certificate directly gives the inflated-rank inequality. -/
theorem piPlusBooleanProjected_rank_le_rankInc_of_windowedRowCertificate
    (extraK extraL : Nat)
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hrow : PiPlusBooleanProjectedWindowedRawPullbackRowCertificate
      extraK extraL M n hn2 htb hns piP)
    (κ ℓ : Nat) (p : SATDeciderGaugeSpace M n hn2 htb hns) :
    mlBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ
        (piPlusBooleanProjectedGauge M n hn2 htb hns piP p) ≤
      mlBlockedSpdpRankInc
        (cook_levin_compilation M n hn2 htb hns).partition
        (κ + extraK) (ℓ + extraL) p :=
  piPlusBooleanProjected_rank_le_rankInc_of_windowedRawPullbackMembership
    extraK extraL M n hn2 htb hns piP
    (piPlusBooleanProjectedWindowedRawPullbackGeneratorMembership_of_windowedRowCertificate
      extraK extraL M n hn2 htb hns piP hrow)
    κ ℓ p

/-- Paper-scale windowed row certificate gives the inflated-rank inequality for
the concrete Cook--Levin `Pi+ᵦ` gauge. -/
theorem cookLevinPiPlusBooleanProjected_rank_le_rankInc_paperScale_of_windowedRowCertificate
    (extraK extraL : Nat)
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hrow : PaperScalePiPlusBooleanProjectedWindowedRawPullbackRowCertificate
      extraK extraL M htb hns)
    (κ ℓ : Nat) (p : SATDeciderGaugeSpace M (2 ^ 804) paperScale_ge_two htb hns) :
    mlBlockedSpdpRank
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition κ ℓ
        (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns p) ≤
      mlBlockedSpdpRankInc
        (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
        (κ + extraK) (ℓ + extraL) p :=
  piPlusBooleanProjected_rank_le_rankInc_of_windowedRowCertificate
    extraK extraL M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hrow κ ℓ p

/-! ## Axiom audit anchors -/

#print axioms piPlusBooleanProjectedWindowedRawPullbackGeneratorMembership_of_windowedRowCertificate
#print axioms piPlusBooleanProjectedSubspace_le_map_inc_of_windowedRawPullbackMembership
#print axioms piPlusBooleanProjected_rank_le_rankInc_of_windowedRawPullbackMembership
#print axioms piPlusBooleanProjected_rank_le_rankInc_of_windowedRowCertificate
#print axioms cookLevinPiPlusBooleanProjected_rank_le_rankInc_paperScale_of_windowedRowCertificate

end PallLean.Paper93.DeepMath.PathC
