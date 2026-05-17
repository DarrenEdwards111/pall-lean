import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedAction

/-!
# Rank monotonicity for Boolean-projected Pi+

After the local obstruction, Route C uses the Boolean-projected action

`Pi+ᵦ = booleanNormalize ∘ Pi+`.

This action is not claimed to be an equivalence.  Therefore the right rank
criterion is not equality of SPDP ranks; it is the SAT-gauge monotonicity
inequality

`rank(Pi+ᵦ p) ≤ rank(p)`.

This file proves the finite-dimensional bridge: it is enough to show that every
SPDP generator for `Pi+ᵦ p` lies in the image of the SPDP subspace for `p` under
`Pi+ᵦ`.  Then `Submodule.finrank_map_le` gives the rank inequality.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

/-- Backward generator transport for the Boolean-projected `Pi+` action.

Every SPDP generator of the projected polynomial `Pi+ᵦ p` must already lie in
the image under `Pi+ᵦ` of the SPDP subspace of `p`.  This is the exact generator
criterion needed for rank monotonicity of the projected gauge. -/
def PiPlusBooleanProjectedBackwardGeneratorTransport
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
      mlProj (m * iterDerivList S
        (piPlusBooleanProjectedGauge M n hn2 htb hns piP p)) ∈
        Submodule.map (piPlusBooleanProjectedGauge M n hn2 htb hns piP)
          (mlBlockedSpdpSubspace
            (cook_levin_compilation M n hn2 htb hns).partition κ ℓ p)

/-- Backward generator transport gives the subspace inclusion needed for rank
monotonicity. -/
theorem piPlusBooleanProjectedSubspace_le_map_of_backwardGeneratorTransport
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hback : PiPlusBooleanProjectedBackwardGeneratorTransport M n hn2 htb hns piP)
    (κ ℓ : Nat) (p : SATDeciderGaugeSpace M n hn2 htb hns) :
      mlBlockedSpdpSubspace
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ
        (piPlusBooleanProjectedGauge M n hn2 htb hns piP p) ≤
    Submodule.map (piPlusBooleanProjectedGauge M n hn2 htb hns piP)
        (mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition κ ℓ p) := by
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨S, m, hlen, hdeg, hvars, hadm, hq⟩
  rw [hq]
  exact hback κ ℓ p S m hlen hdeg hvars hadm

/-- Backward generator transport proves SAT-gauge rank monotonicity for the
Boolean-projected `Pi+` gauge. -/
theorem piPlusBooleanProjected_rankMonotonicity_of_backwardGeneratorTransport
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hback : PiPlusBooleanProjectedBackwardGeneratorTransport M n hn2 htb hns piP) :
    SATDeciderGaugeRankMonotonicity M n hn2 htb hns
      (piPlusBooleanProjectedGauge M n hn2 htb hns piP) := by
  intro κ ℓ p
  unfold mlBlockedSpdpRank
  calc
    Module.finrank ℚ
        (mlBlockedSpdpSubspace
          (cook_levin_compilation M n hn2 htb hns).partition κ ℓ
          (piPlusBooleanProjectedGauge M n hn2 htb hns piP p))
        ≤ Module.finrank ℚ
            (Submodule.map (piPlusBooleanProjectedGauge M n hn2 htb hns piP)
              (mlBlockedSpdpSubspace
                (cook_levin_compilation M n hn2 htb hns).partition κ ℓ p)) :=
          Submodule.finrank_mono
            (piPlusBooleanProjectedSubspace_le_map_of_backwardGeneratorTransport
              M n hn2 htb hns piP hback κ ℓ p)
    _ ≤ Module.finrank ℚ
          (mlBlockedSpdpSubspace
            (cook_levin_compilation M n hn2 htb hns).partition κ ℓ p) :=
          Submodule.finrank_map_le _ _

/-- Paper-scale backward generator transport for the concrete Boolean-projected
`Pi+` action. -/
abbrev PaperScalePiPlusBooleanProjectedBackwardGeneratorTransport
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedBackwardGeneratorTransport M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- Paper-scale backward generator transport proves rank monotonicity for the
concrete Boolean-projected `Pi+` gauge. -/
theorem cookLevinPiPlusBooleanProjected_rankMonotonicity_paperScale_of_backwardGeneratorTransport
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hback : PaperScalePiPlusBooleanProjectedBackwardGeneratorTransport M htb hns) :
    SATDeciderGaugeRankMonotonicity M (2 ^ 804) paperScale_ge_two htb hns
      (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns) := by
  exact piPlusBooleanProjected_rankMonotonicity_of_backwardGeneratorTransport
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hback

/-! ## Axiom audit anchors -/

#print axioms piPlusBooleanProjectedSubspace_le_map_of_backwardGeneratorTransport
#print axioms piPlusBooleanProjected_rankMonotonicity_of_backwardGeneratorTransport
#print axioms cookLevinPiPlusBooleanProjected_rankMonotonicity_paperScale_of_backwardGeneratorTransport

end PallLean.Paper93.DeepMath.PathC
