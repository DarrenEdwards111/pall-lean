import PallLean.Paper93.DeepMath.PathC.PiPlusBoolNPRepresentativeCriterion

/-!
# Boolean normality criterion for NP representative exactness

`PiPlusBoolNPRepresentativeCriterion` used the strong condition that the raw
Cook--Levin compiled polynomial equals its `BoolPoly` representative.  This file
rewrites that condition into the more direct algebraic target:

`zeroProfileBooleanNormalize compiledPoly = compiledPoly`.

That is the clean normal-form seam.  If it fails, the next step must be a real
Boolean derivative/product compatibility theorem rather than representative
identity.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

namespace BoolPoly

/-- A polynomial is already in the Boolean normal-form representative if Boolean
normalization fixes it. -/
def IsBooleanNormal {n : ℕ} (p : MvPolynomial (Fin n) ℚ) : Prop :=
  zeroProfileBooleanNormalize p = p

/-- At paper scale, the Cook--Levin compiled polynomial is Boolean-normal. -/
def PaperScaleCookLevinCompiledBooleanNormal
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  IsBooleanNormal
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Boolean normality is exactly representative exactness for `liftToBool`. -/
theorem representativeExact_of_booleanNormal {n : ℕ}
    (q : MvPolynomial (Fin n) ℚ)
    (h : IsBooleanNormal q) :
    q = ((liftToBool q : BoolPoly n) : MvPolynomial (Fin n) ℚ) := by
  unfold IsBooleanNormal at h
  change q = zeroProfileBooleanNormalize q
  exact h.symm

/-- Conversely, representative exactness says Boolean normalization fixes the
polynomial. -/
theorem booleanNormal_of_representativeExact {n : ℕ}
    (q : MvPolynomial (Fin n) ℚ)
    (h : q = ((liftToBool q : BoolPoly n) : MvPolynomial (Fin n) ℚ)) :
    IsBooleanNormal q := by
  unfold IsBooleanNormal
  exact h.symm

/-- Boolean normality iff representative exactness. -/
theorem booleanNormal_iff_representativeExact {n : ℕ}
    (q : MvPolynomial (Fin n) ℚ) :
    IsBooleanNormal q ↔
      q = ((liftToBool q : BoolPoly n) : MvPolynomial (Fin n) ℚ) :=
  ⟨representativeExact_of_booleanNormal q,
   booleanNormal_of_representativeExact q⟩

/-- Paper-scale Boolean normality gives the representative-exactness field used
by the previous closure layer. -/
theorem paperScaleCookLevinCompiledBoolRepresentativeExact_of_booleanNormal
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hnorm : PaperScaleCookLevinCompiledBooleanNormal M htb hns) :
    PaperScaleCookLevinCompiledBoolRepresentativeExact M htb hns := by
  unfold PaperScaleCookLevinCompiledBooleanNormal
    PaperScaleCookLevinCompiledBoolRepresentativeExact at *
  change compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns) =
    ((liftToBool
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)) :
        BoolPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) :
          MvPolynomial
            (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) ℚ)
  exact representativeExact_of_booleanNormal
    (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))
    hnorm

/-- Final no-decider surface where NP image exactness is supplied by Boolean
normality of the compiled polynomial. -/
theorem no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPNormalKernelFromDecider
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HrowInc : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRowPreservationInc M htb hns)
    (Hrow : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRowPreservation M htb hns)
    (HP : DecidesSAT M → PaperScaleCookLevinLegacyBlockedIncPSideRankBoundOneZero M htb hns)
    (Hnorm : DecidesSAT M → PaperScaleCookLevinCompiledBooleanNormal M htb hns)
    (Hker : DecidesSAT M → PaperScaleCookLevinRawToBoolSourceNPKernelDisjoint M htb hns) :
    ¬ DecidesSAT M := by
  apply no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPRepresentativeKernelFromDecider
    M htb hns HrowInc Hrow HP
  · intro hdec
    exact paperScaleCookLevinCompiledBoolRepresentativeExact_of_booleanNormal
      M htb hns (Hnorm hdec)
  · exact Hker

/-! ## Axiom audit anchors -/

#print axioms representativeExact_of_booleanNormal
#print axioms booleanNormal_of_representativeExact
#print axioms booleanNormal_iff_representativeExact
#print axioms paperScaleCookLevinCompiledBoolRepresentativeExact_of_booleanNormal
#print axioms no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPNormalKernelFromDecider

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
