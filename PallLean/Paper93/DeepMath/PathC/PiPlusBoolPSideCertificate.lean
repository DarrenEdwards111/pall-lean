import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRankPaperScale

/-!
# Boolean-ambient P-side certificate for Route C

This file packages the P-side rank estimate in the new Boolean ambient.  The
source compiled polynomial is first lifted into `BoolPoly`; the concrete
paper-scale `Pi+` map is then applied in the Boolean ambient; and the target
rank is the inclusive Boolean SPDP rank at the enlarged window.

The main theorem says that a legacy inclusive unprojected blocked-rank estimate,
together with the concrete paper-scale Boolean `Pi+` rank-invariance obligation,
discharges this Boolean P-side certificate.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec

namespace BoolPoly

/-- The compiled Cook-Levin polynomial as an element of the Boolean ambient. -/
noncomputable def compiledBoolPoly
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) :
    BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars :=
  liftToBool (compiledPoly (cook_levin_compilation M n hn2 htb hns))

/-- Concrete paper-scale compiled polynomial in the Boolean ambient. -/
noncomputable def paperScaleCompiledBoolPoly
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    BoolPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars :=
  compiledBoolPoly M (2 ^ 804) paperScale_ge_two htb hns

/-- Boolean-ambient P-side bound after the concrete paper-scale Cook-Levin `Pi+`
map, at an enlarged inclusive window. -/
def PaperScaleCookLevinPiPlusBoolPSideRankBound
    (extraK extraL : Nat)
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  boolBlockedSpdpRankInc
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    (Nat.log 2 (2 ^ 804) + extraK) (Nat.log 2 (2 ^ 804) + extraL)
    (piPlusBoolLinearMap (cookLevinPiPlusSATTransform_paperScale M htb hns)
      (paperScaleCompiledBoolPoly M htb hns)) ≤ (2 ^ 804) ^ 200

/-- Legacy inclusive unprojected P-side rank estimate for the Boolean-lifted
compiled polynomial.  This is the source-side estimate consumed by the new
Boolean bridge. -/
def PaperScaleCookLevinLegacyBlockedIncPSideRankBound
    (extraK extraL : Nat)
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  blockedSpdpRankInc
    (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
    (Nat.log 2 (2 ^ 804) + extraK) (Nat.log 2 (2 ^ 804) + extraL)
    ((paperScaleCompiledBoolPoly M htb hns) :
      MvPolynomial (Fin (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).numVars) ℚ)
    Finset.univ ≤ (2 ^ 804) ^ 200

/-- Legacy inclusive P-side rank plus Boolean `Pi+` rank invariance discharges
the new Boolean-ambient P-side certificate. -/
theorem paperScaleCookLevinPiPlusBoolPSideRankBound_of_legacyBlockedInc
    (extraK extraL : Nat)
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinv : PaperScaleCookLevinPiPlusBoolRankInvariantInc M htb hns)
    (hlegacy : PaperScaleCookLevinLegacyBlockedIncPSideRankBound
      extraK extraL M htb hns) :
    PaperScaleCookLevinPiPlusBoolPSideRankBound extraK extraL M htb hns := by
  unfold PaperScaleCookLevinPiPlusBoolPSideRankBound
  exact paperScaleCookLevinPiPlusBoolRankInc_le_of_rankInvariantInc_of_blockedSpdpRankInc_le
    M htb hns hinv hlegacy

/-- One-zero paper-scale Boolean P-side certificate. -/
abbrev PaperScaleCookLevinPiPlusBoolPSideRankBoundOneZero
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PaperScaleCookLevinPiPlusBoolPSideRankBound 1 0 M htb hns

/-- One-zero legacy source certificate. -/
abbrev PaperScaleCookLevinLegacyBlockedIncPSideRankBoundOneZero
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PaperScaleCookLevinLegacyBlockedIncPSideRankBound 1 0 M htb hns

/-- One-zero specialization of the Boolean P-side certificate bridge. -/
theorem paperScaleCookLevinPiPlusBoolPSideRankBoundOneZero_of_legacyBlockedInc
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinv : PaperScaleCookLevinPiPlusBoolRankInvariantInc M htb hns)
    (hlegacy : PaperScaleCookLevinLegacyBlockedIncPSideRankBoundOneZero M htb hns) :
    PaperScaleCookLevinPiPlusBoolPSideRankBoundOneZero M htb hns :=
  paperScaleCookLevinPiPlusBoolPSideRankBound_of_legacyBlockedInc
    1 0 M htb hns hinv hlegacy

/-! ## Axiom audit anchors -/

#print axioms paperScaleCookLevinPiPlusBoolPSideRankBound_of_legacyBlockedInc
#print axioms paperScaleCookLevinPiPlusBoolPSideRankBoundOneZero_of_legacyBlockedInc

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
