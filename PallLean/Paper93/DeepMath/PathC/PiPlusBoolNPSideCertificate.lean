import PallLean.Paper93.DeepMath.PathC.PiPlusBoolPSideCertificate

/-!
# Boolean-ambient NP-side certificate for Route C

This is the honest Boolean-quotient analogue of the NP-side lower-bound package.
Unlike the P-side, an old full-ring lower bound does **not** automatically
survive quotienting into `BoolPoly`: Boolean normalization can identify rows.
So this file isolates the exact Boolean NP obligation.

The package has two parts:
* a source Boolean NP lower bound for the compiled polynomial; and
* nondecrease of the Boolean NP-window rank under the concrete paper-scale
  `Pi+` map.

A Boolean `Pi+` rank-invariance theorem discharges the nondecrease part.  The
source Boolean lower bound remains a genuine mathematical payload, not hidden
behind the obsolete raw/full-ring socket.
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

/-- Boolean NP-window source lower bound for the compiled Cook-Levin polynomial
at paper scale.  This is the quotient-safe replacement for trying to reuse the
full-ring `mlBlockedSpdpRank` NP lower bound directly. -/
def PaperScaleCookLevinBoolSourceNPLowerBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  Nat.choose ((2 ^ 804) / 3) (Nat.log 2 (2 ^ 804)) ≤
    boolBlockedSpdpRank
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
      (paperScaleCompiledBoolPoly M htb hns)

/-- Boolean NP-window rank nondecrease for the concrete paper-scale Cook-Levin
`Pi+` map. -/
def PaperScaleCookLevinPiPlusBoolNPWindowRankNondecreasing
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  boolBlockedSpdpRank
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
      (paperScaleCompiledBoolPoly M htb hns) ≤
    boolBlockedSpdpRank
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
      (piPlusBoolLinearMap (cookLevinPiPlusSATTransform_paperScale M htb hns)
        (paperScaleCompiledBoolPoly M htb hns))

/-- Boolean post-`Pi+` NP lower bound at the paper-scale NP window. -/
def PaperScaleCookLevinPiPlusBoolNPLowerBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  Nat.choose ((2 ^ 804) / 3) (Nat.log 2 (2 ^ 804)) ≤
    boolBlockedSpdpRank
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
      (piPlusBoolLinearMap (cookLevinPiPlusSATTransform_paperScale M htb hns)
        (paperScaleCompiledBoolPoly M htb hns))

/-- Boolean rank invariance discharges the Boolean NP-window nondecrease
obligation. -/
theorem paperScaleCookLevinPiPlusBoolNPWindowRankNondecreasing_of_rankInvariant
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hinv : PaperScaleCookLevinPiPlusBoolRankInvariant M htb hns) :
    PaperScaleCookLevinPiPlusBoolNPWindowRankNondecreasing M htb hns := by
  unfold PaperScaleCookLevinPiPlusBoolNPWindowRankNondecreasing
  exact le_of_eq ((hinv (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
    (paperScaleCompiledBoolPoly M htb hns)).symm)

/-- Source Boolean NP lower bound plus Boolean NP-window nondecrease gives the
post-`Pi+` Boolean NP lower bound. -/
theorem paperScaleCookLevinPiPlusBoolNPLowerBound_of_sourceLower_of_nondecreasing
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hsource : PaperScaleCookLevinBoolSourceNPLowerBound M htb hns)
    (hnondec : PaperScaleCookLevinPiPlusBoolNPWindowRankNondecreasing M htb hns) :
    PaperScaleCookLevinPiPlusBoolNPLowerBound M htb hns := by
  unfold PaperScaleCookLevinBoolSourceNPLowerBound
    PaperScaleCookLevinPiPlusBoolNPWindowRankNondecreasing
    PaperScaleCookLevinPiPlusBoolNPLowerBound at *
  exact le_trans hsource hnondec

/-- Source Boolean NP lower bound plus Boolean rank invariance gives the
post-`Pi+` Boolean NP lower bound. -/
theorem paperScaleCookLevinPiPlusBoolNPLowerBound_of_sourceLower_of_rankInvariant
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hsource : PaperScaleCookLevinBoolSourceNPLowerBound M htb hns)
    (hinv : PaperScaleCookLevinPiPlusBoolRankInvariant M htb hns) :
    PaperScaleCookLevinPiPlusBoolNPLowerBound M htb hns :=
  paperScaleCookLevinPiPlusBoolNPLowerBound_of_sourceLower_of_nondecreasing
    M htb hns hsource
    (paperScaleCookLevinPiPlusBoolNPWindowRankNondecreasing_of_rankInvariant
      M htb hns hinv)

/-- Bundle of Boolean NP-side data sufficient to derive the post-`Pi+` Boolean
NP lower bound. -/
structure PaperScaleCookLevinPiPlusBoolNPSideCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  source_lower : PaperScaleCookLevinBoolSourceNPLowerBound M htb hns
  rank_nondecreasing : PaperScaleCookLevinPiPlusBoolNPWindowRankNondecreasing M htb hns

/-- The bundled Boolean NP-side certificate gives the post-`Pi+` Boolean NP
lower bound. -/
theorem paperScaleCookLevinPiPlusBoolNPLowerBound_of_npSideCertificate
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScaleCookLevinPiPlusBoolNPSideCertificate M htb hns) :
    PaperScaleCookLevinPiPlusBoolNPLowerBound M htb hns :=
  paperScaleCookLevinPiPlusBoolNPLowerBound_of_sourceLower_of_nondecreasing
    M htb hns D.source_lower D.rank_nondecreasing

/-! ## Axiom audit anchors -/

#print axioms paperScaleCookLevinPiPlusBoolNPWindowRankNondecreasing_of_rankInvariant
#print axioms paperScaleCookLevinPiPlusBoolNPLowerBound_of_sourceLower_of_nondecreasing
#print axioms paperScaleCookLevinPiPlusBoolNPLowerBound_of_sourceLower_of_rankInvariant
#print axioms paperScaleCookLevinPiPlusBoolNPLowerBound_of_npSideCertificate

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
