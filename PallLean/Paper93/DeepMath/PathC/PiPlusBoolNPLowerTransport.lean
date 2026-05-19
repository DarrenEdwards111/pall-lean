import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRowTransport

/-!
# Boolean NP-source lower-bound transport

The old/full-ring Cook--Levin NP lower bound cannot simply be reused after
Boolean quotienting.  This file isolates the exact transport steps needed to
turn a source NP lower bound into the Boolean-source lower bound used by the
final Boolean Route-C bridge.
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

/-- Raw full-ring source lower bound at the paper-scale NP window, using the
raw row source that maps exactly into the Boolean row space. -/
def PaperScaleCookLevinRawSourceNPLowerBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  Nat.choose ((2 ^ 804) / 3) (Nat.log 2 (2 ^ 804)) ≤
    rawBlockedSpdpRank
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- The precise rank-transport obligation saying Boolean normalization does not
collapse the paper-scale raw NP source rank. -/
def PaperScaleCookLevinRawToBoolSourceNPRankLower
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  rawBlockedSpdpRank
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)) ≤
    boolBlockedSpdpRank
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
      (paperScaleCompiledBoolPoly M htb hns)

/-- Raw source NP lower plus raw-to-Boolean rank noncollapse gives the Boolean
source NP lower used by the final Boolean bridge. -/
theorem paperScaleCookLevinBoolSourceNPLowerBound_of_rawSourceLower_of_rawToBoolLower
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hraw : PaperScaleCookLevinRawSourceNPLowerBound M htb hns)
    (htransport : PaperScaleCookLevinRawToBoolSourceNPRankLower M htb hns) :
    PaperScaleCookLevinBoolSourceNPLowerBound M htb hns := by
  unfold PaperScaleCookLevinRawSourceNPLowerBound
    PaperScaleCookLevinRawToBoolSourceNPRankLower
    PaperScaleCookLevinBoolSourceNPLowerBound at *
  exact le_trans hraw htransport

/-- Legacy/full-ring NP lower bound at paper scale.  This is the shape supplied
by the older Cook--Levin lower-bound theorem. -/
def PaperScaleCookLevinLegacySourceNPLowerBound
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  Nat.choose ((2 ^ 804) / 3) (Nat.log 2 (2 ^ 804)) ≤
    mlBlockedSpdpRank
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Transport obligation from the old legacy/full-ring NP lower rank into the
raw source rank that has an exact Boolean image.  This is not automatic: the raw
source imposes the `m.vars ⊆ S.toFinset` discipline. -/
def PaperScaleCookLevinLegacyToRawSourceNPRankLower
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  mlBlockedSpdpRank
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns)) ≤
    rawBlockedSpdpRank
      (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns).partition
      (Nat.log 2 (2 ^ 804)) (Nat.log 2 (2 ^ 804))
      (compiledPoly (cook_levin_compilation M (2 ^ 804) paperScale_ge_two htb hns))

/-- Legacy NP lower plus legacy-to-raw transport gives the raw source NP lower. -/
theorem paperScaleCookLevinRawSourceNPLowerBound_of_legacyLower_of_legacyToRawLower
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hlegacy : PaperScaleCookLevinLegacySourceNPLowerBound M htb hns)
    (htransport : PaperScaleCookLevinLegacyToRawSourceNPRankLower M htb hns) :
    PaperScaleCookLevinRawSourceNPLowerBound M htb hns := by
  unfold PaperScaleCookLevinLegacySourceNPLowerBound
    PaperScaleCookLevinLegacyToRawSourceNPRankLower
    PaperScaleCookLevinRawSourceNPLowerBound at *
  exact le_trans hlegacy htransport

/-- Legacy NP lower plus both transport obligations gives the Boolean source NP
lower. -/
theorem paperScaleCookLevinBoolSourceNPLowerBound_of_legacyLower_of_transports
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hlegacy : PaperScaleCookLevinLegacySourceNPLowerBound M htb hns)
    (hlegacyToRaw : PaperScaleCookLevinLegacyToRawSourceNPRankLower M htb hns)
    (hrawToBool : PaperScaleCookLevinRawToBoolSourceNPRankLower M htb hns) :
    PaperScaleCookLevinBoolSourceNPLowerBound M htb hns :=
  paperScaleCookLevinBoolSourceNPLowerBound_of_rawSourceLower_of_rawToBoolLower
    M htb hns
    (paperScaleCookLevinRawSourceNPLowerBound_of_legacyLower_of_legacyToRawLower
      M htb hns hlegacy hlegacyToRaw)
    hrawToBool

/-- The existing Cook--Levin NP lower theorem supplies the legacy source NP lower
at paper scale. -/
theorem paperScaleCookLevinLegacySourceNPLowerBound_of_compiledNPLower
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) :
    PaperScaleCookLevinLegacySourceNPLowerBound M htb hns := by
  unfold PaperScaleCookLevinLegacySourceNPLowerBound
  have hnp := GodMoveReal.compiled_np_lower_bound_any_dtm
    M (2 ^ 804) (le_rfl : 2 ^ 804 ≥ 2 ^ 804) htb hns
  convert hnp using 2

/-- Fully expanded no-decider surface where the NP source lower is supplied by
the existing legacy lower theorem plus the two explicit NP transport seams. -/
theorem no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPTransportsFromDecider
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HrowInc : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRowPreservationInc M htb hns)
    (Hrow : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRowPreservation M htb hns)
    (HP : DecidesSAT M → PaperScaleCookLevinLegacyBlockedIncPSideRankBoundOneZero M htb hns)
    (HlegacyToRaw : DecidesSAT M → PaperScaleCookLevinLegacyToRawSourceNPRankLower M htb hns)
    (HrawToBool : DecidesSAT M → PaperScaleCookLevinRawToBoolSourceNPRankLower M htb hns) :
    ¬ DecidesSAT M := by
  apply no_decidesSAT_at_paperScale_of_boolRowPayloadsFromDecider
    M htb hns HrowInc Hrow HP
  intro hdec
  exact paperScaleCookLevinBoolSourceNPLowerBound_of_legacyLower_of_transports
    M htb hns
    (paperScaleCookLevinLegacySourceNPLowerBound_of_compiledNPLower M htb hns)
    (HlegacyToRaw hdec)
    (HrawToBool hdec)

/-! ## Axiom audit anchors -/

#print axioms paperScaleCookLevinBoolSourceNPLowerBound_of_rawSourceLower_of_rawToBoolLower
#print axioms paperScaleCookLevinRawSourceNPLowerBound_of_legacyLower_of_legacyToRawLower
#print axioms paperScaleCookLevinBoolSourceNPLowerBound_of_legacyLower_of_transports
#print axioms paperScaleCookLevinLegacySourceNPLowerBound_of_compiledNPLower
#print axioms no_decidesSAT_at_paperScale_of_boolRowPayloadsAndNPTransportsFromDecider

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
