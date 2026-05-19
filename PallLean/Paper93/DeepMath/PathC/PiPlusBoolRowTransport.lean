import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRouteCFinal

/-!
# Boolean row-transport interfaces for Route C

Boolean quotient descent is necessary but not sufficient for rank invariance:
SPDP rows involve derivatives and shifts.  This file exposes the exact row-space
transport obligations that imply the Boolean rank-invariance fields used by the
final Route-C closure.
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

/-- Strict Boolean row-space preservation for a concrete `Pi+` transform.
This is the row-level content behind strict Boolean rank invariance. -/
def PiPlusBoolRowPreservation
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  ∀ (κ ℓ : ℕ)
    (p : BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars),
    boolBlockedSpdpSubspace
        (cook_levin_compilation M n hn2 htb hns).partition
        κ ℓ (piPlusBoolLinearMap piP p) =
      boolBlockedSpdpSubspace
        (cook_levin_compilation M n hn2 htb hns).partition
        κ ℓ p

/-- Inclusive Boolean row-space preservation for a concrete `Pi+` transform.
This is the row-level content behind inclusive Boolean rank invariance. -/
def PiPlusBoolRowPreservationInc
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  ∀ (κ ℓ : ℕ)
    (p : BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars),
    boolBlockedSpdpSubspaceInc
        (cook_levin_compilation M n hn2 htb hns).partition
        κ ℓ (piPlusBoolLinearMap piP p) =
      boolBlockedSpdpSubspaceInc
        (cook_levin_compilation M n hn2 htb hns).partition
        κ ℓ p

/-- Row preservation implies strict Boolean rank invariance. -/
theorem piPlusBoolRankInvariant_of_rowPreservation
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hrow : PiPlusBoolRowPreservation piP) :
    PiPlusBoolRankInvariant piP := by
  intro κ ℓ p
  unfold boolBlockedSpdpRank
  rw [hrow κ ℓ p]

/-- Inclusive row preservation implies inclusive Boolean rank invariance. -/
theorem piPlusBoolRankInvariantInc_of_rowPreservationInc
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hrow : PiPlusBoolRowPreservationInc piP) :
    PiPlusBoolRankInvariantInc piP := by
  intro κ ℓ p
  unfold boolBlockedSpdpRankInc
  rw [hrow κ ℓ p]

/-- Paper-scale strict Boolean row-preservation obligation for the concrete
Cook-Levin `Pi+` transform. -/
abbrev PaperScaleCookLevinPiPlusBoolRowPreservation
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBoolRowPreservation (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- Paper-scale inclusive Boolean row-preservation obligation for the concrete
Cook-Levin `Pi+` transform. -/
abbrev PaperScaleCookLevinPiPlusBoolRowPreservationInc
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBoolRowPreservationInc (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- Paper-scale strict row preservation implies the strict rank-invariance field
used by the NP-side Boolean certificate. -/
theorem paperScaleCookLevinPiPlusBoolRankInvariant_of_rowPreservation
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hrow : PaperScaleCookLevinPiPlusBoolRowPreservation M htb hns) :
    PaperScaleCookLevinPiPlusBoolRankInvariant M htb hns :=
  piPlusBoolRankInvariant_of_rowPreservation
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hrow

/-- Paper-scale inclusive row preservation implies the inclusive rank-invariance
field used by the P-side Boolean certificate. -/
theorem paperScaleCookLevinPiPlusBoolRankInvariantInc_of_rowPreservationInc
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hrow : PaperScaleCookLevinPiPlusBoolRowPreservationInc M htb hns) :
    PaperScaleCookLevinPiPlusBoolRankInvariantInc M htb hns :=
  piPlusBoolRankInvariantInc_of_rowPreservationInc
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hrow

/-- Final closure inputs, but with row-preservation obligations instead of
opaque rank-invariance obligations. -/
def PaperScaleCookLevinPiPlusBoolRowClosureInputs
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PaperScaleCookLevinPiPlusBoolRowPreservationInc M htb hns ∧
  PaperScaleCookLevinPiPlusBoolRowPreservation M htb hns ∧
  PaperScaleCookLevinLegacyBlockedIncPSideRankBoundOneZero M htb hns ∧
  PaperScaleCookLevinBoolSourceNPLowerBound M htb hns

/-- Row-level closure inputs imply the Boolean final contradiction. -/
theorem paperScaleCookLevinPiPlusBoolRowClosureInputs_incompatible
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (H : PaperScaleCookLevinPiPlusBoolRowClosureInputs M htb hns) :
    False := by
  rcases H with ⟨hrowInc, hrow, hP, hNP⟩
  exact paperScaleCookLevinPiPlusBoolClosureInputs_incompatible M htb hns
    ⟨paperScaleCookLevinPiPlusBoolRankInvariantInc_of_rowPreservationInc M htb hns hrowInc,
     paperScaleCookLevinPiPlusBoolRankInvariant_of_rowPreservation M htb hns hrow,
     hP,
     hNP⟩

/-- No-decider surface from row-level Boolean Route-C payloads. -/
theorem no_decidesSAT_at_paperScale_of_boolRowPayloadsFromDecider
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HrowInc : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRowPreservationInc M htb hns)
    (Hrow : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRowPreservation M htb hns)
    (HP : DecidesSAT M → PaperScaleCookLevinLegacyBlockedIncPSideRankBoundOneZero M htb hns)
    (HNP : DecidesSAT M → PaperScaleCookLevinBoolSourceNPLowerBound M htb hns) :
    ¬ DecidesSAT M := by
  intro hdec
  exact paperScaleCookLevinPiPlusBoolRowClosureInputs_incompatible M htb hns
    ⟨HrowInc hdec, Hrow hdec, HP hdec, HNP hdec⟩

/-! ## Axiom audit anchors -/

#print axioms piPlusBoolRankInvariant_of_rowPreservation
#print axioms piPlusBoolRankInvariantInc_of_rowPreservationInc
#print axioms paperScaleCookLevinPiPlusBoolRankInvariant_of_rowPreservation
#print axioms paperScaleCookLevinPiPlusBoolRankInvariantInc_of_rowPreservationInc
#print axioms paperScaleCookLevinPiPlusBoolRowClosureInputs_incompatible
#print axioms no_decidesSAT_at_paperScale_of_boolRowPayloadsFromDecider

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
