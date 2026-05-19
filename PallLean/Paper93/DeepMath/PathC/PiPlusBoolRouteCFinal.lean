import PallLean.Paper93.DeepMath.PathC.PiPlusBoolFinalBridge

/-!
# Boolean Route-C final no-decider surface

`PiPlusBoolFinalBridge` proves that the Boolean P/NP closure payloads are
mutually inconsistent.  This file packages the final Route-C shape: if a SAT
decider supplies those Boolean closure payloads, then no such decider exists.

This is deliberately an interface, not a fake proof of the remaining payloads:
the hard mathematical obligations remain exactly the Boolean closure inputs
(rank invariance, legacy inclusive P-side source rank bound, and Boolean source
NP lower bound).
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

/-- Route-C final Boolean payload generator: a SAT decider would produce the
Boolean closure inputs.  Keeping this as a separate interface makes the final
logical step reusable while preserving the exact remaining mathematical seams. -/
def PaperScaleCookLevinPiPlusBoolClosureFromDecider
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  DecidesSAT M → PaperScaleCookLevinPiPlusBoolClosureInputs M htb hns

/-- If any SAT decider supplies the Boolean Route-C closure inputs, then that
decider cannot exist. -/
theorem no_decidesSAT_at_paperScale_of_boolClosureFromDecider
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (H : PaperScaleCookLevinPiPlusBoolClosureFromDecider M htb hns) :
    ¬ DecidesSAT M := by
  intro hdec
  exact paperScaleCookLevinPiPlusBoolClosureInputs_incompatible
    M htb hns (H hdec)

/-- Bundled final Boolean Route-C data: all that remains is to show that a
paper-scale SAT decider yields the Boolean closure inputs. -/
structure PaperScaleCookLevinPiPlusBoolRouteCFinalData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  closure_from_decider : PaperScaleCookLevinPiPlusBoolClosureFromDecider M htb hns

/-- Final Boolean Route-C no-decider theorem from the bundled data. -/
theorem no_decidesSAT_at_paperScale_of_boolRouteCFinalData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScaleCookLevinPiPlusBoolRouteCFinalData M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_boolClosureFromDecider
    M htb hns D.closure_from_decider

/-- Expanded final Boolean Route-C theorem with the individual closure fields
visible under a `DecidesSAT` hypothesis. -/
theorem no_decidesSAT_at_paperScale_of_boolPayloadsFromDecider
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (HrankInc : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRankInvariantInc M htb hns)
    (Hrank : DecidesSAT M → PaperScaleCookLevinPiPlusBoolRankInvariant M htb hns)
    (HP : DecidesSAT M → PaperScaleCookLevinLegacyBlockedIncPSideRankBoundOneZero M htb hns)
    (HNP : DecidesSAT M → PaperScaleCookLevinBoolSourceNPLowerBound M htb hns) :
    ¬ DecidesSAT M := by
  apply no_decidesSAT_at_paperScale_of_boolClosureFromDecider M htb hns
  intro hdec
  exact ⟨HrankInc hdec, Hrank hdec, HP hdec, HNP hdec⟩

/-! ## Axiom audit anchors -/

#print axioms no_decidesSAT_at_paperScale_of_boolClosureFromDecider
#print axioms no_decidesSAT_at_paperScale_of_boolRouteCFinalData
#print axioms no_decidesSAT_at_paperScale_of_boolPayloadsFromDecider

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
