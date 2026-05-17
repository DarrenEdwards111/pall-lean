import PallLean.Paper93.DeepMath.PathC.PiPlusBooleanProjectedWindowedMembershipClosure

/-!
# NP-side lower-bound bridge for Boolean-projected Pi+

The final Route-C closure needs the projected NP lower bound for the concrete
Boolean-projected `Pi+ᵦ` gauge.  This file isolates the exact remaining
mathematical content: `Pi+ᵦ` must not decrease the Cook--Levin identity-minor
rank at the NP window.

This is deliberately weaker and cleaner than a global rank-monotonicity claim.
It only asks for the single compiled-polynomial comparison needed by the final
contradiction.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.Paper283
open PaperFaithfulSeparation
open TuringMachine

attribute [local instance] Classical.dec
set_option exponentiation.threshold 1000

/-- NP-window rank nondecrease for the Boolean-projected `Pi+` image of the
compiled Cook--Levin polynomial.  This is the precise NP-side payload needed
from Route C: no global same-window rank monotonicity, only preservation of the
identity-minor lower-bound rank at the final window. -/
def PiPlusBooleanProjectedNPWindowRankNondecreasing
    (M : DTM) (n : Nat) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns) : Prop :=
  mlBlockedSpdpRank
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (compiledPoly (cook_levin_compilation M n hn2 htb hns)) ≤
    mlBlockedSpdpRank
      (cook_levin_compilation M n hn2 htb hns).partition
      (Nat.log 2 n) (Nat.log 2 n)
      (piPlusBooleanProjectedGauge M n hn2 htb hns piP
        (compiledPoly (cook_levin_compilation M n hn2 htb hns)))

/-- Paper-scale abbreviation for the concrete Cook--Levin Boolean-projected
`Pi+` NP-window rank-nondecrease target. -/
abbrev PaperScalePiPlusBooleanProjectedNPWindowRankNondecreasing
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop :=
  PiPlusBooleanProjectedNPWindowRankNondecreasing
    M (2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns)

/-- At any scale where the existing Cook--Levin NP lower bound applies, the
single NP-window rank-nondecrease comparison implies the projected NP lower
bound for `Pi+ᵦ`. -/
theorem routeBSATProjectedNPIdentityMinorLowerBound_of_npWindowRankNondecreasing
    (M : DTM) (n : Nat) (hn : n ≥ 2 ^ 804) (hn2 : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (piP : PiPlusSATTransform M n hn2 htb hns)
    (hnondec : PiPlusBooleanProjectedNPWindowRankNondecreasing
      M n hn2 htb hns piP) :
    RouteBSATProjectedNPIdentityMinorLowerBound M n hn2 htb hns
      (piPlusBooleanProjectedGauge M n hn2 htb hns piP) := by
  unfold RouteBSATProjectedNPIdentityMinorLowerBound
  exact le_trans
    (by
      have hnp := GodMoveReal.compiled_np_lower_bound_any_dtm M n hn htb hns
      convert hnp using 2)
    hnondec

/-- Paper-scale specialization of the NP lower-bound bridge. -/
theorem paperScale_routeBSATProjectedNPIdentityMinorLowerBound_of_npWindowRankNondecreasing
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (hnondec : PaperScalePiPlusBooleanProjectedNPWindowRankNondecreasing
      M htb hns) :
    RouteBSATProjectedNPIdentityMinorLowerBound M (2 ^ 804)
      paperScale_ge_two htb hns
      (cookLevinPiPlusBooleanProjectedGauge_paperScale M htb hns) :=
  routeBSATProjectedNPIdentityMinorLowerBound_of_npWindowRankNondecreasing
    M (2 ^ 804) (le_rfl : 2 ^ 804 ≥ 2 ^ 804) paperScale_ge_two htb hns
    (cookLevinPiPlusSATTransform_paperScale M htb hns) hnondec

/-- Final membership-level one-window closure with the NP side reduced to the
single rank-nondecrease comparison. -/
structure PaperScalePiPlusBooleanProjectedOneWindowAlmostClosedData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804) : Prop where
  windowed_pullback_membership :
    PaperScalePiPlusBooleanProjectedWindowedRawPullbackMembership 1 0 M htb hns
  windowed_p_side_bound :
    RouteBSATWindowedIncPSideRankBound
      1 0 M (2 ^ 804) paperScale_ge_two htb hns
  np_window_rank_nondecreasing :
    PaperScalePiPlusBooleanProjectedNPWindowRankNondecreasing M htb hns

/-- The almost-closed package fills the previous membership-level contradiction
data by deriving the projected NP lower bound from NP-window rank nondecrease. -/
theorem oneWindowMembershipContradictionData_of_almostClosedData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScalePiPlusBooleanProjectedOneWindowAlmostClosedData M htb hns) :
    PaperScalePiPlusBooleanProjectedOneWindowMembershipContradictionData
      M htb hns where
  windowed_pullback_membership := D.windowed_pullback_membership
  windowed_p_side_bound := D.windowed_p_side_bound
  projected_np_lower_bound :=
    paperScale_routeBSATProjectedNPIdentityMinorLowerBound_of_npWindowRankNondecreasing
      M htb hns D.np_window_rank_nondecreasing

/-- One-window final theorem with the NP side reduced to rank nondecrease. -/
theorem no_decidesSAT_at_paperScale_of_oneWindowAlmostClosedData
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (D : PaperScalePiPlusBooleanProjectedOneWindowAlmostClosedData M htb hns) :
    ¬ DecidesSAT M :=
  no_decidesSAT_at_paperScale_of_oneWindowMembershipContradictionData
    M htb hns
    (oneWindowMembershipContradictionData_of_almostClosedData M htb hns D)

/-! ## Axiom audit anchors -/

#print axioms routeBSATProjectedNPIdentityMinorLowerBound_of_npWindowRankNondecreasing
#print axioms paperScale_routeBSATProjectedNPIdentityMinorLowerBound_of_npWindowRankNondecreasing
#print axioms oneWindowMembershipContradictionData_of_almostClosedData
#print axioms no_decidesSAT_at_paperScale_of_oneWindowAlmostClosedData

end PallLean.Paper93.DeepMath.PathC
