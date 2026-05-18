import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRankBudget

/-!
# Boolean Pi+ rank-budget transport

This file connects the new Boolean rank surface to closure-style P-side
budgets.  Once a Boolean `Pi+` action is rank-monotone (or rank-invariant), a
raw full-ring source budget for `p` gives the corresponding Boolean SPDP budget
for `Pi+(p)`.

This is deliberately an interface layer: the hard payload remains proving the
actual `Pi+` Boolean rank invariance/descent facts, but downstream Route-C
statements can now consume them in the right ambient.
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

/-- A Boolean rank-monotone map transports a raw strict source budget for `p`
into a Boolean strict budget for `T p`. -/
theorem boolBlockedSpdpRank_map_le_of_monotone_of_rawBudget {n : ℕ}
    {B : BlockPartition n} {T : BoolPoly n →ₗ[ℚ] BoolPoly n}
    {κ ℓ C : ℕ} {p : BoolPoly n}
    (hmono : BoolRankMonotonicity B T)
    (hraw : RawToBoolRankBudget B κ ℓ C p) :
    boolBlockedSpdpRank B κ ℓ (T p) ≤ C := by
  exact le_trans (hmono κ ℓ p)
    (boolBlockedSpdpRank_le_of_rawToBoolRankBudget hraw)

/-- Inclusive version: a Boolean rank-monotone map transports a raw inclusive
source budget for `p` into a Boolean inclusive budget for `T p`. -/
theorem boolBlockedSpdpRankInc_map_le_of_monotone_of_rawBudget {n : ℕ}
    {B : BlockPartition n} {T : BoolPoly n →ₗ[ℚ] BoolPoly n}
    {κ ℓ C : ℕ} {p : BoolPoly n}
    (hmono : BoolRankMonotonicityInc B T)
    (hraw : RawToBoolRankBudgetInc B κ ℓ C p) :
    boolBlockedSpdpRankInc B κ ℓ (T p) ≤ C := by
  exact le_trans (hmono κ ℓ p)
    (boolBlockedSpdpRankInc_le_of_rawToBoolRankBudgetInc hraw)

/-- Route-C strict interface: Boolean `Pi+` rank invariance plus a raw source
budget bounds the Boolean rank after the concrete `piPlusBoolLinearMap`. -/
theorem piPlusBoolRank_le_of_rankInvariant_of_rawBudget
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    {κ ℓ C : ℕ}
    {p : BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars}
    (hinv : PiPlusBoolRankInvariant piP)
    (hraw : RawToBoolRankBudget
      (cook_levin_compilation M n hn2 htb hns).partition κ ℓ C p) :
    boolBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        κ ℓ (piPlusBoolLinearMap piP p) ≤ C := by
  exact boolBlockedSpdpRank_map_le_of_monotone_of_rawBudget
    (hmono := boolRankMonotonicity_of_rankInvariant piP hinv)
    (hraw := hraw)

/-- Route-C inclusive interface: Boolean `Pi+` rank invariance plus a raw source
budget bounds the Boolean inclusive rank after `piPlusBoolLinearMap`. -/
theorem piPlusBoolRankInc_le_of_rankInvariantInc_of_rawBudget
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    {κ ℓ C : ℕ}
    {p : BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars}
    (hinv : PiPlusBoolRankInvariantInc piP)
    (hraw : RawToBoolRankBudgetInc
      (cook_levin_compilation M n hn2 htb hns).partition κ ℓ C p) :
    boolBlockedSpdpRankInc
        (cook_levin_compilation M n hn2 htb hns).partition
        κ ℓ (piPlusBoolLinearMap piP p) ≤ C := by
  exact boolBlockedSpdpRankInc_map_le_of_monotone_of_rawBudget
    (hmono := boolRankMonotonicityInc_of_rankInvariantInc piP hinv)
    (hraw := hraw)

/-- Paper-scale strict route interface specialized to `n = 2^804`. -/
abbrev PaperScalePiPlusBoolRankBudgetTransport
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (piP : PiPlusSATTransform M (2 ^ 804) paperScale_ge_two htb hns) : Prop :=
  PiPlusBoolRankInvariant piP

/-- Paper-scale inclusive route interface specialized to `n = 2^804`. -/
abbrev PaperScalePiPlusBoolRankBudgetTransportInc
    (M : DTM) (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ 2 ^ 804)
    (piP : PiPlusSATTransform M (2 ^ 804) paperScale_ge_two htb hns) : Prop :=
  PiPlusBoolRankInvariantInc piP

/-! ## Axiom audit anchors -/

#print axioms boolBlockedSpdpRank_map_le_of_monotone_of_rawBudget
#print axioms boolBlockedSpdpRankInc_map_le_of_monotone_of_rawBudget
#print axioms piPlusBoolRank_le_of_rankInvariant_of_rawBudget
#print axioms piPlusBoolRankInc_le_of_rankInvariantInc_of_rawBudget

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
