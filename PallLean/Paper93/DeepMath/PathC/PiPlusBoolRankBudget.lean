import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRankBridge

/-!
# Boolean rank budget bridge

The previous bridge identifies Boolean SPDP row spaces with the image of raw
full-ring row spaces under `liftToBoolLinearMap`.  This file packages the
resulting dimension/rank inequalities.

These lemmas are intentionally modest but important migration plumbing: any old
proof that gives a finite-dimensional/bounded raw row span can now feed a
Boolean-ambient SPDP rank bound by `Submodule.finrank_map_le`, without invoking
the obsolete full-ring zero-profile socket.
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

/-- Raw strict-κ source rank before quotienting into the Boolean ambient. -/
noncomputable def rawBlockedSpdpRank {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ) : ℕ :=
  Module.finrank ℚ (rawBlockedSpdpSubspace B κ ℓ p)

/-- Raw inclusive-κ source rank before quotienting into the Boolean ambient. -/
noncomputable def rawBlockedSpdpRankInc {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ) : ℕ :=
  Module.finrank ℚ (rawBlockedSpdpSubspaceInc B κ ℓ p)

/-- Boolean strict rank is bounded by the corresponding raw full-ring source
rank.  The only mathematical input is that quotient/image maps do not increase
finrank. -/
theorem boolBlockedSpdpRank_le_rawBlockedSpdpRank {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : BoolPoly n) :
    boolBlockedSpdpRank B κ ℓ p ≤
      rawBlockedSpdpRank B κ ℓ (p : MvPolynomial (Fin n) ℚ) := by
  unfold boolBlockedSpdpRank rawBlockedSpdpRank
  rw [← map_liftToBool_rawBlockedSpdpSubspace_eq_bool]
  exact Submodule.finrank_map_le _ _

/-- Boolean inclusive rank is bounded by the corresponding raw full-ring source
rank. -/
theorem boolBlockedSpdpRankInc_le_rawBlockedSpdpRankInc {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : BoolPoly n) :
    boolBlockedSpdpRankInc B κ ℓ p ≤
      rawBlockedSpdpRankInc B κ ℓ (p : MvPolynomial (Fin n) ℚ) := by
  unfold boolBlockedSpdpRankInc rawBlockedSpdpRankInc
  rw [← map_liftToBool_rawBlockedSpdpSubspaceInc_eq_bool]
  exact Submodule.finrank_map_le _ _

/-- A raw strict rank budget immediately gives a Boolean strict rank budget. -/
theorem boolBlockedSpdpRank_le_of_rawBlockedSpdpRank_le {n : ℕ}
    {B : BlockPartition n} {κ ℓ C : ℕ} {p : BoolPoly n}
    (hraw : rawBlockedSpdpRank B κ ℓ (p : MvPolynomial (Fin n) ℚ) ≤ C) :
    boolBlockedSpdpRank B κ ℓ p ≤ C :=
  le_trans (boolBlockedSpdpRank_le_rawBlockedSpdpRank B κ ℓ p) hraw

/-- A raw inclusive rank budget immediately gives a Boolean inclusive rank
budget. -/
theorem boolBlockedSpdpRankInc_le_of_rawBlockedSpdpRankInc_le {n : ℕ}
    {B : BlockPartition n} {κ ℓ C : ℕ} {p : BoolPoly n}
    (hraw : rawBlockedSpdpRankInc B κ ℓ (p : MvPolynomial (Fin n) ℚ) ≤ C) :
    boolBlockedSpdpRankInc B κ ℓ p ≤ C :=
  le_trans (boolBlockedSpdpRankInc_le_rawBlockedSpdpRankInc B κ ℓ p) hraw

/-- Interface for migrating old P-side strict raw-rank estimates into the
Boolean ambient. -/
abbrev RawToBoolRankBudget {n : ℕ}
    (B : BlockPartition n) (κ ℓ C : ℕ) (p : BoolPoly n) : Prop :=
  rawBlockedSpdpRank B κ ℓ (p : MvPolynomial (Fin n) ℚ) ≤ C

/-- Interface for migrating old P-side inclusive raw-rank estimates into the
Boolean ambient. -/
abbrev RawToBoolRankBudgetInc {n : ℕ}
    (B : BlockPartition n) (κ ℓ C : ℕ) (p : BoolPoly n) : Prop :=
  rawBlockedSpdpRankInc B κ ℓ (p : MvPolynomial (Fin n) ℚ) ≤ C

/-- The strict migration interface discharges the Boolean rank bound. -/
theorem boolBlockedSpdpRank_le_of_rawToBoolRankBudget {n : ℕ}
    {B : BlockPartition n} {κ ℓ C : ℕ} {p : BoolPoly n}
    (h : RawToBoolRankBudget B κ ℓ C p) :
    boolBlockedSpdpRank B κ ℓ p ≤ C :=
  boolBlockedSpdpRank_le_of_rawBlockedSpdpRank_le h

/-- The inclusive migration interface discharges the Boolean rank bound. -/
theorem boolBlockedSpdpRankInc_le_of_rawToBoolRankBudgetInc {n : ℕ}
    {B : BlockPartition n} {κ ℓ C : ℕ} {p : BoolPoly n}
    (h : RawToBoolRankBudgetInc B κ ℓ C p) :
    boolBlockedSpdpRankInc B κ ℓ p ≤ C :=
  boolBlockedSpdpRankInc_le_of_rawBlockedSpdpRankInc_le h

/-! ## Axiom audit anchors -/

#print axioms boolBlockedSpdpRank_le_rawBlockedSpdpRank
#print axioms boolBlockedSpdpRankInc_le_rawBlockedSpdpRankInc
#print axioms boolBlockedSpdpRank_le_of_rawToBoolRankBudget
#print axioms boolBlockedSpdpRankInc_le_of_rawToBoolRankBudgetInc

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
