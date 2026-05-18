import PallLean.Paper93.DeepMath.PathC.PiPlusBoolRankTransport

/-!
# Legacy unprojected SPDP to Boolean-rank bridge

The new Boolean rank surface uses `rawBlockedSpdpSubspace` as the source rows:
these are unprojected rows with the paper-side support condition
`m.vars ⊆ S.toFinset`.  This file connects that source to the older unprojected
`blockedSpdpSubspace` API from `SPDPDefs` by a simple containment.

This gives a migration path for existing unprojected SPDP estimates: if the
older `blockedSpdpRank` is bounded, then the raw source rank is bounded, hence
so is the Boolean quotient rank and, assuming Boolean `Pi+` rank invariance, the
post-`Pi+` Boolean rank.
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

/-- The raw strict Boolean-source row span is contained in the older unprojected
blocked SPDP span with all variables active.  The raw source has the additional
paper support condition `m.vars ⊆ S.toFinset`, so it is a stricter generator
family. -/
theorem rawBlockedSpdpSubspace_le_blockedSpdpSubspace_univ {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ) :
    rawBlockedSpdpSubspace B κ ℓ p ≤
      blockedSpdpSubspace B κ ℓ p Finset.univ := by
  apply Submodule.span_mono
  intro q hq
  rcases hq with ⟨S, m, hlen, hdeg, _hvars, hadm, rfl⟩
  exact ⟨S, m, hlen, hdeg, hadm, by simp, by simp, rfl⟩

/-- The raw strict source rank is bounded by the older unprojected blocked SPDP
rank. -/
theorem rawBlockedSpdpRank_le_blockedSpdpRank_univ {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ) :
    rawBlockedSpdpRank B κ ℓ p ≤ blockedSpdpRank B κ ℓ p Finset.univ := by
  unfold rawBlockedSpdpRank blockedSpdpRank
  exact Submodule.finrank_mono
    (rawBlockedSpdpSubspace_le_blockedSpdpSubspace_univ B κ ℓ p)

/-- A legacy unprojected blocked-rank bound supplies a raw-to-Boolean strict
rank budget. -/
theorem rawToBoolRankBudget_of_blockedSpdpRank_le {n : ℕ}
    {B : BlockPartition n} {κ ℓ C : ℕ} {p : BoolPoly n}
    (h : blockedSpdpRank B κ ℓ
        (p : MvPolynomial (Fin n) ℚ) Finset.univ ≤ C) :
    RawToBoolRankBudget B κ ℓ C p :=
  le_trans
    (rawBlockedSpdpRank_le_blockedSpdpRank_univ B κ ℓ
      (p : MvPolynomial (Fin n) ℚ)) h

/-- A legacy unprojected blocked-rank bound directly gives a Boolean strict rank
bound. -/
theorem boolBlockedSpdpRank_le_of_blockedSpdpRank_le {n : ℕ}
    {B : BlockPartition n} {κ ℓ C : ℕ} {p : BoolPoly n}
    (h : blockedSpdpRank B κ ℓ
        (p : MvPolynomial (Fin n) ℚ) Finset.univ ≤ C) :
    boolBlockedSpdpRank B κ ℓ p ≤ C :=
  boolBlockedSpdpRank_le_of_rawToBoolRankBudget
    (rawToBoolRankBudget_of_blockedSpdpRank_le h)

/-- Route-C strict bridge: Boolean `Pi+` rank invariance plus an old unprojected
blocked-rank estimate for the source polynomial bounds the Boolean rank after
`piPlusBoolLinearMap`. -/
theorem piPlusBoolRank_le_of_rankInvariant_of_blockedSpdpRank_le
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    {κ ℓ C : ℕ}
    {p : BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars}
    (hinv : PiPlusBoolRankInvariant piP)
    (hlegacy : blockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ
        (p : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
        Finset.univ ≤ C) :
    boolBlockedSpdpRank
        (cook_levin_compilation M n hn2 htb hns).partition
        κ ℓ (piPlusBoolLinearMap piP p) ≤ C := by
  exact piPlusBoolRank_le_of_rankInvariant_of_rawBudget piP hinv
    (rawToBoolRankBudget_of_blockedSpdpRank_le hlegacy)

/-! ## Axiom audit anchors -/

#print axioms rawBlockedSpdpSubspace_le_blockedSpdpSubspace_univ
#print axioms rawBlockedSpdpRank_le_blockedSpdpRank_univ
#print axioms rawToBoolRankBudget_of_blockedSpdpRank_le
#print axioms boolBlockedSpdpRank_le_of_blockedSpdpRank_le
#print axioms piPlusBoolRank_le_of_rankInvariant_of_blockedSpdpRank_le

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
