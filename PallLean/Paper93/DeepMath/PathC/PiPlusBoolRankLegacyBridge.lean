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

/-- Inclusive unprojected blocked SPDP source span with active-variable
restriction.  This mirrors `blockedSpdpSubspace`, but uses `S.length ≤ κ`, which
is the paper-faithful row indexing convention. -/
noncomputable def blockedSpdpSubspaceInc {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    (activeVars : Finset (Fin n) := Finset.univ) :
    Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  Submodule.span ℚ
    { q | ∃ (S : List (Fin n)) (m : MvPolynomial (Fin n) ℚ),
        S.length ≤ κ ∧ m.totalDegree ≤ ℓ ∧
        isBlockAdmissible B S ∧
        (∀ i ∈ S, i ∈ activeVars) ∧
        (∀ v ∈ m.vars, v ∈ activeVars) ∧
        q = m * iterDerivList S p }

/-- Inclusive unprojected blocked SPDP rank. -/
noncomputable def blockedSpdpRankInc {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    (activeVars : Finset (Fin n) := Finset.univ) : ℕ :=
  Module.finrank ℚ (blockedSpdpSubspaceInc B κ ℓ p activeVars)

/-- Inclusive unprojected blocked rows have bounded total degree. -/
theorem blockedSpdpSubspaceInc_le_restrictTotalDegree {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    (activeVars : Finset (Fin n) := Finset.univ) :
    blockedSpdpSubspaceInc B κ ℓ p activeVars ≤
      MvPolynomial.restrictTotalDegree (Fin n) ℚ (ℓ + p.totalDegree) := by
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨S, m, _hlen, hdeg, _hadm, _hS, _hm, rfl⟩
  have hdeg' : (m * iterDerivList S p).totalDegree ≤ ℓ + p.totalDegree :=
    le_trans (MvPolynomial.totalDegree_mul m (iterDerivList S p))
      (Nat.add_le_add hdeg (totalDegree_iterDerivList_le S p))
  exact (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr hdeg'

/-- Inclusive unprojected blocked spans are finite-dimensional. -/
noncomputable instance blockedSpdpSubspaceInc_finite {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ)
    (activeVars : Finset (Fin n) := Finset.univ) :
    Module.Finite ℚ (blockedSpdpSubspaceInc B κ ℓ p activeVars) := by
  have hle := blockedSpdpSubspaceInc_le_restrictTotalDegree B κ ℓ p activeVars
  have : Module.Finite ℚ (MvPolynomial.restrictTotalDegree (Fin n) ℚ (ℓ + p.totalDegree)) :=
    MvPolynomial.instFiniteSubtypeMemSubmoduleRestrictTotalDegreeOfFinite _ _ _
  exact Module.Finite.of_injective
    (Submodule.inclusion hle)
    (Submodule.inclusion_injective _)

/-- The raw inclusive Boolean-source row span is contained in the inclusive
unprojected blocked SPDP span with all variables active. -/
theorem rawBlockedSpdpSubspaceInc_le_blockedSpdpSubspaceInc_univ {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ) :
    rawBlockedSpdpSubspaceInc B κ ℓ p ≤
      blockedSpdpSubspaceInc B κ ℓ p Finset.univ := by
  apply Submodule.span_mono
  intro q hq
  rcases hq with ⟨S, m, hlen, hdeg, _hvars, hadm, rfl⟩
  exact ⟨S, m, hlen, hdeg, hadm, by simp, by simp, rfl⟩

/-- The raw inclusive source rank is bounded by the inclusive unprojected blocked
SPDP rank. -/
theorem rawBlockedSpdpRankInc_le_blockedSpdpRankInc_univ {n : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) ℚ) :
    rawBlockedSpdpRankInc B κ ℓ p ≤ blockedSpdpRankInc B κ ℓ p Finset.univ := by
  unfold rawBlockedSpdpRankInc blockedSpdpRankInc
  exact Submodule.finrank_mono
    (rawBlockedSpdpSubspaceInc_le_blockedSpdpSubspaceInc_univ B κ ℓ p)

/-- A legacy inclusive unprojected blocked-rank bound supplies a raw-to-Boolean
inclusive rank budget. -/
theorem rawToBoolRankBudgetInc_of_blockedSpdpRankInc_le {n : ℕ}
    {B : BlockPartition n} {κ ℓ C : ℕ} {p : BoolPoly n}
    (h : blockedSpdpRankInc B κ ℓ
        (p : MvPolynomial (Fin n) ℚ) Finset.univ ≤ C) :
    RawToBoolRankBudgetInc B κ ℓ C p :=
  le_trans
    (rawBlockedSpdpRankInc_le_blockedSpdpRankInc_univ B κ ℓ
      (p : MvPolynomial (Fin n) ℚ)) h

/-- A legacy inclusive unprojected blocked-rank bound directly gives a Boolean
inclusive rank bound. -/
theorem boolBlockedSpdpRankInc_le_of_blockedSpdpRankInc_le {n : ℕ}
    {B : BlockPartition n} {κ ℓ C : ℕ} {p : BoolPoly n}
    (h : blockedSpdpRankInc B κ ℓ
        (p : MvPolynomial (Fin n) ℚ) Finset.univ ≤ C) :
    boolBlockedSpdpRankInc B κ ℓ p ≤ C :=
  boolBlockedSpdpRankInc_le_of_rawToBoolRankBudgetInc
    (rawToBoolRankBudgetInc_of_blockedSpdpRankInc_le h)

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

/-- Route-C inclusive bridge: Boolean `Pi+` inclusive rank invariance plus an
inclusive unprojected blocked-rank estimate for the source polynomial bounds the
Boolean inclusive rank after `piPlusBoolLinearMap`. -/
theorem piPlusBoolRankInc_le_of_rankInvariantInc_of_blockedSpdpRankInc_le
    {M : DTM} {n : Nat} {hn2 : n ≥ 2}
    {htb : M.timeBound ≤ 4} {hns : M.numStates ≤ n}
    (piP : PiPlusSATTransform M n hn2 htb hns)
    {κ ℓ C : ℕ}
    {p : BoolPoly (cook_levin_compilation M n hn2 htb hns).numVars}
    (hinv : PiPlusBoolRankInvariantInc piP)
    (hlegacy : blockedSpdpRankInc
        (cook_levin_compilation M n hn2 htb hns).partition κ ℓ
        (p : MvPolynomial (Fin (cook_levin_compilation M n hn2 htb hns).numVars) ℚ)
        Finset.univ ≤ C) :
    boolBlockedSpdpRankInc
        (cook_levin_compilation M n hn2 htb hns).partition
        κ ℓ (piPlusBoolLinearMap piP p) ≤ C := by
  exact piPlusBoolRankInc_le_of_rankInvariantInc_of_rawBudget piP hinv
    (rawToBoolRankBudgetInc_of_blockedSpdpRankInc_le hlegacy)

/-! ## Axiom audit anchors -/

#print axioms rawBlockedSpdpSubspace_le_blockedSpdpSubspace_univ
#print axioms rawBlockedSpdpRank_le_blockedSpdpRank_univ
#print axioms rawToBoolRankBudget_of_blockedSpdpRank_le
#print axioms boolBlockedSpdpRank_le_of_blockedSpdpRank_le
#print axioms piPlusBoolRank_le_of_rankInvariant_of_blockedSpdpRank_le
#print axioms blockedSpdpSubspaceInc_le_restrictTotalDegree
#print axioms blockedSpdpSubspaceInc_finite
#print axioms rawBlockedSpdpSubspaceInc_le_blockedSpdpSubspaceInc_univ
#print axioms rawBlockedSpdpRankInc_le_blockedSpdpRankInc_univ
#print axioms rawToBoolRankBudgetInc_of_blockedSpdpRankInc_le
#print axioms boolBlockedSpdpRankInc_le_of_blockedSpdpRankInc_le
#print axioms piPlusBoolRankInc_le_of_rankInvariantInc_of_blockedSpdpRankInc_le

end BoolPoly

end PallLean.Paper93.DeepMath.PathC
