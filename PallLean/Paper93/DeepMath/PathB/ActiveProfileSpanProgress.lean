import PallLean.Paper93.DeepMath.PathB.CommonSpanProfileCaseSplit
import PallLean.Paper93.Direct.PerTypeComposition

/-!
# Active profile common-span progress

This file works below
`CookLevinAllBoundedProfileCommonSpanLiveProfileCase`.  It isolates the
remaining live histograms into the three active Cook-Levin type coordinates and
provides kernel-checked bridges from existing per-type row-span packages to the
live-profile common-span package.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open PaperFaithfulSeparation
open SymmetricPowerBound
open TuringMachine (DTM)
open WithinProfileBound

attribute [local instance] Classical.dec

/-- A nonzero profile with zero dormant `transitionRight` mass has positive mass
in one of the three active Cook-Levin coordinates. -/
theorem activeProfile_positive_type_of_transitionRight_zero
    {h : ProfileHistogram}
    (htr : h ConstraintType.transitionRight = 0)
    (hne : h ≠ zeroProfileHistogram) :
    0 < h ConstraintType.booleanity ∨
      0 < h ConstraintType.adjacency ∨
        0 < h ConstraintType.transitionLeft := by
  by_contra hnone
  push_neg at hnone
  apply hne
  funext τ
  cases τ with
  | booleanity => exact Nat.eq_zero_of_le_zero (hnone.1)
  | adjacency => exact Nat.eq_zero_of_le_zero (hnone.2.1)
  | transitionLeft => exact Nat.eq_zero_of_le_zero (hnone.2.2)
  | transitionRight => exact htr

/-- Prop-level three-way blocker for the live common-span branch.

The only profiles not already closed by `CommonSpanProfileCaseSplit` have
`transitionRight = 0` and are nonzero.  This blocker asks for the common-span
target separately in the three possible active positive coordinates. -/
def CookLevinActiveProfileTypeCaseBlockers
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  (∀ h : ProfileHistogram,
    ProfileAdmissible (Nat.log 2 n) h →
      h ConstraintType.transitionRight = 0 →
        h ≠ zeroProfileHistogram →
          0 < h ConstraintType.booleanity →
            CookLevinAllBoundedProfileCommonSpanAtProfile M n hn htb hns h) ∧
  (∀ h : ProfileHistogram,
    ProfileAdmissible (Nat.log 2 n) h →
      h ConstraintType.transitionRight = 0 →
        h ≠ zeroProfileHistogram →
          0 < h ConstraintType.adjacency →
            CookLevinAllBoundedProfileCommonSpanAtProfile M n hn htb hns h) ∧
  (∀ h : ProfileHistogram,
    ProfileAdmissible (Nat.log 2 n) h →
      h ConstraintType.transitionRight = 0 →
        h ≠ zeroProfileHistogram →
          0 < h ConstraintType.transitionLeft →
            CookLevinAllBoundedProfileCommonSpanAtProfile M n hn htb hns h)

/-- The active three-way blocker proves the fixed live-profile obligation. -/
theorem cookLevinAllBoundedProfileCommonSpanLiveProfileCase_of_activeTypeCaseBlockers
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (h : ProfileHistogram)
    (hblock : CookLevinActiveProfileTypeCaseBlockers M n hn htb hns) :
    CookLevinAllBoundedProfileCommonSpanLiveProfileCase M n hn htb hns h := by
  intro hadm htr hne
  rcases hblock with ⟨hbool, hadj, hleft⟩
  rcases activeProfile_positive_type_of_transitionRight_zero htr hne with
    hpos | hpos | hpos
  · exact hbool h hadm htr hne hpos
  · exact hadj h hadm htr hne hpos
  · exact hleft h hadm htr hne hpos

/-- The active three-way blocker proves the all-live-profile package. -/
theorem cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_activeTypeCaseBlockers
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hblock : CookLevinActiveProfileTypeCaseBlockers M n hn htb hns) :
    CookLevinAllBoundedProfileCommonSpanLiveProfileCases M n hn htb hns := by
  intro h
  exact
    cookLevinAllBoundedProfileCommonSpanLiveProfileCase_of_activeTypeCaseBlockers
      M n hn htb hns h hblock

/-- A per-type row-span package with finite `W_τ` of dimension at most three
closes any fixed live profile. -/
theorem cookLevinAllBoundedProfileCommonSpanLiveProfileCase_of_perTypeSpanning
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (hSpan : PallLean.Paper93.Spanning.CookLevinPerTypeSpanning
      M n hn htb hns W)
    (h : ProfileHistogram) :
    CookLevinAllBoundedProfileCommonSpanLiveProfileCase M n hn htb hns h := by
  intro hadm _htr _hne
  let bp : BoundedProfile (Nat.log 2 n) := admissibleToBounded hadm
  have htemplate :
      Module.finrank ℚ ↥(PallLean.Paper93.cookLevinPostSpanAt
          M n hn htb hns bp.toHistogram)
        ≤ profileTemplateBound bp.toHistogram :=
    PallLean.Paper93.Spanning.cookLevin_allBoundedProfilePostSpan_finrank_le_from_perTypeSpanning
      M n hn htb hns bp W hW_fin hW_dim hSpan
  have hdim :
      Module.finrank ℚ
          ↥(allBoundedProfilePostSpan
            (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn htb hns).get i)
            (cookLevinConstraintType M n hn htb hns)
            h)
        ≤ withinProfileBound (Nat.log 2 n) := by
    change
      Module.finrank ℚ ↥(PallLean.Paper93.cookLevinPostSpanAt
          M n hn htb hns bp.toHistogram)
        ≤ withinProfileBound (Nat.log 2 n)
    exact le_trans htemplate
      (profileTemplateBound_le_withinProfileBound
        (Nat.log 2 n) bp.toHistogram hadm)
  exact
    cookLevinAllBoundedProfileCommonSpanAtProfile_of_allBoundedProfilePostSpan_finrank
      M n hn htb hns h hdim

/-- A per-type row-span package with finite `W_τ` of dimension at most three
closes all live profiles. -/
theorem cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_perTypeSpanning
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (hSpan : PallLean.Paper93.Spanning.CookLevinPerTypeSpanning
      M n hn htb hns W) :
    CookLevinAllBoundedProfileCommonSpanLiveProfileCases M n hn htb hns := by
  intro h
  exact
    cookLevinAllBoundedProfileCommonSpanLiveProfileCase_of_perTypeSpanning
      M n hn htb hns W hW_fin hW_dim hSpan h

/-- The per-type row-span package supplies the three active type blockers. -/
theorem cookLevinActiveProfileTypeCaseBlockers_of_perTypeSpanning
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ))
    (hW_dim : ∀ τ, Module.finrank ℚ ↥(W τ) ≤ 3)
    (hSpan : PallLean.Paper93.Spanning.CookLevinPerTypeSpanning
      M n hn htb hns W) :
    CookLevinActiveProfileTypeCaseBlockers M n hn htb hns := by
  refine ⟨?_, ?_, ?_⟩ <;>
    intro h hadm htr hne _hpos <;>
      exact
        cookLevinAllBoundedProfileCommonSpanLiveProfileCase_of_perTypeSpanning
          M n hn htb hns W hW_fin hW_dim hSpan h hadm htr hne

/-- ConcreteW row embeddings close any fixed live profile. -/
theorem cookLevinAllBoundedProfileCommonSpanLiveProfileCase_of_concreteW_rowEmbeddings
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4)
    (h : ProfileHistogram) :
    CookLevinAllBoundedProfileCommonSpanLiveProfileCase M n hn htb hns h :=
  cookLevinAllBoundedProfileCommonSpanLiveProfileCase_of_perTypeSpanning
    M n hn htb hns
    (fun τ =>
      PallLean.Paper93.Wiring.concreteW n hn4 (Fin.castLEEmb hn4) τ)
    (fun τ =>
      PallLean.Paper93.Wiring.concreteW_finite
        n hn4 (Fin.castLEEmb hn4) τ)
    (fun τ =>
      PallLean.Paper93.Wiring.concreteW_finrank_le_three
        n hn4 (Fin.castLEEmb hn4) τ)
    hRowEmbeddings h

/-- ConcreteW row embeddings close all live profiles. -/
theorem cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_concreteW_rowEmbeddings
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    CookLevinAllBoundedProfileCommonSpanLiveProfileCases M n hn htb hns := by
  intro h
  exact
    cookLevinAllBoundedProfileCommonSpanLiveProfileCase_of_concreteW_rowEmbeddings
      M n hn htb hns hn4 hRowEmbeddings h

/-- ConcreteW row embeddings supply the three active type blockers. -/
theorem cookLevinActiveProfileTypeCaseBlockers_of_concreteW_rowEmbeddings
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    CookLevinActiveProfileTypeCaseBlockers M n hn htb hns :=
  cookLevinActiveProfileTypeCaseBlockers_of_perTypeSpanning
    M n hn htb hns
    (fun τ =>
      PallLean.Paper93.Wiring.concreteW n hn4 (Fin.castLEEmb hn4) τ)
    (fun τ =>
      PallLean.Paper93.Wiring.concreteW_finite
        n hn4 (Fin.castLEEmb hn4) τ)
    (fun τ =>
      PallLean.Paper93.Wiring.concreteW_finrank_le_three
        n hn4 (Fin.castLEEmb hn4) τ)
    hRowEmbeddings

/-! ## Axiom audit anchors -/

#print axioms activeProfile_positive_type_of_transitionRight_zero
#print axioms cookLevinAllBoundedProfileCommonSpanLiveProfileCase_of_activeTypeCaseBlockers
#print axioms cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_activeTypeCaseBlockers
#print axioms cookLevinAllBoundedProfileCommonSpanLiveProfileCase_of_perTypeSpanning
#print axioms cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_perTypeSpanning
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_perTypeSpanning
#print axioms cookLevinAllBoundedProfileCommonSpanLiveProfileCase_of_concreteW_rowEmbeddings
#print axioms cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_concreteW_rowEmbeddings
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_concreteW_rowEmbeddings

end PallLean.Paper93.DeepMath.PathB
