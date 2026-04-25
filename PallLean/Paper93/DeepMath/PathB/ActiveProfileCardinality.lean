import PallLean.Paper93.DeepMath.PathB.CommonSpanProfileCaseSplit

/-!
# Active bounded-profile cardinality

The ambient `BoundedProfile k` type in `WithinProfileBound` keeps the dormant
`transitionRight` coordinate for compatibility with the older four-coordinate
profile universe.  The concrete Cook-Levin P-side frontier after the checked
case split only has live obligations at profiles with
`transitionRight = 0`.

This file packages that active finite type and its three-coordinate encoding.
The bridge at the end turns the all-histogram live-profile obligation into a
finite active-profile obligation without using the legacy generator package or
any P-versus-NP route.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PaperFaithfulSeparation
open SymmetricPowerBound
open TuringMachine (DTM)
open WithinProfileBound

attribute [local instance] Classical.dec

/-- Active bounded profiles: bounded profiles whose dormant
`transitionRight` coordinate is zero. -/
def ActiveBoundedProfile (κ : ℕ) : Type :=
  { bp : BoundedProfile κ // bp.toHistogram ConstraintType.transitionRight = 0 }

namespace ActiveBoundedProfile

/-- Forget the active side condition. -/
def toBoundedProfile {κ : ℕ} (bp : ActiveBoundedProfile κ) :
    BoundedProfile κ :=
  bp.val

/-- The underlying histogram of an active bounded profile. -/
def toHistogram {κ : ℕ} (bp : ActiveBoundedProfile κ) :
    ProfileHistogram :=
  bp.toBoundedProfile.toHistogram

@[simp] theorem toBoundedProfile_toHistogram {κ : ℕ}
    (bp : ActiveBoundedProfile κ) :
    bp.toBoundedProfile.toHistogram = bp.toHistogram := rfl

@[simp] theorem toHistogram_transitionRight {κ : ℕ}
    (bp : ActiveBoundedProfile κ) :
    bp.toHistogram ConstraintType.transitionRight = 0 :=
  bp.property

theorem toHistogram_component_le {κ : ℕ}
    (bp : ActiveBoundedProfile κ) (τ : ConstraintType) :
    bp.toHistogram τ ≤ κ :=
  bp.toBoundedProfile.property τ

/-- Build an active bounded profile from explicit component bounds and the
active side condition. -/
def ofHistogram {κ : ℕ} (h : ProfileHistogram)
    (hbd : ∀ τ, h τ ≤ κ)
    (htr : h ConstraintType.transitionRight = 0) :
    ActiveBoundedProfile κ :=
  ⟨⟨h, hbd⟩, by simpa [BoundedProfile.toHistogram] using htr⟩

@[simp] theorem ofHistogram_toHistogram {κ : ℕ}
    (h : ProfileHistogram) (hbd : ∀ τ, h τ ≤ κ)
    (htr : h ConstraintType.transitionRight = 0) :
    (ofHistogram h hbd htr).toHistogram = h :=
  rfl

/-- Every admissible active histogram gives an active bounded profile. -/
def ofAdmissible {κ : ℕ} (h : ProfileHistogram)
    (hadm : ProfileAdmissible κ h)
    (htr : h ConstraintType.transitionRight = 0) :
    ActiveBoundedProfile κ :=
  ofHistogram h (admissible_implies_bounded hadm) htr

@[simp] theorem ofAdmissible_toHistogram {κ : ℕ}
    (h : ProfileHistogram) (hadm : ProfileAdmissible κ h)
    (htr : h ConstraintType.transitionRight = 0) :
    (ofAdmissible h hadm htr).toHistogram = h :=
  rfl

/-- Forgetting the active side condition is injective. -/
theorem toBoundedProfile_injective (κ : ℕ) :
    Function.Injective
      (fun bp : ActiveBoundedProfile κ => bp.toBoundedProfile) := by
  intro bp₁ bp₂ h
  exact Subtype.ext h

/-- Active bounded profiles inject into histograms. -/
theorem toHistogram_injective (κ : ℕ) :
    Function.Injective
      (fun bp : ActiveBoundedProfile κ => bp.toHistogram) := by
  intro bp₁ bp₂ h
  apply toBoundedProfile_injective κ
  exact Subtype.ext h

/-- Three-coordinate tuple encoding for active bounded profiles.  It is the
four-coordinate `boundedProfileToTuple` with the dormant zero coordinate
removed. -/
def toTuple {κ : ℕ} (bp : ActiveBoundedProfile κ) :
    Fin (κ + 1) × Fin (κ + 1) × Fin (κ + 1) :=
  (⟨bp.toHistogram ConstraintType.booleanity,
      Nat.lt_succ_of_le (bp.toHistogram_component_le ConstraintType.booleanity)⟩,
   ⟨bp.toHistogram ConstraintType.adjacency,
      Nat.lt_succ_of_le (bp.toHistogram_component_le ConstraintType.adjacency)⟩,
   ⟨bp.toHistogram ConstraintType.transitionLeft,
      Nat.lt_succ_of_le (bp.toHistogram_component_le ConstraintType.transitionLeft)⟩)

/-- The active three-coordinate tuple encoding is injective.

The proof reuses `boundedProfileToTuple_injective`: equality of the three active
coordinates plus the built-in `transitionRight = 0` equality gives equality of
the full four-coordinate bounded-profile tuples. -/
theorem toTuple_injective (κ : ℕ) :
    Function.Injective (fun bp : ActiveBoundedProfile κ => bp.toTuple) := by
  intro bp₁ bp₂ htuple
  apply toBoundedProfile_injective κ
  apply boundedProfileToTuple_injective κ
  rcases bp₁ with ⟨bp₁, hz₁⟩
  rcases bp₂ with ⟨bp₂, hz₂⟩
  simp only [toTuple, toHistogram, toBoundedProfile, BoundedProfile.toHistogram,
    boundedProfileToTuple, Prod.mk.injEq, Fin.mk.injEq] at htuple ⊢
  rcases htuple with ⟨hbool, hadj, hleft⟩
  have hright :
      bp₁.val ConstraintType.transitionRight =
        bp₂.val ConstraintType.transitionRight := by
    simpa [BoundedProfile.toHistogram] using hz₁.trans hz₂.symm
  exact ⟨hbool, hadj, hleft, hright⟩

/-- Active bounded profiles are finite. -/
noncomputable instance fintype (κ : ℕ) :
    Fintype (ActiveBoundedProfile κ) := by
  classical
  unfold ActiveBoundedProfile
  infer_instance

/-- The active subtype has no more profiles than the ambient bounded-profile
type. -/
theorem card_le_boundedProfile_card (κ : ℕ) :
    Fintype.card (ActiveBoundedProfile κ) ≤
      Fintype.card (BoundedProfile κ) :=
  Fintype.card_le_of_injective _
    (toBoundedProfile_injective κ)

/-- Sharp active-profile count: the live bounded-profile space has only three
free coordinates. -/
theorem card_le_pow3 (κ : ℕ) :
    Fintype.card (ActiveBoundedProfile κ) ≤ (κ + 1) ^ 3 := by
  calc
    Fintype.card (ActiveBoundedProfile κ)
        ≤ Fintype.card
            (Fin (κ + 1) × Fin (κ + 1) × Fin (κ + 1)) :=
          Fintype.card_le_of_injective _ (toTuple_injective κ)
    _ = (κ + 1) ^ 3 := by
          simp [Fintype.card_prod, Fintype.card_fin]
          ring

/-- The older four-coordinate bound still follows immediately by forgetting the
active side condition. -/
theorem card_le_pow4 (κ : ℕ) :
    Fintype.card (ActiveBoundedProfile κ) ≤ (κ + 1) ^ 4 :=
  le_trans (card_le_boundedProfile_card κ) (boundedProfile_card_le κ)

end ActiveBoundedProfile

/-- The active profile-count constant. -/
def activeProfileCount (κ : ℕ) : ℕ := (κ + 1) ^ 3

theorem activeProfileCount_le_profileCount (κ : ℕ) :
    activeProfileCount κ ≤ profileCount κ := by
  unfold activeProfileCount profileCount
  calc
    (κ + 1) ^ 3 = (κ + 1) ^ 3 * 1 := by ring
    _ ≤ (κ + 1) ^ 3 * (κ + 1) := by
          exact Nat.mul_le_mul_left _ (by omega)
    _ = (κ + 1) ^ 4 := by ring

theorem activeBoundedProfile_card_le_activeProfileCount (κ : ℕ) :
    Fintype.card (ActiveBoundedProfile κ) ≤ activeProfileCount κ := by
  simpa [activeProfileCount] using ActiveBoundedProfile.card_le_pow3 κ

theorem activeBoundedProfile_card_le_profileCount (κ : ℕ) :
    Fintype.card (ActiveBoundedProfile κ) ≤ profileCount κ :=
  le_trans (activeBoundedProfile_card_le_activeProfileCount κ)
    (activeProfileCount_le_profileCount κ)

/-- Active admissible profiles: the finite subtype matching the live
`ProfileAdmissible k h` and `transitionRight = 0` side conditions. -/
def ActiveAdmissibleProfile (κ : ℕ) : Type :=
  { bp : ActiveBoundedProfile κ // ProfileAdmissible κ bp.toHistogram }

namespace ActiveAdmissibleProfile

def toActiveBoundedProfile {κ : ℕ}
    (bp : ActiveAdmissibleProfile κ) :
    ActiveBoundedProfile κ :=
  bp.val

def toHistogram {κ : ℕ} (bp : ActiveAdmissibleProfile κ) :
    ProfileHistogram :=
  bp.toActiveBoundedProfile.toHistogram

@[simp] theorem toActiveBoundedProfile_toHistogram {κ : ℕ}
    (bp : ActiveAdmissibleProfile κ) :
    bp.toActiveBoundedProfile.toHistogram = bp.toHistogram := rfl

@[simp] theorem toHistogram_transitionRight {κ : ℕ}
    (bp : ActiveAdmissibleProfile κ) :
    bp.toHistogram ConstraintType.transitionRight = 0 :=
  bp.toActiveBoundedProfile.toHistogram_transitionRight

theorem toHistogram_admissible {κ : ℕ}
    (bp : ActiveAdmissibleProfile κ) :
    ProfileAdmissible κ bp.toHistogram :=
  bp.property

def ofHistogram {κ : ℕ} (h : ProfileHistogram)
    (hadm : ProfileAdmissible κ h)
    (htr : h ConstraintType.transitionRight = 0) :
    ActiveAdmissibleProfile κ :=
  ⟨ActiveBoundedProfile.ofAdmissible h hadm htr, by simpa using hadm⟩

@[simp] theorem ofHistogram_toHistogram {κ : ℕ}
    (h : ProfileHistogram)
    (hadm : ProfileAdmissible κ h)
    (htr : h ConstraintType.transitionRight = 0) :
    (ofHistogram h hadm htr).toHistogram = h :=
  rfl

theorem toActiveBoundedProfile_injective (κ : ℕ) :
    Function.Injective
      (fun bp : ActiveAdmissibleProfile κ => bp.toActiveBoundedProfile) := by
  intro bp₁ bp₂ h
  exact Subtype.ext h

noncomputable instance fintype (κ : ℕ) :
    Fintype (ActiveAdmissibleProfile κ) := by
  classical
  unfold ActiveAdmissibleProfile
  infer_instance

theorem card_le_activeBoundedProfile_card (κ : ℕ) :
    Fintype.card (ActiveAdmissibleProfile κ) ≤
      Fintype.card (ActiveBoundedProfile κ) :=
  Fintype.card_le_of_injective _
    (toActiveBoundedProfile_injective κ)

theorem card_le_activeProfileCount (κ : ℕ) :
    Fintype.card (ActiveAdmissibleProfile κ) ≤ activeProfileCount κ :=
  le_trans (card_le_activeBoundedProfile_card κ)
    (activeBoundedProfile_card_le_activeProfileCount κ)

theorem card_le_profileCount (κ : ℕ) :
    Fintype.card (ActiveAdmissibleProfile κ) ≤ profileCount κ :=
  le_trans (card_le_activeProfileCount κ)
    (activeProfileCount_le_profileCount κ)

end ActiveAdmissibleProfile

/-- Finite active-bounded version of the remaining fixed-profile common-span
frontier.  Non-admissible active bounded profiles remain vacuous; this Prop only
asks for the admissible nonzero ones. -/
def CookLevinAllBoundedProfileCommonSpanActiveBoundedProfileCases
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ bp : ActiveBoundedProfile (Nat.log 2 n),
    ProfileAdmissible (Nat.log 2 n) bp.toHistogram →
      bp.toHistogram ≠ zeroProfileHistogram →
        CookLevinAllBoundedProfileCommonSpanAtProfile
          M n hn htb hns bp.toHistogram

/-- Finite active-admissible version of the remaining fixed-profile common-span
frontier.  The only per-profile side condition left here is excluding the zero
histogram, which is handled separately by the zero-profile shift blocker. -/
def CookLevinAllBoundedProfileCommonSpanActiveAdmissibleProfileCases
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) : Prop :=
  ∀ bp : ActiveAdmissibleProfile (Nat.log 2 n),
    bp.toHistogram ≠ zeroProfileHistogram →
      CookLevinAllBoundedProfileCommonSpanAtProfile
        M n hn htb hns bp.toHistogram

theorem cookLevinAllBoundedProfileCommonSpanActiveAdmissibleProfileCases_of_activeBoundedProfileCases
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcases :
      CookLevinAllBoundedProfileCommonSpanActiveBoundedProfileCases
        M n hn htb hns) :
    CookLevinAllBoundedProfileCommonSpanActiveAdmissibleProfileCases
      M n hn htb hns := by
  intro bp hnonzero
  exact hcases bp.toActiveBoundedProfile
    bp.toHistogram_admissible hnonzero

/-- The finite active-admissible frontier proves the all-histogram live-profile
package used by `CommonSpanProfileCaseSplit`. -/
theorem cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_activeAdmissibleProfileCases
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcases :
      CookLevinAllBoundedProfileCommonSpanActiveAdmissibleProfileCases
        M n hn htb hns) :
    CookLevinAllBoundedProfileCommonSpanLiveProfileCases
      M n hn htb hns := by
  intro h hadm htr hnonzero
  let bp : ActiveAdmissibleProfile (Nat.log 2 n) :=
    ActiveAdmissibleProfile.ofHistogram h hadm htr
  simpa [bp] using hcases bp hnonzero

/-- The active-bounded frontier also proves the all-histogram live-profile
package. -/
theorem cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_activeBoundedProfileCases
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hcases :
      CookLevinAllBoundedProfileCommonSpanActiveBoundedProfileCases
        M n hn htb hns) :
    CookLevinAllBoundedProfileCommonSpanLiveProfileCases
      M n hn htb hns :=
  cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_activeAdmissibleProfileCases
    M n hn htb hns
    (cookLevinAllBoundedProfileCommonSpanActiveAdmissibleProfileCases_of_activeBoundedProfileCases
      M n hn htb hns hcases)

/-- Active-admissible fixed-profile cases plus the zero-profile blocker prove
the full all-bounded common-span lemma. -/
theorem cookLevinAllBoundedProfileCommonSpanLemma_of_activeAdmissibleProfileCases
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn htb hns)
    (hcases :
      CookLevinAllBoundedProfileCommonSpanActiveAdmissibleProfileCases
        M n hn htb hns) :
    CookLevinAllBoundedProfileCommonSpanLemma M n hn htb hns :=
  cookLevinAllBoundedProfileCommonSpanLemma_of_liveProfileCases
    M n hn htb hns hn4 hzero
    (cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_activeAdmissibleProfileCases
      M n hn htb hns hcases)

/-- Active-bounded fixed-profile cases plus the zero-profile blocker prove the
full all-bounded common-span lemma. -/
theorem cookLevinAllBoundedProfileCommonSpanLemma_of_activeBoundedProfileCases
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn htb hns)
    (hcases :
      CookLevinAllBoundedProfileCommonSpanActiveBoundedProfileCases
        M n hn htb hns) :
    CookLevinAllBoundedProfileCommonSpanLemma M n hn htb hns :=
  cookLevinAllBoundedProfileCommonSpanLemma_of_activeAdmissibleProfileCases
    M n hn htb hns hn4 hzero
    (cookLevinAllBoundedProfileCommonSpanActiveAdmissibleProfileCases_of_activeBoundedProfileCases
      M n hn htb hns hcases)

/-- The active-admissible frontier also closes the bounded-profile common-span
lemma through the existing all-span bridge. -/
theorem cookLevinBoundedProfileCommonSpanLemma_of_activeAdmissibleProfileCases
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn htb hns)
    (hcases :
      CookLevinAllBoundedProfileCommonSpanActiveAdmissibleProfileCases
        M n hn htb hns) :
    CookLevinBoundedProfileCommonSpanLemma M n hn htb hns :=
  cookLevinBoundedProfileCommonSpanLemma_of_liveProfileCases
    M n hn htb hns hn4 hzero
    (cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_activeAdmissibleProfileCases
      M n hn htb hns hcases)

/-- The active-bounded frontier also closes the bounded-profile common-span
lemma through the existing all-span bridge. -/
theorem cookLevinBoundedProfileCommonSpanLemma_of_activeBoundedProfileCases
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hzero : CookLevinZeroHistogramShiftCommonSpan M n hn htb hns)
    (hcases :
      CookLevinAllBoundedProfileCommonSpanActiveBoundedProfileCases
        M n hn htb hns) :
    CookLevinBoundedProfileCommonSpanLemma M n hn htb hns :=
  cookLevinBoundedProfileCommonSpanLemma_of_activeAdmissibleProfileCases
    M n hn htb hns hn4 hzero
    (cookLevinAllBoundedProfileCommonSpanActiveAdmissibleProfileCases_of_activeBoundedProfileCases
      M n hn htb hns hcases)

/-! ## Axiom audit anchors -/

#print axioms ActiveBoundedProfile.card_le_pow3
#print axioms activeBoundedProfile_card_le_activeProfileCount
#print axioms ActiveAdmissibleProfile.card_le_activeProfileCount
#print axioms cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_activeAdmissibleProfileCases
#print axioms cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_activeBoundedProfileCases
#print axioms cookLevinAllBoundedProfileCommonSpanLemma_of_activeAdmissibleProfileCases
#print axioms cookLevinAllBoundedProfileCommonSpanLemma_of_activeBoundedProfileCases
#print axioms cookLevinBoundedProfileCommonSpanLemma_of_activeAdmissibleProfileCases
#print axioms cookLevinBoundedProfileCommonSpanLemma_of_activeBoundedProfileCases

end PallLean.Paper93.DeepMath.PathB
