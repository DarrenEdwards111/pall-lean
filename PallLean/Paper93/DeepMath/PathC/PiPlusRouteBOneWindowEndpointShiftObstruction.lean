import PallLean.Paper93.DeepMath.PathC.PiPlusRouteBOneWindowEndpointActiveProgress

/-!
# Endpoint same-profile one-window shift obstruction

The endpoint-augmented family was useful for discharging the derivative field of
`CookLevinOneWindowPerTypeSpanningActiveData`, but its same-profile active
shift/`mlProj` closure is still too strong.  This file lifts the existing
booleanity-mass-one obstruction from the `log₂ n` API to the new one-window
`log₂ n + 1` API.

Conclusion: the final nonzero active side cannot be closed by endpoint-augmented
same-profile closure.  It needs the charged/target-profile machinery (or a
strictly different row family), not this false field.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open PallLean.Paper93.DeepMath.PathB
open PaperFaithfulSeparation
open TuringMachine
open SymmetricPowerBound
open WithinProfileBound

attribute [local instance] Classical.dec

/-- The booleanity-mass-one histogram. -/
def booleanityMassOneHistogram : ProfileHistogram :=
  fun τ => if τ = ConstraintType.booleanity then 1 else 0

@[simp] theorem booleanityMassOneHistogram_booleanity :
    booleanityMassOneHistogram ConstraintType.booleanity = 1 := by
  simp [booleanityMassOneHistogram]

@[simp] theorem booleanityMassOneHistogram_of_ne_booleanity
    {τ : ConstraintType} (hτ : τ ≠ ConstraintType.booleanity) :
    booleanityMassOneHistogram τ = 0 := by
  simp [booleanityMassOneHistogram, hτ]

@[simp] theorem booleanityMassOneHistogram_transitionRight :
    booleanityMassOneHistogram ConstraintType.transitionRight = 0 := by
  simp [booleanityMassOneHistogram]

@[simp] theorem profileMass_booleanityMassOneHistogram :
    profileMass booleanityMassOneHistogram = 1 := by
  unfold profileMass booleanityMassOneHistogram
  decide

/-- Booleanity-mass-one is admissible at every positive profile radius. -/
theorem booleanityMassOneHistogram_admissible {κ : ℕ} (hκ : 1 ≤ κ) :
    ProfileAdmissible κ booleanityMassOneHistogram := by
  simpa [ProfileAdmissible, profileMass_booleanityMassOneHistogram] using hκ

/-- The old-radius bounded profile used by the checked endpoint obstruction. -/
def booleanityMassOneBoundedProfileLog
    (n : ℕ) (hn4 : n ≥ 4) : BoundedProfile (Nat.log 2 n) :=
  ⟨booleanityMassOneHistogram, by
    intro τ
    by_cases hτ : τ = ConstraintType.booleanity
    · subst τ
      have hlog : 1 ≤ Nat.log 2 n :=
        Nat.le_log_of_pow_le (by norm_num : 1 < 2) (by omega : 2 ^ 1 ≤ n)
      simpa using hlog
    · simp [booleanityMassOneHistogram, hτ]⟩

/-- The one-window active admissible profile at booleanity mass one. -/
def booleanityMassOneActiveAdmissibleProfileOneWindow
    (n : ℕ) (_hn4 : n ≥ 4) :
    ActiveAdmissibleProfile (Nat.log 2 n + 1) :=
  ActiveAdmissibleProfile.ofHistogram booleanityMassOneHistogram
    (booleanityMassOneHistogram_admissible (by omega))
    booleanityMassOneHistogram_transitionRight

@[simp] theorem booleanityMassOneActiveAdmissibleProfileOneWindow_hist
    (n : ℕ) (hn4 : n ≥ 4) :
    (booleanityMassOneActiveAdmissibleProfileOneWindow n hn4).toHistogram =
      booleanityMassOneHistogram := by
  simp [booleanityMassOneActiveAdmissibleProfileOneWindow]

/-- One-window same-profile closure at booleanity mass one would imply the old
same-profile closure already known to be false. -/
theorem old_endpointShiftClosure_of_oneWindow_booleanityMassOne
    (n : ℕ) (hn4 : n ≥ 4)
    (hnew : PerTypeShiftMlprojClosureAtOneWindowBoundedProfile
      (endpointAugmentedConcreteW n hn4)
      (booleanityMassOneActiveAdmissibleProfileOneWindow n hn4).toActiveBoundedProfile.toBoundedProfile) :
    PerTypeShiftMlprojClosureAtBoundedProfile
      (endpointAugmentedConcreteW n hn4)
      (booleanityMassOneBoundedProfileLog n hn4) := by
  intro S hSlen shift hshift g hg
  have hSlen' : S.length ≤ Nat.log 2 n + 1 := by omega
  have hnewmem := hnew S hSlen' shift hshift g ?_
  · simpa [booleanityMassOneBoundedProfileLog,
      booleanityMassOneActiveAdmissibleProfileOneWindow,
      ActiveAdmissibleProfile.toActiveBoundedProfile,
      ActiveBoundedProfile.toBoundedProfile,
      BoundedProfile.toHistogram] using hnewmem
  · simpa [booleanityMassOneBoundedProfileLog,
      booleanityMassOneActiveAdmissibleProfileOneWindow,
      ActiveAdmissibleProfile.toActiveBoundedProfile,
      ActiveBoundedProfile.toBoundedProfile,
      BoundedProfile.toHistogram] using hg

/-- Endpoint-augmented one-window active same-profile shift closure is false. -/
theorem not_EndpointAugmentedOneWindowActiveShiftMlprojClosure
    (n : ℕ) (hn4 : n ≥ 4) :
    ¬ EndpointAugmentedOneWindowActiveShiftMlprojClosure n hn4 := by
  intro hShift
  let bp1 := booleanityMassOneActiveAdmissibleProfileOneWindow n hn4
  have hne : bp1.toHistogram ≠ zeroProfileHistogram := by
    intro h
    have hb := congrFun h ConstraintType.booleanity
    simp [bp1, booleanityMassOneActiveAdmissibleProfileOneWindow,
      zeroProfileHistogram] at hb
  have hnew := hShift bp1 hne
  have hold := old_endpointShiftClosure_of_oneWindow_booleanityMassOne
    n hn4 hnew
  exact not_endpointAugmentedConcreteW_shiftMlprojClosureAt_booleanity_mass_one
    n hn4 (booleanityMassOneBoundedProfileLog n hn4)
    (by
      change booleanityMassOneHistogram ConstraintType.booleanity = 1
      simp)
    (by
      intro τ hτ
      change booleanityMassOneHistogram τ = 0
      simp [booleanityMassOneHistogram, hτ])
    hold

/-- Consequently, the endpoint-augmented active-data package cannot be closed
via its advertised same-profile shift/`mlProj` field. -/
theorem not_endpointAugmented_activeData_via_sameProfileShift
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4) :
    ¬ ∃ _ : EndpointAugmentedOneWindowActiveShiftMlprojClosure n hn4,
      CookLevinOneWindowPerTypeSpanningActiveData M n hn htb hns
        (endpointAugmentedConcreteW n hn4) := by
  intro h
  rcases h with ⟨hShift, _hdata⟩
  exact not_EndpointAugmentedOneWindowActiveShiftMlprojClosure n hn4 hShift

/-! ## Axiom audit anchors -/

#print axioms booleanityMassOneHistogram_admissible
#print axioms old_endpointShiftClosure_of_oneWindow_booleanityMassOne
#print axioms not_EndpointAugmentedOneWindowActiveShiftMlprojClosure
#print axioms not_endpointAugmented_activeData_via_sameProfileShift

end PallLean.Paper93.DeepMath.PathC
