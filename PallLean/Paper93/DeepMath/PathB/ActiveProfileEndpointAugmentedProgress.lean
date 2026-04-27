import PallLean.Paper93.DeepMath.PathB.ActiveProfileBlockerConcreteProgress
import PallLean.Paper93.DeepMath.PathB.AugmentedConcreteWI5

/-!
# Active-profile endpoint-augmented retargeting

The canonical unaugmented `concreteW` route to active-profile blockers is
formally blocked by canonical H4.  This file exposes the replacement shape
without pretending the remaining estimates are solved:

* use endpoint-augmented `concreteW`, whose H4 is checked;
* only ask for row embeddings at active live profiles, not a global
  same-profile I5 package that would include the zero-profile obstruction;
* bound the active profile subspace directly by an explicit finite/profile
  budget, or by the older dimension-`≤ 3` template estimate when available;
* optionally recover active same-profile row embeddings from a charged I5
  package plus a self-targeting charge proof for the active profile.
-/

namespace PallLean.Paper93.DeepMath.PathB

open MvPolynomial
open PaperFaithfulSeparation
open SymmetricPowerBound
open SPDP MultilinearSPDP
open TuringMachine (DTM)
open WithinProfileBound
open PallLean.Paper93
open PallLean.Paper93.Closure
open PallLean.Paper93.Spanning
open PallLean.Paper93.Wiring (concreteW)
open scoped BigOperators

attribute [local instance] Classical.dec

/-- The nonzero active support condition left after the dormant
`transitionRight` and zero-profile cases have been split away. -/
def ActiveProfileSupport (h : ProfileHistogram) : Prop :=
  0 < h ConstraintType.booleanity ∨
    0 < h ConstraintType.adjacency ∨
      0 < h ConstraintType.transitionLeft

/-- Canonical-row H3 embeds into the endpoint-augmented H3 target.  This is
the exact positive membership result available for the fixed
`endpointAugmentedConcreteW` family: arbitrary direct branch rows still need
alignment with the fixed canonical row, as witnessed by
`booleanity_directBranchFactor_not_mem_endpointAugmentedConcreteW_of_ne_endpoints`. -/
theorem CookLevinFactorMemPerType_endpointAugmentedConcreteW_of_concreteWCanonical
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hFactor :
      CookLevinFactorMemPerType M n hn htb hns
        (concreteWCanonical n hn4)) :
    CookLevinFactorMemPerType M n hn htb hns
      (endpointAugmentedConcreteW n hn4) := by
  intro i
  unfold endpointAugmentedConcreteW
  exact Submodule.mem_sup_left (hFactor i)

/-- One bounded-profile slice of the per-type row-embedding bundle.

This is the active-profile replacement for demanding a full global
`CookLevinPerTypeSpanning` package.  It is intentionally profile-local, so
callers do not have to prove the zero-profile same-profile closure that is
known to be the wrong target for Route B. -/
def CookLevinPerTypeSpanningAtBoundedProfile
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (bp : BoundedProfile (Nat.log 2 n)) : Prop :=
  ∀ (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ) (_hshift : shift.vars ⊆ S.toFinset)
    (g : MvPolynomial (Fin n) ℚ)
    (_hg : g ∈ boundedProfileClassifiedSet
              (fun i => (cookLevinFactorList M n hn htb hns).get i)
              (cookLevinConstraintType M n hn htb hns)
              S bp.toHistogram),
    mlProj (shift * g) ∈ cookLevinProfileSubspace bp W

/-- The full per-type spanning package specializes to any bounded-profile
slice. -/
theorem cookLevinPerTypeSpanningAtBoundedProfile_of_perTypeSpanning
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (bp : BoundedProfile (Nat.log 2 n))
    (hSpan : CookLevinPerTypeSpanning M n hn htb hns W) :
    CookLevinPerTypeSpanningAtBoundedProfile M n hn htb hns W bp :=
  fun S hSlen shift hshift g hg =>
    hSpan bp S hSlen shift hshift g hg

/-- A profile-local row embedding gives the post-span containment at that
profile. -/
theorem cookLevinProfileSubspace_contains_postSpan_at_bp_of_perTypeSpanningAtBoundedProfile
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (bp : BoundedProfile (Nat.log 2 n))
    (hSpanAt :
      CookLevinPerTypeSpanningAtBoundedProfile M n hn htb hns W bp) :
    cookLevinPostSpanAt M n hn htb hns bp.toHistogram
      ≤ cookLevinProfileSubspace bp W := by
  classical
  refine Submodule.span_le.mpr ?_
  intro q hq
  simp only [Set.mem_iUnion, Set.mem_image] at hq
  obtain ⟨S, hSlen, shift, hshiftvars, g, hg, rfl⟩ := hq
  exact hSpanAt S hSlen shift hshiftvars g hg

/-- Profile-local shift/mlProj closure, only at one bounded profile. -/
def PerTypeShiftMlprojClosureAtBoundedProfile {n : ℕ}
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (bp : BoundedProfile (Nat.log 2 n)) : Prop :=
  ∀ (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ) (_hshift : shift.vars ⊆ S.toFinset)
    (g : MvPolynomial (Fin n) ℚ)
    (_hg_prod :
      ∃ (L : ℕ) (factors : Fin L → MvPolynomial (Fin n) ℚ)
        (constraintType : Fin L → ConstraintType)
        (d : Fin L → List (Fin n)),
        (∀ i, ∀ v ∈ d i, v ∈ S) ∧
        (∀ i, iterDerivList (d i) (factors i) ∈ W (constraintType i)) ∧
        g = Finset.univ.prod (fun i => iterDerivList (d i) (factors i)) ∧
        derivCountProfile constraintType d = bp.toHistogram ∧
        ∑ i : Fin L, (d i).length ≤ S.length),
    mlProj (shift * g) ∈ cookLevinProfileSubspace bp W

/-- The global same-profile closure specializes to the profile-local closure. -/
theorem perTypeShiftMlprojClosureAtBoundedProfile_of_global {n : ℕ}
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (bp : BoundedProfile (Nat.log 2 n))
    (hShiftMlproj : PerTypeShiftMlprojClosure (n := n) W) :
    PerTypeShiftMlprojClosureAtBoundedProfile W bp :=
  fun S hSlen shift hshift g hg =>
    hShiftMlproj bp S hSlen shift hshift g hg

/-- A charged I5 package gives the profile-local same-profile closure when the
chosen charge relation can target the same active profile for the shift. -/
def ProfileChargeSelfAtBoundedProfile {n : ℕ}
    (charge : ProfileCharge n) (bp : BoundedProfile (Nat.log 2 n)) : Prop :=
  ∀ (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ) (_hshift : shift.vars ⊆ S.toFinset),
    charge bp S shift bp

/-- Charged profile-local closure collapses to the uncharged profile-local
surface when the charge self-targets this active profile. -/
theorem perTypeShiftMlprojClosureAtBoundedProfile_of_charged_self {n : ℕ}
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (charge : ProfileCharge n)
    (bp : BoundedProfile (Nat.log 2 n))
    (hCharged : PerTypeShiftMlprojClosureCharged (n := n) charge W)
    (hSelf : ProfileChargeSelfAtBoundedProfile charge bp) :
    PerTypeShiftMlprojClosureAtBoundedProfile W bp := by
  intro S hSlen shift hshift g hg
  exact hCharged bp bp S hSlen shift hshift g hg
    (hSelf S hSlen shift hshift)

/-- Discharge a bounded-profile row-embedding slice from H3, endpoint H4, and
profile-local shift/mlProj closure. -/
theorem cookLevinPerTypeSpanningAtBoundedProfile_discharged
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (bp : BoundedProfile (Nat.log 2 n))
    (hFactor : CookLevinFactorMemPerType M n hn htb hns W)
    (hClosure : DerivClosurePerType (n := n) W)
    (hShiftMlprojAt : PerTypeShiftMlprojClosureAtBoundedProfile W bp) :
    CookLevinPerTypeSpanningAtBoundedProfile M n hn htb hns W bp := by
  classical
  intro S hSlen shift hshiftvars g hg
  obtain ⟨d, hd_elts, hg_prod, hprof, hsum⟩ := hg
  have hEachMem :
      ∀ i : Fin (cookLevinFactorList M n hn htb hns).length,
        iterDerivList (d i)
            ((fun j => (cookLevinFactorList M n hn htb hns).get j) i)
          ∈ W (cookLevinConstraintType M n hn htb hns i) := by
    intro i
    have hdi_le : (d i).length ≤ Nat.log 2 n := by
      have : (d i).length ≤ S.length := by
        refine le_trans ?_ hsum
        refine Finset.single_le_sum (f := fun j => (d j).length) ?_
          (Finset.mem_univ i)
        intro j _
        exact Nat.zero_le _
      exact le_trans this hSlen
    exact iterDerivList_factor_mem_W
      M n hn htb hns W hFactor hClosure i
      (cookLevinConstraintType M n hn htb hns i) rfl (d i) hdi_le
  exact hShiftMlprojAt S hSlen shift hshiftvars g
    ⟨(cookLevinFactorList M n hn htb hns).length,
     (fun j => (cookLevinFactorList M n hn htb hns).get j),
     cookLevinConstraintType M n hn htb hns, d,
     hd_elts, hEachMem, hg_prod, hprof, hsum⟩

/-- Endpoint-augmented profile subspace budget for active profiles.  This is
the faithful replacement for the blocked canonical-H4 route: the active
post-span must factor through an endpoint-augmented low-dimensional profile
space whose finrank is already within the paper's per-profile budget. -/
def EndpointAugmentedActiveProfileSubspaceBudget
    (n : ℕ) (hn4 : n ≥ 4) : Prop :=
  ∀ (h : ProfileHistogram)
    (hadm : ProfileAdmissible (Nat.log 2 n) h),
    ActiveProfileSupport h →
      Module.Finite ℚ
          ↥(cookLevinProfileSubspace
              (admissibleToBounded hadm)
              (endpointAugmentedConcreteW n hn4)) ∧
        Module.finrank ℚ
            ↥(cookLevinProfileSubspace
                (admissibleToBounded hadm)
                (endpointAugmentedConcreteW n hn4))
          ≤ withinProfileBound (Nat.log 2 n)

/-- The older `dim W_τ ≤ 3` template estimate is one way to satisfy the
explicit endpoint-augmented active-profile budget.  It is exposed separately
because endpoint augmentation may instead require a sharper profile-specific
compression proof. -/
theorem endpointAugmentedActiveProfileSubspaceBudget_of_dim_le_three
    (n : ℕ) (hn4 : n ≥ 4)
    (hW_fin :
      ∀ τ, Module.Finite ℚ ↥(endpointAugmentedConcreteW n hn4 τ))
    (hW_dim :
      ∀ τ, Module.finrank ℚ ↥(endpointAugmentedConcreteW n hn4 τ) ≤ 3) :
    EndpointAugmentedActiveProfileSubspaceBudget n hn4 := by
  intro h hadm _hactive
  constructor
  · exact cookLevinProfileSubspace_finite
      (admissibleToBounded hadm)
      (endpointAugmentedConcreteW n hn4) hW_fin
  · exact le_trans
      (cookLevinProfileSubspace_finrank_le
        (admissibleToBounded hadm)
        (endpointAugmentedConcreteW n hn4) hW_fin hW_dim)
      (profileTemplateBound_le_withinProfileBound
        (Nat.log 2 n) h hadm)

/-- A profile-local endpoint-augmented row embedding plus the explicit
active-profile budget closes the fixed common-span target. -/
theorem cookLevinAllBoundedProfileCommonSpanAtProfile_of_endpointAugmented_spanningAtProfile
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (h : ProfileHistogram)
    (hadm : ProfileAdmissible (Nat.log 2 n) h)
    (hactive : ActiveProfileSupport h)
    (hBudget : EndpointAugmentedActiveProfileSubspaceBudget n hn4)
    (hSpanAt :
      CookLevinPerTypeSpanningAtBoundedProfile M n hn htb hns
        (endpointAugmentedConcreteW n hn4)
        (admissibleToBounded hadm)) :
    CookLevinAllBoundedProfileCommonSpanAtProfile M n hn htb hns h := by
  classical
  rcases hBudget h hadm hactive with ⟨hProfileFinite, hProfileBound⟩
  let bp : BoundedProfile (Nat.log 2 n) := admissibleToBounded hadm
  have hPost :
      cookLevinPostSpanAt M n hn htb hns bp.toHistogram
        ≤ cookLevinProfileSubspace bp (endpointAugmentedConcreteW n hn4) :=
    cookLevinProfileSubspace_contains_postSpan_at_bp_of_perTypeSpanningAtBoundedProfile
      M n hn htb hns (endpointAugmentedConcreteW n hn4) bp hSpanAt
  letI : Module.Finite ℚ
      ↥(cookLevinProfileSubspace bp (endpointAugmentedConcreteW n hn4)) := by
    simpa [bp] using hProfileFinite
  have hmono :
      Module.finrank ℚ ↥(cookLevinPostSpanAt M n hn htb hns bp.toHistogram)
        ≤ Module.finrank ℚ
            ↥(cookLevinProfileSubspace bp (endpointAugmentedConcreteW n hn4)) :=
    Submodule.finrank_mono hPost
  have hdim_post :
      Module.finrank ℚ ↥(cookLevinPostSpanAt M n hn htb hns bp.toHistogram)
        ≤ withinProfileBound (Nat.log 2 n) := by
    exact le_trans hmono (by simpa [bp] using hProfileBound)
  have hdim_all :
      Module.finrank ℚ
          ↥(allBoundedProfilePostSpan
            (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn htb hns).get i)
            (cookLevinConstraintType M n hn htb hns)
            h)
        ≤ withinProfileBound (Nat.log 2 n) := by
    simpa [bp] using hdim_post
  exact
    cookLevinAllBoundedProfileCommonSpanAtProfile_of_allBoundedProfilePostSpan_finrank
      M n hn htb hns h hdim_all

/-- Endpoint-augmented active-profile closure frontier at one profile.

H4 is not a field: it is supplied by the checked theorem
`endpointAugmentedConcreteW_derivClosurePerType`.  The remaining profile-local
content is factor membership into the augmented type spaces and active-only
same-profile shift/mlProj closure. -/
def EndpointAugmentedActiveProfileClosureAtProfile
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4) (bp : BoundedProfile (Nat.log 2 n)) : Prop :=
  CookLevinFactorMemPerType M n hn htb hns
      (endpointAugmentedConcreteW n hn4) ∧
    PerTypeShiftMlprojClosureAtBoundedProfile
      (endpointAugmentedConcreteW n hn4) bp

/-- The one-profile endpoint-augmented closure frontier produces the
one-profile row-embedding slice. -/
theorem cookLevinPerTypeSpanningAtBoundedProfile_endpointAugmented_of_closureAtProfile
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4) (bp : BoundedProfile (Nat.log 2 n))
    (hFrontier :
      EndpointAugmentedActiveProfileClosureAtProfile
        M n hn htb hns hn4 bp) :
    CookLevinPerTypeSpanningAtBoundedProfile M n hn htb hns
      (endpointAugmentedConcreteW n hn4) bp := by
  exact
    cookLevinPerTypeSpanningAtBoundedProfile_discharged
      M n hn htb hns (endpointAugmentedConcreteW n hn4) bp
      hFrontier.1
      (endpointAugmentedConcreteW_derivClosurePerType n hn4)
      hFrontier.2

/-- Charged endpoint-augmented closure frontier at one active profile.

The `ProfileChargeSelfAtBoundedProfile` field is deliberately explicit:
charged Route B only feeds the existing same-profile active common-span target
when the chosen charge can self-target this active profile. -/
def EndpointAugmentedActiveProfileChargedClosureAtProfile
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (charge : ProfileCharge n)
    (hn4 : n ≥ 4) (bp : BoundedProfile (Nat.log 2 n)) : Prop :=
  CookLevinFactorMemPerType M n hn htb hns
      (endpointAugmentedConcreteW n hn4) ∧
    PerTypeProductGrouping (n := n) (endpointAugmentedConcreteW n hn4) ∧
    PerTypeChargedShiftClosure (n := n) charge
      (endpointAugmentedConcreteW n hn4) ∧
    PerTypeMlprojClosure (n := n) (endpointAugmentedConcreteW n hn4) ∧
    ProfileChargeSelfAtBoundedProfile charge bp

/-- Charged endpoint-augmented closure gives the one-profile row-embedding
slice when the charge self-targets the active profile. -/
theorem cookLevinPerTypeSpanningAtBoundedProfile_endpointAugmented_of_chargedClosureAtProfile
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (charge : ProfileCharge n)
    (hn4 : n ≥ 4) (bp : BoundedProfile (Nat.log 2 n))
    (hFrontier :
      EndpointAugmentedActiveProfileChargedClosureAtProfile
        M n hn htb hns charge hn4 bp) :
    CookLevinPerTypeSpanningAtBoundedProfile M n hn htb hns
      (endpointAugmentedConcreteW n hn4) bp := by
  rcases hFrontier with ⟨hFactor, hI1, hI2c, hI3, hSelf⟩
  have hCharged :
      PerTypeShiftMlprojClosureCharged (n := n) charge
        (endpointAugmentedConcreteW n hn4) :=
    perTypeShiftMlprojClosure_charged_discharged
      (n := n) charge (endpointAugmentedConcreteW n hn4)
      hI1 hI2c hI3
  exact
    cookLevinPerTypeSpanningAtBoundedProfile_discharged
      M n hn htb hns (endpointAugmentedConcreteW n hn4) bp
      hFactor
      (endpointAugmentedConcreteW_derivClosurePerType n hn4)
      (perTypeShiftMlprojClosureAtBoundedProfile_of_charged_self
        (endpointAugmentedConcreteW n hn4) charge bp hCharged hSelf)

/-- All active profiles can be closed by endpoint-augmented one-profile
frontiers plus the active profile budget. -/
def EndpointAugmentedActiveProfileFrontier
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4) : Prop :=
  EndpointAugmentedActiveProfileSubspaceBudget n hn4 ∧
    ∀ (h : ProfileHistogram)
      (hadm : ProfileAdmissible (Nat.log 2 n) h),
      h ConstraintType.transitionRight = 0 →
        h ≠ zeroProfileHistogram →
          ActiveProfileSupport h →
            EndpointAugmentedActiveProfileClosureAtProfile
              M n hn htb hns hn4 (admissibleToBounded hadm)

/-- Charged variant of the endpoint-augmented active frontier. -/
def EndpointAugmentedActiveProfileChargedFrontier
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (charge : ProfileCharge n)
    (hn4 : n ≥ 4) : Prop :=
  EndpointAugmentedActiveProfileSubspaceBudget n hn4 ∧
    ∀ (h : ProfileHistogram)
      (hadm : ProfileAdmissible (Nat.log 2 n) h),
      h ConstraintType.transitionRight = 0 →
        h ≠ zeroProfileHistogram →
          ActiveProfileSupport h →
            EndpointAugmentedActiveProfileChargedClosureAtProfile
              M n hn htb hns charge hn4 (admissibleToBounded hadm)

/-- Endpoint-augmented active frontiers feed the existing active blocker
interface. -/
theorem cookLevinActiveProfileTypeCaseBlockers_of_endpointAugmentedActiveProfileFrontier
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hFrontier :
      EndpointAugmentedActiveProfileFrontier M n hn htb hns hn4) :
    CookLevinActiveProfileTypeCaseBlockers M n hn htb hns := by
  rcases hFrontier with ⟨hBudget, hProfile⟩
  refine ⟨?_, ?_, ?_⟩
  · intro h hadm htr hne hpos
    exact
      cookLevinAllBoundedProfileCommonSpanAtProfile_of_endpointAugmented_spanningAtProfile
        M n hn htb hns hn4 h hadm (Or.inl hpos) hBudget
        (cookLevinPerTypeSpanningAtBoundedProfile_endpointAugmented_of_closureAtProfile
          M n hn htb hns hn4 (admissibleToBounded hadm)
          (hProfile h hadm htr hne (Or.inl hpos)))
  · intro h hadm htr hne hpos
    exact
      cookLevinAllBoundedProfileCommonSpanAtProfile_of_endpointAugmented_spanningAtProfile
        M n hn htb hns hn4 h hadm (Or.inr (Or.inl hpos)) hBudget
        (cookLevinPerTypeSpanningAtBoundedProfile_endpointAugmented_of_closureAtProfile
          M n hn htb hns hn4 (admissibleToBounded hadm)
          (hProfile h hadm htr hne (Or.inr (Or.inl hpos))))
  · intro h hadm htr hne hpos
    exact
      cookLevinAllBoundedProfileCommonSpanAtProfile_of_endpointAugmented_spanningAtProfile
        M n hn htb hns hn4 h hadm (Or.inr (Or.inr hpos)) hBudget
        (cookLevinPerTypeSpanningAtBoundedProfile_endpointAugmented_of_closureAtProfile
          M n hn htb hns hn4 (admissibleToBounded hadm)
          (hProfile h hadm htr hne (Or.inr (Or.inr hpos))))

/-- Charged endpoint-augmented active frontiers feed the existing active
blocker interface once self-targeting is proved profile-by-profile. -/
theorem cookLevinActiveProfileTypeCaseBlockers_of_endpointAugmentedActiveProfileChargedFrontier
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (charge : ProfileCharge n)
    (hn4 : n ≥ 4)
    (hFrontier :
      EndpointAugmentedActiveProfileChargedFrontier
        M n hn htb hns charge hn4) :
    CookLevinActiveProfileTypeCaseBlockers M n hn htb hns := by
  rcases hFrontier with ⟨hBudget, hProfile⟩
  refine ⟨?_, ?_, ?_⟩
  · intro h hadm htr hne hpos
    exact
      cookLevinAllBoundedProfileCommonSpanAtProfile_of_endpointAugmented_spanningAtProfile
        M n hn htb hns hn4 h hadm (Or.inl hpos) hBudget
        (cookLevinPerTypeSpanningAtBoundedProfile_endpointAugmented_of_chargedClosureAtProfile
          M n hn htb hns charge hn4 (admissibleToBounded hadm)
          (hProfile h hadm htr hne (Or.inl hpos)))
  · intro h hadm htr hne hpos
    exact
      cookLevinAllBoundedProfileCommonSpanAtProfile_of_endpointAugmented_spanningAtProfile
        M n hn htb hns hn4 h hadm (Or.inr (Or.inl hpos)) hBudget
        (cookLevinPerTypeSpanningAtBoundedProfile_endpointAugmented_of_chargedClosureAtProfile
          M n hn htb hns charge hn4 (admissibleToBounded hadm)
          (hProfile h hadm htr hne (Or.inr (Or.inl hpos))))
  · intro h hadm htr hne hpos
    exact
      cookLevinAllBoundedProfileCommonSpanAtProfile_of_endpointAugmented_spanningAtProfile
        M n hn htb hns hn4 h hadm (Or.inr (Or.inr hpos)) hBudget
        (cookLevinPerTypeSpanningAtBoundedProfile_endpointAugmented_of_chargedClosureAtProfile
          M n hn htb hns charge hn4 (admissibleToBounded hadm)
          (hProfile h hadm htr hne (Or.inr (Or.inr hpos))))

/-- The endpoint-augmented active frontier also closes the named all-live
profile package. -/
theorem cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_endpointAugmentedActiveProfileFrontier
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hFrontier :
      EndpointAugmentedActiveProfileFrontier M n hn htb hns hn4) :
    CookLevinAllBoundedProfileCommonSpanLiveProfileCases M n hn htb hns :=
  cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_activeTypeCaseBlockers
    M n hn htb hns
    (cookLevinActiveProfileTypeCaseBlockers_of_endpointAugmentedActiveProfileFrontier
      M n hn htb hns hn4 hFrontier)

/-- Charged endpoint-augmented active frontier version of the all-live package. -/
theorem cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_endpointAugmentedActiveProfileChargedFrontier
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (charge : ProfileCharge n)
    (hn4 : n ≥ 4)
    (hFrontier :
      EndpointAugmentedActiveProfileChargedFrontier
        M n hn htb hns charge hn4) :
    CookLevinAllBoundedProfileCommonSpanLiveProfileCases M n hn htb hns :=
  cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_activeTypeCaseBlockers
    M n hn htb hns
    (cookLevinActiveProfileTypeCaseBlockers_of_endpointAugmentedActiveProfileChargedFrontier
      M n hn htb hns charge hn4 hFrontier)

/-! ## Axiom audit anchors -/

#print axioms CookLevinFactorMemPerType_endpointAugmentedConcreteW_of_concreteWCanonical
#print axioms cookLevinPerTypeSpanningAtBoundedProfile_of_perTypeSpanning
#print axioms cookLevinProfileSubspace_contains_postSpan_at_bp_of_perTypeSpanningAtBoundedProfile
#print axioms perTypeShiftMlprojClosureAtBoundedProfile_of_global
#print axioms perTypeShiftMlprojClosureAtBoundedProfile_of_charged_self
#print axioms cookLevinPerTypeSpanningAtBoundedProfile_discharged
#print axioms endpointAugmentedActiveProfileSubspaceBudget_of_dim_le_three
#print axioms cookLevinAllBoundedProfileCommonSpanAtProfile_of_endpointAugmented_spanningAtProfile
#print axioms cookLevinPerTypeSpanningAtBoundedProfile_endpointAugmented_of_closureAtProfile
#print axioms cookLevinPerTypeSpanningAtBoundedProfile_endpointAugmented_of_chargedClosureAtProfile
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_endpointAugmentedActiveProfileFrontier
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_endpointAugmentedActiveProfileChargedFrontier
#print axioms cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_endpointAugmentedActiveProfileFrontier
#print axioms cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_endpointAugmentedActiveProfileChargedFrontier

end PallLean.Paper93.DeepMath.PathB
