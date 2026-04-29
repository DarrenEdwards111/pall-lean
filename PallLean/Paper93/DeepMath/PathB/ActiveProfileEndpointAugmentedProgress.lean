import PallLean.Paper93.DeepMath.PathB.ActiveProfileBlockerConcreteProgress
import PallLean.Paper93.DeepMath.PathB.AugmentedConcreteWI5
import PallLean.Paper93.CompiledCoefficientBasis
import PallLean.Paper93.Canonical.ProfileSubspaceStructure

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
open PallLean.Paper93.Bridge
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

/-- H3 for the fixed canonical concreteW row embeds into the endpoint-augmented
H3 target. -/
theorem CookLevinFactorMemPerType_endpointAugmentedConcreteW_of_concreteW
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hFactor :
      CookLevinFactorMemPerType M n hn htb hns
        (fun τ => concreteW n hn4 (Fin.castLEEmb hn4) τ)) :
    CookLevinFactorMemPerType M n hn htb hns
      (endpointAugmentedConcreteW n hn4) :=
  CookLevinFactorMemPerType_endpointAugmentedConcreteW_of_concreteWCanonical
    M n hn htb hns hn4
    (by simpa [concreteWCanonical] using hFactor)

/-- Canonical fixed-row factor shapes discharge endpoint-augmented H3. -/
theorem CookLevinFactorMemPerType_endpointAugmentedConcreteW_of_canonicalShapeWitnesses
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hShape :
      CookLevinCanonicalConcreteWShapeWitnesses M n hn htb hns hn4) :
    CookLevinFactorMemPerType M n hn htb hns
      (endpointAugmentedConcreteW n hn4) :=
  CookLevinFactorMemPerType_endpointAugmentedConcreteW_of_concreteW
    M n hn htb hns hn4
    (CookLevinFactorMemPerType_concreteW_of_canonicalShapeWitnesses
      M n hn htb hns hn4 hShape)

/-- Direct branch shapes discharge endpoint-augmented H3 once the exact
canonical-row transport has been supplied. -/
theorem CookLevinFactorMemPerType_endpointAugmentedConcreteW_of_directBranchShapes_transport
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hShape : CookLevinDirectBranchShapeWitnesses M n hn htb hns hn4)
    (hTransport :
      CookLevinConcreteWCanonicalRowTransport M n hn htb hns hn4) :
    CookLevinFactorMemPerType M n hn htb hns
      (endpointAugmentedConcreteW n hn4) :=
  CookLevinFactorMemPerType_endpointAugmentedConcreteW_of_concreteW
    M n hn htb hns hn4
    (CookLevinFactorMemPerType_concreteW_of_directBranchShapes_transport
      M n hn htb hns hn4 hShape hTransport)

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

/-- Charged profile-local row embedding with an explicit target profile.

This is the target-profile replacement for
`CookLevinPerTypeSpanningAtBoundedProfile`: the derivative product has source
profile `bpSrc`, while `shift` is allowed to move it to `bpTgt` through the
chosen charge relation. -/
def CookLevinPerTypeChargedSpanningAtBoundedProfileTarget
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (charge : ProfileCharge n)
    (bpSrc bpTgt : BoundedProfile (Nat.log 2 n)) : Prop :=
  ∀ (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
    (shift : MvPolynomial (Fin n) ℚ) (_hshift : shift.vars ⊆ S.toFinset)
    (g : MvPolynomial (Fin n) ℚ)
    (_hg : g ∈ boundedProfileClassifiedSet
              (fun i => (cookLevinFactorList M n hn htb hns).get i)
              (cookLevinConstraintType M n hn htb hns)
              S bpSrc.toHistogram),
    charge bpSrc S shift bpTgt →
      mlProj (shift * g) ∈ cookLevinProfileSubspace bpTgt W

/-- H3, H4, and charged I5 discharge the explicit-target charged
profile-local row embedding. -/
theorem cookLevinPerTypeChargedSpanningAtBoundedProfileTarget_discharged
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (charge : ProfileCharge n)
    (bpSrc bpTgt : BoundedProfile (Nat.log 2 n))
    (hFactor : CookLevinFactorMemPerType M n hn htb hns W)
    (hClosure : DerivClosurePerType (n := n) W)
    (hCharged : PerTypeShiftMlprojClosureCharged (n := n) charge W) :
    CookLevinPerTypeChargedSpanningAtBoundedProfileTarget
      M n hn htb hns W charge bpSrc bpTgt := by
  classical
  intro S hSlen shift hshiftvars g hg hcharge
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
  exact hCharged bpSrc bpTgt S hSlen shift hshiftvars g
    ⟨(cookLevinFactorList M n hn htb hns).length,
     (fun j => (cookLevinFactorList M n hn htb hns).get j),
     cookLevinConstraintType M n hn htb hns, d,
     hd_elts, hEachMem, hg_prod, hprof, hsum⟩ hcharge

/-- If every generator shift in the source profile is charged to the same
target profile, the ordinary Cook-Levin post-span at the source profile lands
in the target profile subspace.  This carries `bpTgt` explicitly and does not
require `bpTgt = bpSrc`. -/
theorem cookLevinPostSpanAt_le_chargedTarget_of_chargedSpanningAtBoundedProfileTarget
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (charge : ProfileCharge n)
    (bpSrc bpTgt : BoundedProfile (Nat.log 2 n))
    (hSpanAt :
      CookLevinPerTypeChargedSpanningAtBoundedProfileTarget
        M n hn htb hns W charge bpSrc bpTgt)
    (hCharge :
      ∀ (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
        (shift : MvPolynomial (Fin n) ℚ)
        (_hshift : shift.vars ⊆ S.toFinset)
        (g : MvPolynomial (Fin n) ℚ)
        (_hg : g ∈ boundedProfileClassifiedSet
              (fun i => (cookLevinFactorList M n hn htb hns).get i)
              (cookLevinConstraintType M n hn htb hns)
              S bpSrc.toHistogram),
          charge bpSrc S shift bpTgt) :
    cookLevinPostSpanAt M n hn htb hns bpSrc.toHistogram
      ≤ cookLevinProfileSubspace bpTgt W := by
  classical
  refine Submodule.span_le.mpr ?_
  intro q hq
  simp only [Set.mem_iUnion, Set.mem_image] at hq
  obtain ⟨S, hSlen, shift, hshiftvars, g, hg, rfl⟩ := hq
  exact hSpanAt S hSlen shift hshiftvars g hg
    (hCharge S hSlen shift hshiftvars g hg)

/-- Charged/restricted Cook-Levin post-span from a source bounded profile to a
target bounded profile.

Unlike `cookLevinPostSpanAt`, this does not range over all shifts.  It keeps
only the generators whose shift is accepted by the chosen profile charge. -/
noncomputable def cookLevinChargedPostSpanAtTarget
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (charge : ProfileCharge n)
    (bpSrc bpTgt : BoundedProfile (Nat.log 2 n)) :
    Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
  Submodule.span ℚ
    { p | ∃ (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
        (shift : MvPolynomial (Fin n) ℚ)
        (_hshift : shift.vars ⊆ S.toFinset)
        (g : MvPolynomial (Fin n) ℚ)
        (_hg : g ∈ boundedProfileClassifiedSet
              (fun i => (cookLevinFactorList M n hn htb hns).get i)
              (cookLevinConstraintType M n hn htb hns)
              S bpSrc.toHistogram),
        charge bpSrc S shift bpTgt ∧ p = mlProj (shift * g) }

/-- Generator-level form of the charged target-profile cover obligation.

It exposes exactly what is needed to upgrade the unrestricted Cook-Levin
post-span into the charged/restricted target span: every source generator must
carry the selected charge to one admissible active target profile. -/
def CookLevinEndpointChargedTargetGeneratorCoverAt
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (charge : ProfileCharge n)
    (h : ProfileHistogram)
    (hadm : ProfileAdmissible (Nat.log 2 n) h) : Prop :=
  ∃ bpTgt : BoundedProfile (Nat.log 2 n),
    ProfileAdmissible (Nat.log 2 n) bpTgt.toHistogram ∧
      bpTgt.toHistogram ConstraintType.transitionRight = 0 ∧
      ActiveProfileSupport bpTgt.toHistogram ∧
      ∀ (S : List (Fin n)) (_hSlen : S.length ≤ Nat.log 2 n)
        (shift : MvPolynomial (Fin n) ℚ)
        (_hshift : shift.vars ⊆ S.toFinset)
        (g : MvPolynomial (Fin n) ℚ),
        g ∈ boundedProfileClassifiedSet
            (fun i => (cookLevinFactorList M n hn htb hns).get i)
            (cookLevinConstraintType M n hn htb hns)
            S h →
          charge (admissibleToBounded hadm) S shift bpTgt

/-- A target-profile charged spanning slice contains the corresponding
charged/restricted post-span. -/
theorem cookLevinChargedPostSpanAtTarget_le_profileSubspace_of_chargedSpanningAtBoundedProfileTarget
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (charge : ProfileCharge n)
    (bpSrc bpTgt : BoundedProfile (Nat.log 2 n))
    (hSpanAt :
      CookLevinPerTypeChargedSpanningAtBoundedProfileTarget
        M n hn htb hns W charge bpSrc bpTgt) :
    cookLevinChargedPostSpanAtTarget M n hn htb hns charge bpSrc bpTgt
      ≤ cookLevinProfileSubspace bpTgt W := by
  classical
  refine Submodule.span_le.mpr ?_
  intro p hp
  rcases hp with ⟨S, hSlen, shift, hshiftvars, g, hg, hcharge, rfl⟩
  exact hSpanAt S hSlen shift hshiftvars g hg hcharge

/-- H3, H4, and charged I5 contain the charged/restricted post-span in the
target profile subspace. -/
theorem cookLevinChargedPostSpanAtTarget_le_profileSubspace_discharged
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (charge : ProfileCharge n)
    (bpSrc bpTgt : BoundedProfile (Nat.log 2 n))
    (hFactor : CookLevinFactorMemPerType M n hn htb hns W)
    (hClosure : DerivClosurePerType (n := n) W)
    (hCharged : PerTypeShiftMlprojClosureCharged (n := n) charge W) :
    cookLevinChargedPostSpanAtTarget M n hn htb hns charge bpSrc bpTgt
      ≤ cookLevinProfileSubspace bpTgt W :=
  cookLevinChargedPostSpanAtTarget_le_profileSubspace_of_chargedSpanningAtBoundedProfileTarget
    M n hn htb hns W charge bpSrc bpTgt
    (cookLevinPerTypeChargedSpanningAtBoundedProfileTarget_discharged
      M n hn htb hns W charge bpSrc bpTgt hFactor hClosure hCharged)

/-- A source active profile is covered by charged target profiles when its full
post-span is contained in the charged/restricted span for one admissible target
profile.  This is the replacement for same-profile self-targeting: the target
profile may differ from the source profile. -/
def CookLevinEndpointChargedTargetProfileCoverAt
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (charge : ProfileCharge n)
    (h : ProfileHistogram)
    (hadm : ProfileAdmissible (Nat.log 2 n) h) : Prop :=
  ∃ bpTgt : BoundedProfile (Nat.log 2 n),
    ProfileAdmissible (Nat.log 2 n) bpTgt.toHistogram ∧
      bpTgt.toHistogram ConstraintType.transitionRight = 0 ∧
      ActiveProfileSupport bpTgt.toHistogram ∧
      cookLevinPostSpanAt M n hn htb hns h ≤
        cookLevinChargedPostSpanAtTarget M n hn htb hns charge
          (admissibleToBounded hadm) bpTgt

/-- The generator-level charged target condition implies the profile-level
charged target cover. -/
theorem CookLevinEndpointChargedTargetProfileCoverAt_of_generatorCover
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (charge : ProfileCharge n)
    (h : ProfileHistogram)
    (hadm : ProfileAdmissible (Nat.log 2 n) h)
    (hgen :
      CookLevinEndpointChargedTargetGeneratorCoverAt
        M n hn htb hns charge h hadm) :
    CookLevinEndpointChargedTargetProfileCoverAt
      M n hn htb hns charge h hadm := by
  classical
  rcases hgen with ⟨bpTgt, hadmTgt, htrTgt, hactiveTgt, hcharge⟩
  refine ⟨bpTgt, hadmTgt, htrTgt, hactiveTgt, ?_⟩
  refine Submodule.span_le.mpr ?_
  intro p hp
  simp only [Set.mem_iUnion, Set.mem_image] at hp
  rcases hp with ⟨S, hSlen, shift, hshiftvars, g, hg, rfl⟩
  exact Submodule.subset_span
    ⟨S, hSlen, shift, hshiftvars, g, hg,
      hcharge S hSlen shift hshiftvars g hg, rfl⟩

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
    h ConstraintType.transitionRight = 0 →
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
  intro h hadm _htr _hactive
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

/-- Existing compiled-coefficient interface spaces satisfy the active-profile
symmetric-power budget side: once rows factor through these spaces, the
standard `dim W_τ ≤ 3` estimate gives the paper's per-profile bound. -/
theorem compiledCoefficientBasis_activeProfileSubspaceBudget
    {n : ℕ} (B : BlockPartition n) (ℓ : ℕ)
    (h : ProfileHistogram)
    (hadm : ProfileAdmissible (Nat.log 2 n) h)
    (_hactive : ActiveProfileSupport h) :
    Module.Finite ℚ
        ↥(cookLevinProfileSubspace
            (admissibleToBounded hadm)
            (fun τ => interfaceSpace_compiledBasis B (Nat.log 2 n) ℓ τ)) ∧
      Module.finrank ℚ
          ↥(cookLevinProfileSubspace
              (admissibleToBounded hadm)
              (fun τ => interfaceSpace_compiledBasis B (Nat.log 2 n) ℓ τ))
        ≤ withinProfileBound (Nat.log 2 n) := by
  constructor
  · exact cookLevinProfileSubspace_finite
      (admissibleToBounded hadm)
      (fun τ => interfaceSpace_compiledBasis B (Nat.log 2 n) ℓ τ)
      (fun τ => interfaceSpace_compiledBasis_finite B (Nat.log 2 n) ℓ τ)
  · exact le_trans
      (cookLevinProfileSubspace_finrank_le
        (admissibleToBounded hadm)
        (fun τ => interfaceSpace_compiledBasis B (Nat.log 2 n) ℓ τ)
        (fun τ => interfaceSpace_compiledBasis_finite B (Nat.log 2 n) ℓ τ)
        (fun τ =>
          interfaceSpace_compiledBasis_finrank_le_three
            B (Nat.log 2 n) ℓ τ))
      (profileTemplateBound_le_withinProfileBound
        (Nat.log 2 n) h hadm)

/-- Positive active-type membership after replacing the zero compiled-basis
placeholder: every non-dormant local type contains the constant normal form. -/
theorem one_mem_interfaceSpace_compiledBasis_activeType
    {n : ℕ} (B : BlockPartition n) (κ ℓ : ℕ) (τ : ConstraintType)
    (hτ : τ ≠ ConstraintType.transitionRight) :
    (1 : MvPolynomial (Fin n) ℚ) ∈ interfaceSpace_compiledBasis B κ ℓ τ :=
  one_mem_interfaceSpace_compiledBasis_of_not_transitionRight B κ ℓ τ hτ

/-- The booleanity compiled chart contains the basic singleton row and the
canonical Cook-Levin booleanity factor. -/
theorem compiledBasis_booleanity_basicRows_mem
    {n : ℕ} (B : BlockPartition n) (κ ℓ : ℕ) :
    canonicalLocalX ∈
        interfaceSpace_compiledBasis B κ ℓ ConstraintType.booleanity ∧
      canonicalLocalBoolFactor ∈
        interfaceSpace_compiledBasis B κ ℓ ConstraintType.booleanity :=
  ⟨canonicalLocalX_mem_interfaceSpace_compiledBasis_booleanity B κ ℓ,
    canonicalLocalBoolFactor_mem_interfaceSpace_compiledBasis_booleanity B κ ℓ⟩

/-- The adjacency compiled chart contains the two canonical endpoint singleton
rows used by the interface-anonymous normal form. -/
theorem compiledBasis_adjacency_basicRows_mem
    {n : ℕ} (B : BlockPartition n) (κ ℓ : ℕ) :
    canonicalLocalX ∈
        interfaceSpace_compiledBasis B κ ℓ ConstraintType.adjacency ∧
      canonicalLocalX1 ∈
        interfaceSpace_compiledBasis B κ ℓ ConstraintType.adjacency :=
  ⟨canonicalLocalX_mem_interfaceSpace_compiledBasis_adjacency B κ ℓ,
    canonicalLocalX1_mem_interfaceSpace_compiledBasis_adjacency B κ ℓ⟩

/-- The transition-left compiled chart contains its canonical singleton row. -/
theorem compiledBasis_transitionLeft_basicRow_mem
    {n : ℕ} (B : BlockPartition n) (κ ℓ : ℕ) :
    canonicalLocalX ∈
      interfaceSpace_compiledBasis B κ ℓ ConstraintType.transitionLeft :=
  canonicalLocalX_mem_interfaceSpace_compiledBasis_transitionLeft B κ ℓ

/-- Corrected interface-anonymous normal-form/profile-span gate.

This is the active/profile target that avoids the obstructed same-profile
endpoint closure: it asks directly that the Cook-Levin post-span at `h` lies in
the profile subspace generated by the compiled-basis local normal-form
alphabet.  The existing `dim W_τ ≤ 3` compiled-basis bound then closes the
common-span profile. -/
theorem cookLevinAllBoundedProfileCommonSpanAtProfile_of_interfaceAnonymousProfileSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B : BlockPartition n) (ℓ : ℕ)
    (h : ProfileHistogram)
    (hadm : ProfileAdmissible (Nat.log 2 n) h)
    (hactive : ActiveProfileSupport h)
    (hProfileSpan :
      cookLevinPostSpanAt M n hn htb hns h ≤
        cookLevinProfileSubspace (admissibleToBounded hadm)
          (fun τ =>
            interfaceSpace_compiledBasis B (Nat.log 2 n) ℓ τ)) :
    CookLevinAllBoundedProfileCommonSpanAtProfile M n hn htb hns h := by
  classical
  rcases compiledCoefficientBasis_activeProfileSubspaceBudget
      B ℓ h hadm hactive with
    ⟨hProfileFinite, hProfileBound⟩
  letI : Module.Finite ℚ
      ↥(cookLevinProfileSubspace (admissibleToBounded hadm)
        (fun τ => interfaceSpace_compiledBasis B (Nat.log 2 n) ℓ τ)) :=
    hProfileFinite
  have hmono :
      Module.finrank ℚ ↥(cookLevinPostSpanAt M n hn htb hns h)
        ≤ Module.finrank ℚ
            ↥(cookLevinProfileSubspace (admissibleToBounded hadm)
              (fun τ =>
                interfaceSpace_compiledBasis B (Nat.log 2 n) ℓ τ)) :=
    Submodule.finrank_mono hProfileSpan
  have hdim_all :
      Module.finrank ℚ
          ↥(allBoundedProfilePostSpan
            (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn htb hns).get i)
            (cookLevinConstraintType M n hn htb hns)
            h)
        ≤ withinProfileBound (Nat.log 2 n) := by
    change
      Module.finrank ℚ ↥(cookLevinPostSpanAt M n hn htb hns h)
        ≤ withinProfileBound (Nat.log 2 n)
    exact le_trans hmono hProfileBound
  exact
    cookLevinAllBoundedProfileCommonSpanAtProfile_of_allBoundedProfilePostSpan_finrank
      M n hn htb hns h hdim_all

/-- Direct interface-anonymous active profile span containments are enough for
the active type-case blockers.  This is the blocker-level retarget that avoids
the endpoint same-profile closure field entirely: each active case only has to
place the Cook-Levin post-span inside the compiled-basis profile subspace. -/
theorem cookLevinActiveProfileTypeCaseBlockers_of_interfaceAnonymous_activeProfileSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B : BlockPartition n) (ℓ : ℕ)
    (hProfileSpan :
      ∀ (h : ProfileHistogram)
        (hadm : ProfileAdmissible (Nat.log 2 n) h),
          h ConstraintType.transitionRight = 0 →
            ActiveProfileSupport h →
              cookLevinPostSpanAt M n hn htb hns h ≤
                cookLevinProfileSubspace (admissibleToBounded hadm)
                  (fun τ =>
                    interfaceSpace_compiledBasis B (Nat.log 2 n) ℓ τ)) :
    CookLevinActiveProfileTypeCaseBlockers M n hn htb hns := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro h hadm htr _hne hpos
    exact
      cookLevinAllBoundedProfileCommonSpanAtProfile_of_interfaceAnonymousProfileSpan
        M n hn htb hns B ℓ h hadm (Or.inl hpos)
        (hProfileSpan h hadm htr (Or.inl hpos))
  · intro h hadm htr _hne hpos
    exact
      cookLevinAllBoundedProfileCommonSpanAtProfile_of_interfaceAnonymousProfileSpan
        M n hn htb hns B ℓ h hadm (Or.inr (Or.inl hpos))
        (hProfileSpan h hadm htr (Or.inr (Or.inl hpos)))
  · intro h hadm htr _hne hpos
    exact
      cookLevinAllBoundedProfileCommonSpanAtProfile_of_interfaceAnonymousProfileSpan
        M n hn htb hns B ℓ h hadm (Or.inr (Or.inr hpos))
        (hProfileSpan h hadm htr (Or.inr (Or.inr hpos)))

/-! ## Endpoint active-profile budget -/

/-- Variable-dimension version of the generic profile-subspace finrank bound.

The existing `profileSubspace_finrank_bound` specializes this to the paper
`≤ 3` case.  The endpoint-augmented live slice has type dimensions
`4, 4, 3` instead, so we keep the exact multichoose product and discharge the
active arithmetic separately. -/
theorem profileSubspace_finrank_bound_by_finrank
    {N : ℕ} {Iface : Type*} [Fintype Iface] [DecidableEq Iface]
    (h : Iface → ℕ)
    (W : Iface → Submodule ℚ (MvPolynomial (Fin N) ℚ))
    (hW_fin : ∀ σ, Module.Finite ℚ ↥(W σ)) :
    Module.finrank ℚ (profileSubspace h W) ≤
      ∏ σ : Iface, Nat.multichoose
        (Module.finrank ℚ ↥(W σ)) (h σ) := by
  classical
  set d : Iface → ℕ := fun σ => Module.finrank ℚ ↥(W σ) with hd_def
  let b : ∀ σ, Module.Basis (Fin (d σ)) ℚ ↥(W σ) :=
    fun σ => Module.finBasis ℚ ↥(W σ)
  have hsub :
      profileSubspace h W ≤
        Submodule.span ℚ
          (Set.range (profileSymProd W b : ProfileIndex h d → _)) :=
    profileSubspace_le_profileSymProd_span W b
  haveI hfin_big : Module.Finite ℚ
      ↥(Submodule.span ℚ
        (Set.range (profileSymProd W b : ProfileIndex h d → _))) := by
    apply Module.Finite.span_of_finite
    exact Set.finite_range _
  have hmono :
      Module.finrank ℚ (profileSubspace h W) ≤
        Module.finrank ℚ
          (Submodule.span ℚ
            (Set.range (profileSymProd W b : ProfileIndex h d → _))) :=
    Submodule.finrank_mono hsub
  have hcard :
      Module.finrank ℚ
          (Submodule.span ℚ
            (Set.range (profileSymProd W b : ProfileIndex h d → _))) ≤
        Fintype.card (ProfileIndex h d) :=
    by
      let G : Finset (MvPolynomial (Fin N) ℚ) :=
        (Finset.univ : Finset (ProfileIndex h d)).image
          (profileSymProd W b)
      have hrange :
          Set.range (profileSymProd W b : ProfileIndex h d →
              MvPolynomial (Fin N) ℚ) =
            (↑G : Set (MvPolynomial (Fin N) ℚ)) := by
        ext q
        constructor
        · intro hq
          rcases hq with ⟨idx, rfl⟩
          exact Finset.mem_image.mpr ⟨idx, Finset.mem_univ idx, rfl⟩
        · intro hq
          rcases Finset.mem_image.mp hq with ⟨idx, _hidx, hqeq⟩
          exact ⟨idx, hqeq⟩
      have hspan :
          Module.finrank ℚ
              ↥(Submodule.span ℚ
                (Set.range (profileSymProd W b : ProfileIndex h d →
                  MvPolynomial (Fin N) ℚ))) ≤ G.card := by
        rw [hrange]
        exact finrank_span_finset_le_card G
      have hGcard : G.card ≤ Fintype.card (ProfileIndex h d) := by
        calc
          G.card
              ≤ (Finset.univ : Finset (ProfileIndex h d)).card := by
                exact Finset.card_image_le
          _ = Fintype.card (ProfileIndex h d) := Finset.card_univ
      exact hspan.trans hGcard
  have hcard_eq :
      Fintype.card (ProfileIndex h d) =
        ∏ σ : Iface, Nat.multichoose (d σ) (h σ) :=
    profileIndex_card h d
  calc
    Module.finrank ℚ (profileSubspace h W)
        ≤ Module.finrank ℚ
            (Submodule.span ℚ
              (Set.range (profileSymProd W b : ProfileIndex h d → _))) := hmono
    _ ≤ Fintype.card (ProfileIndex h d) := hcard
    _ = ∏ σ : Iface, Nat.multichoose (d σ) (h σ) := hcard_eq
    _ = ∏ σ : Iface,
          Nat.multichoose (Module.finrank ℚ ↥(W σ)) (h σ) := by
            simp [d]

theorem cookLevinProfileSubspace_finrank_le_by_finrank
    {n : ℕ}
    (bp : BoundedProfile (Nat.log 2 n))
    (W : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ))
    (hW_fin : ∀ τ, Module.Finite ℚ ↥(W τ)) :
    Module.finrank ℚ (cookLevinProfileSubspace bp W) ≤
      ∏ τ : ConstraintType, Nat.multichoose
        (Module.finrank ℚ ↥(W τ)) (bp.toHistogram τ) := by
  unfold cookLevinProfileSubspace
  exact profileSubspace_finrank_bound_by_finrank
    bp.toHistogram W hW_fin

private theorem finrank_span_singleton_le_one
    {n : ℕ} (p : MvPolynomial (Fin n) ℚ) :
    Module.finrank ℚ
      ↥(Submodule.span ℚ ({p} : Set (MvPolynomial (Fin n) ℚ))) ≤ 1 := by
  calc
    Module.finrank ℚ
        ↥(Submodule.span ℚ ({p} : Set (MvPolynomial (Fin n) ℚ)))
        ≤ ({p} : Finset (MvPolynomial (Fin n) ℚ)).card := by
          simpa using
            finrank_span_le_card (R := ℚ)
              (s := ({p} : Set (MvPolynomial (Fin n) ℚ)))
    _ = 1 := by simp

private theorem finrank_sup_le_add
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (U W : Submodule ℚ V)
    [Module.Finite ℚ ↥U] [Module.Finite ℚ ↥W] :
    Module.finrank ℚ ↥(U ⊔ W) ≤
      Module.finrank ℚ ↥U + Module.finrank ℚ ↥W := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq U W
  omega

private theorem concreteWCanonical_booleanity_le_endpoint_sqSpan
    (n : ℕ) (hn4 : n ≥ 4) :
    concreteWCanonical n hn4 ConstraintType.booleanity ≤
      concreteWEndpointSpan n hn4 ⊔
        Submodule.span ℚ
          ({(MvPolynomial.X (concreteWEndpoint0 n hn4) :
              MvPolynomial (Fin n) ℚ) ^ 2} :
            Set (MvPolynomial (Fin n) ℚ)) := by
  classical
  intro p hp
  unfold concreteWCanonical concreteW at hp
  unfold ambientPerTypeSpace at hp
  rw [Submodule.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  unfold perTypeInterfaceSpace at hq
  refine Submodule.span_induction
    (p := fun q _ =>
      MvPolynomial.rename
          ((Fin.castLEEmb hn4 : Fin 4 ↪ Fin n).toFun) q ∈
        concreteWEndpointSpan n hn4 ⊔
          Submodule.span ℚ
            ({(MvPolynomial.X (concreteWEndpoint0 n hn4) :
                MvPolynomial (Fin n) ℚ) ^ 2} :
              Set (MvPolynomial (Fin n) ℚ)))
    ?_ ?_ ?_ ?_ hq
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · have hone :
          (1 : MvPolynomial (Fin n) ℚ) ∈
            concreteWEndpointSpan n hn4 := by
          unfold concreteWEndpointSpan
          exact Submodule.subset_span (by simp)
      simpa using Submodule.mem_sup_left hone
    · have hx :
          (MvPolynomial.X (concreteWEndpoint0 n hn4) :
            MvPolynomial (Fin n) ℚ) ∈
            concreteWEndpointSpan n hn4 := by
          unfold concreteWEndpointSpan
          exact Submodule.subset_span (by simp [concreteWEndpoint0])
      simpa [concreteWEndpoint0] using Submodule.mem_sup_left hx
    · have hx2 :
          ((MvPolynomial.X (concreteWEndpoint0 n hn4) :
            MvPolynomial (Fin n) ℚ) ^ 2) ∈
            Submodule.span ℚ
              ({(MvPolynomial.X (concreteWEndpoint0 n hn4) :
                  MvPolynomial (Fin n) ℚ) ^ 2} :
                Set (MvPolynomial (Fin n) ℚ)) := by
          exact Submodule.subset_span (by simp)
      simpa [concreteWEndpoint0] using Submodule.mem_sup_right hx2
  · simp
  · intro p q _ _ hp hq
    simpa [map_add] using Submodule.add_mem _ hp hq
  · intro a p _ hp
    simpa using Submodule.smul_mem _ a hp

private theorem concreteWCanonical_adjacency_le_endpoint_prodSpan
    (n : ℕ) (hn4 : n ≥ 4) :
    concreteWCanonical n hn4 ConstraintType.adjacency ≤
      concreteWEndpointSpan n hn4 ⊔
        Submodule.span ℚ
          ({(MvPolynomial.X (concreteWEndpoint0 n hn4) *
              MvPolynomial.X (concreteWEndpoint1 n hn4) :
              MvPolynomial (Fin n) ℚ)} :
            Set (MvPolynomial (Fin n) ℚ)) := by
  classical
  intro p hp
  unfold concreteWCanonical concreteW at hp
  unfold ambientPerTypeSpace at hp
  rw [Submodule.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  unfold perTypeInterfaceSpace at hq
  refine Submodule.span_induction
    (p := fun q _ =>
      MvPolynomial.rename
          ((Fin.castLEEmb hn4 : Fin 4 ↪ Fin n).toFun) q ∈
        concreteWEndpointSpan n hn4 ⊔
          Submodule.span ℚ
            ({(MvPolynomial.X (concreteWEndpoint0 n hn4) *
                MvPolynomial.X (concreteWEndpoint1 n hn4) :
                MvPolynomial (Fin n) ℚ)} :
              Set (MvPolynomial (Fin n) ℚ)))
    ?_ ?_ ?_ ?_ hq
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · have hone :
          (1 : MvPolynomial (Fin n) ℚ) ∈
            concreteWEndpointSpan n hn4 := by
          unfold concreteWEndpointSpan
          exact Submodule.subset_span (by simp)
      simpa using Submodule.mem_sup_left hone
    · have hprod :
          (MvPolynomial.X (concreteWEndpoint0 n hn4) *
            MvPolynomial.X (concreteWEndpoint1 n hn4) :
              MvPolynomial (Fin n) ℚ) ∈
            Submodule.span ℚ
              ({(MvPolynomial.X (concreteWEndpoint0 n hn4) *
                  MvPolynomial.X (concreteWEndpoint1 n hn4) :
                  MvPolynomial (Fin n) ℚ)} :
                Set (MvPolynomial (Fin n) ℚ)) := by
          exact Submodule.subset_span (by simp)
      simpa [concreteWEndpoint0, concreteWEndpoint1] using
        Submodule.mem_sup_right hprod
  · simp
  · intro p q _ _ hp hq
    simpa [map_add] using Submodule.add_mem _ hp hq
  · intro a p _ hp
    simpa using Submodule.smul_mem _ a hp

private theorem concreteWCanonical_transitionLeft_le_endpointSpan
    (n : ℕ) (hn4 : n ≥ 4) :
    concreteWCanonical n hn4 ConstraintType.transitionLeft ≤
      concreteWEndpointSpan n hn4 := by
  classical
  intro p hp
  unfold concreteWCanonical concreteW at hp
  unfold ambientPerTypeSpace at hp
  rw [Submodule.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  unfold perTypeInterfaceSpace at hq
  refine Submodule.span_induction
    (p := fun q _ =>
      MvPolynomial.rename
          ((Fin.castLEEmb hn4 : Fin 4 ↪ Fin n).toFun) q ∈
        concreteWEndpointSpan n hn4)
    ?_ ?_ ?_ ?_ hq
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · unfold concreteWEndpointSpan
      exact Submodule.subset_span (by simp)
    · have hx :
          (MvPolynomial.X (concreteWEndpoint0 n hn4) :
            MvPolynomial (Fin n) ℚ) ∈
            concreteWEndpointSpan n hn4 := by
          unfold concreteWEndpointSpan
          exact Submodule.subset_span (by simp [concreteWEndpoint0])
      simpa [concreteWEndpoint0] using hx
  · simp
  · intro p q _ _ hp hq
    simpa [map_add] using Submodule.add_mem _ hp hq
  · intro a p _ hp
    simpa using Submodule.smul_mem _ a hp

private theorem concreteWCanonical_transitionRight_le_endpointSpan
    (n : ℕ) (hn4 : n ≥ 4) :
    concreteWCanonical n hn4 ConstraintType.transitionRight ≤
      concreteWEndpointSpan n hn4 := by
  intro p hp
  have hpbot :
      p ∈ (⊥ : Submodule ℚ (MvPolynomial (Fin n) ℚ)) := by
    simpa [concreteWCanonical, concreteW, ambientPerTypeSpace,
      perTypeInterfaceSpace] using hp
  have hpzero : p = 0 := by simpa using hpbot
  rw [hpzero]
  exact Submodule.zero_mem _

/-- Effective endpoint dimensions on the active/profile slice.  The dormant
right coordinate still has an endpoint span, but live profiles have right
mass zero, so it contributes a symmetric power of degree zero. -/
def endpointAugmentedActiveProfileDim : ConstraintType → ℕ
  | .booleanity => 4
  | .adjacency => 4
  | .transitionLeft => 3
  | .transitionRight => 3

theorem endpointAugmentedConcreteW_finrank_le_activeProfileDim
    (n : ℕ) (hn4 : n ≥ 4) (τ : ConstraintType) :
    Module.finrank ℚ ↥(endpointAugmentedConcreteW n hn4 τ) ≤
      endpointAugmentedActiveProfileDim τ := by
  classical
  cases τ with
  | booleanity =>
      let sqSpan : Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
        Submodule.span ℚ
          ({(MvPolynomial.X (concreteWEndpoint0 n hn4) :
              MvPolynomial (Fin n) ℚ) ^ 2} :
            Set (MvPolynomial (Fin n) ℚ))
      haveI hEndpointFinite :
          Module.Finite ℚ ↥(concreteWEndpointSpan n hn4) :=
        concreteWEndpointSpan_finite n hn4
      haveI hSqFinite : Module.Finite ℚ ↥sqSpan := by
        unfold sqSpan
        exact Module.Finite.span_of_finite ℚ (Set.finite_singleton _)
      haveI hTargetFinite :
          Module.Finite ℚ ↥(concreteWEndpointSpan n hn4 ⊔ sqSpan) :=
        Submodule.finite_sup _ _
      have hle :
          endpointAugmentedConcreteW n hn4 ConstraintType.booleanity ≤
            concreteWEndpointSpan n hn4 ⊔ sqSpan := by
        intro p hp
        rw [endpointAugmentedConcreteW, Submodule.mem_sup] at hp
        obtain ⟨pc, hpc, pe, hpe, hp_eq⟩ := hp
        rw [← hp_eq]
        exact Submodule.add_mem _
          (by
            simpa [sqSpan] using
              concreteWCanonical_booleanity_le_endpoint_sqSpan n hn4 hpc)
          (Submodule.mem_sup_left hpe)
      have htarget :
          Module.finrank ℚ ↥(concreteWEndpointSpan n hn4 ⊔ sqSpan) ≤ 4 := by
        have hend := concreteWEndpointSpan_finrank_le_three n hn4
        have hsq :
            Module.finrank ℚ ↥sqSpan ≤ 1 := by
          unfold sqSpan
          exact finrank_span_singleton_le_one _
        have hsup := finrank_sup_le_add (concreteWEndpointSpan n hn4) sqSpan
        omega
      exact le_trans (Submodule.finrank_mono hle)
        (by simpa [endpointAugmentedActiveProfileDim] using htarget)
  | adjacency =>
      let prodSpan : Submodule ℚ (MvPolynomial (Fin n) ℚ) :=
        Submodule.span ℚ
          ({(MvPolynomial.X (concreteWEndpoint0 n hn4) *
              MvPolynomial.X (concreteWEndpoint1 n hn4) :
              MvPolynomial (Fin n) ℚ)} :
            Set (MvPolynomial (Fin n) ℚ))
      haveI hEndpointFinite :
          Module.Finite ℚ ↥(concreteWEndpointSpan n hn4) :=
        concreteWEndpointSpan_finite n hn4
      haveI hProdFinite : Module.Finite ℚ ↥prodSpan := by
        unfold prodSpan
        exact Module.Finite.span_of_finite ℚ (Set.finite_singleton _)
      haveI hTargetFinite :
          Module.Finite ℚ ↥(concreteWEndpointSpan n hn4 ⊔ prodSpan) :=
        Submodule.finite_sup _ _
      have hle :
          endpointAugmentedConcreteW n hn4 ConstraintType.adjacency ≤
            concreteWEndpointSpan n hn4 ⊔ prodSpan := by
        intro p hp
        rw [endpointAugmentedConcreteW, Submodule.mem_sup] at hp
        obtain ⟨pc, hpc, pe, hpe, hp_eq⟩ := hp
        rw [← hp_eq]
        exact Submodule.add_mem _
          (by
            simpa [prodSpan] using
              concreteWCanonical_adjacency_le_endpoint_prodSpan n hn4 hpc)
          (Submodule.mem_sup_left hpe)
      have htarget :
          Module.finrank ℚ ↥(concreteWEndpointSpan n hn4 ⊔ prodSpan) ≤ 4 := by
        have hend := concreteWEndpointSpan_finrank_le_three n hn4
        have hprod :
            Module.finrank ℚ ↥prodSpan ≤ 1 := by
          unfold prodSpan
          exact finrank_span_singleton_le_one _
        have hsup := finrank_sup_le_add (concreteWEndpointSpan n hn4) prodSpan
        omega
      exact le_trans (Submodule.finrank_mono hle)
        (by simpa [endpointAugmentedActiveProfileDim] using htarget)
  | transitionLeft =>
      haveI hEndpointFinite :
          Module.Finite ℚ ↥(concreteWEndpointSpan n hn4) :=
        concreteWEndpointSpan_finite n hn4
      have hle :
          endpointAugmentedConcreteW n hn4 ConstraintType.transitionLeft ≤
            concreteWEndpointSpan n hn4 := by
        intro p hp
        rw [endpointAugmentedConcreteW, Submodule.mem_sup] at hp
        obtain ⟨pc, hpc, pe, hpe, hp_eq⟩ := hp
        rw [← hp_eq]
        exact Submodule.add_mem _
          (concreteWCanonical_transitionLeft_le_endpointSpan n hn4 hpc)
          hpe
      exact le_trans (Submodule.finrank_mono hle)
        (by
          simpa [endpointAugmentedActiveProfileDim] using
            concreteWEndpointSpan_finrank_le_three n hn4)
  | transitionRight =>
      haveI hEndpointFinite :
          Module.Finite ℚ ↥(concreteWEndpointSpan n hn4) :=
        concreteWEndpointSpan_finite n hn4
      have hle :
          endpointAugmentedConcreteW n hn4 ConstraintType.transitionRight ≤
            concreteWEndpointSpan n hn4 := by
        intro p hp
        rw [endpointAugmentedConcreteW, Submodule.mem_sup] at hp
        obtain ⟨pc, hpc, pe, hpe, hp_eq⟩ := hp
        rw [← hp_eq]
        exact Submodule.add_mem _
          (concreteWCanonical_transitionRight_le_endpointSpan n hn4 hpc)
          hpe
      exact le_trans (Submodule.finrank_mono hle)
        (by
          simpa [endpointAugmentedActiveProfileDim] using
            concreteWEndpointSpan_finrank_le_three n hn4)

private theorem multichoose_mono_left (a b k : ℕ) (hab : a ≤ b) :
    Nat.multichoose a k ≤ Nat.multichoose b k := by
  by_cases hk : k = 0
  · subst k
    simp [Nat.multichoose_zero_right]
  · rw [Nat.multichoose_eq a k, Nat.multichoose_eq b k]
    exact Nat.choose_le_choose k (by omega)

private theorem multichoose_four_le_pow_three (k : ℕ) :
    Nat.multichoose 4 k ≤ (k + 1) ^ 3 := by
  calc
    Nat.multichoose 4 k = Nat.choose (4 + k - 1) k :=
      Nat.multichoose_eq 4 k
    _ = Nat.choose (k + 3) 3 := by
      have hsum : 4 + k - 1 = k + 3 := by omega
      rw [hsum]
      rw [← Nat.choose_symm (by omega : k ≤ k + 3)]
      congr 1
      omega
    _ ≤ (k + 1) ^ 3 := dim_sym_le k 3

private theorem multichoose_three_le_pow_two (k : ℕ) :
    Nat.multichoose 3 k ≤ (k + 1) ^ 2 := by
  calc
    Nat.multichoose 3 k = Nat.choose (3 + k - 1) k :=
      Nat.multichoose_eq 3 k
    _ = Nat.choose (k + 2) 2 := by
      have hsum : 3 + k - 1 = k + 2 := by omega
      rw [hsum]
      rw [← Nat.choose_symm (by omega : k ≤ k + 2)]
      congr 1
      omega
    _ ≤ (k + 1) ^ 2 := dim_sym_le k 2

private theorem endpointAugmentedActiveProfile_multichoose_le_withinProfileBound
    (κ : ℕ) (h : ProfileHistogram)
    (hadm : ProfileAdmissible κ h)
    (htr : h ConstraintType.transitionRight = 0) :
    (∏ τ : ConstraintType,
        Nat.multichoose (endpointAugmentedActiveProfileDim τ) (h τ))
      ≤ withinProfileBound κ := by
  classical
  have hfac : ∀ τ : ConstraintType,
      Nat.multichoose (endpointAugmentedActiveProfileDim τ) (h τ) ≤
        match τ with
        | ConstraintType.booleanity => (h ConstraintType.booleanity + 1) ^ 3
        | ConstraintType.adjacency => (h ConstraintType.adjacency + 1) ^ 3
        | ConstraintType.transitionLeft => (h ConstraintType.transitionLeft + 1) ^ 2
        | ConstraintType.transitionRight => 1 := by
    intro τ
    cases τ with
    | booleanity =>
        simpa [endpointAugmentedActiveProfileDim] using
          multichoose_four_le_pow_three (h ConstraintType.booleanity)
    | adjacency =>
        simpa [endpointAugmentedActiveProfileDim] using
          multichoose_four_le_pow_three (h ConstraintType.adjacency)
    | transitionLeft =>
        simpa [endpointAugmentedActiveProfileDim] using
          multichoose_three_le_pow_two (h ConstraintType.transitionLeft)
    | transitionRight =>
        simp [endpointAugmentedActiveProfileDim, htr, Nat.multichoose_zero_right]
  have hprod_le :
      (∏ τ : ConstraintType,
          Nat.multichoose (endpointAugmentedActiveProfileDim τ) (h τ))
        ≤
      ∏ τ : ConstraintType,
        match τ with
        | ConstraintType.booleanity => (h ConstraintType.booleanity + 1) ^ 3
        | ConstraintType.adjacency => (h ConstraintType.adjacency + 1) ^ 3
        | ConstraintType.transitionLeft => (h ConstraintType.transitionLeft + 1) ^ 2
        | ConstraintType.transitionRight => 1 :=
    Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun τ _ => hfac τ)
  have huniv :
      (Finset.univ : Finset ConstraintType) =
        {ConstraintType.booleanity, ConstraintType.adjacency,
          ConstraintType.transitionLeft, ConstraintType.transitionRight} := by
    ext τ
    fin_cases τ <;> simp
  have hprod_eval :
      (∏ τ : ConstraintType,
        match τ with
        | ConstraintType.booleanity => (h ConstraintType.booleanity + 1) ^ 3
        | ConstraintType.adjacency => (h ConstraintType.adjacency + 1) ^ 3
        | ConstraintType.transitionLeft => (h ConstraintType.transitionLeft + 1) ^ 2
        | ConstraintType.transitionRight => 1) =
        (h ConstraintType.booleanity + 1) ^ 3 *
          (h ConstraintType.adjacency + 1) ^ 3 *
          (h ConstraintType.transitionLeft + 1) ^ 2 := by
    rw [huniv]
    simp
    ring
  have hb :
      h ConstraintType.booleanity ≤ κ :=
    admissibleProfile_component_le hadm ConstraintType.booleanity
  have ha :
      h ConstraintType.adjacency ≤ κ :=
    admissibleProfile_component_le hadm ConstraintType.adjacency
  have hl :
      h ConstraintType.transitionLeft ≤ κ :=
    admissibleProfile_component_le hadm ConstraintType.transitionLeft
  have hpow_b :
      (h ConstraintType.booleanity + 1) ^ 3 ≤ (κ + 1) ^ 3 :=
    Nat.pow_le_pow_left (by omega) 3
  have hpow_a :
      (h ConstraintType.adjacency + 1) ^ 3 ≤ (κ + 1) ^ 3 :=
    Nat.pow_le_pow_left (by omega) 3
  have hpow_l :
      (h ConstraintType.transitionLeft + 1) ^ 2 ≤ (κ + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hprod_pow :
      (h ConstraintType.booleanity + 1) ^ 3 *
          (h ConstraintType.adjacency + 1) ^ 3 *
          (h ConstraintType.transitionLeft + 1) ^ 2
        ≤ (κ + 1) ^ 8 := by
    calc
      (h ConstraintType.booleanity + 1) ^ 3 *
          (h ConstraintType.adjacency + 1) ^ 3 *
          (h ConstraintType.transitionLeft + 1) ^ 2
          ≤ (κ + 1) ^ 3 * (κ + 1) ^ 3 * (κ + 1) ^ 2 := by
            exact Nat.mul_le_mul
              (Nat.mul_le_mul hpow_b hpow_a) hpow_l
      _ = (κ + 1) ^ 8 := by ring
  calc
    (∏ τ : ConstraintType,
        Nat.multichoose (endpointAugmentedActiveProfileDim τ) (h τ))
        ≤ ∏ τ : ConstraintType,
          match τ with
          | ConstraintType.booleanity => (h ConstraintType.booleanity + 1) ^ 3
          | ConstraintType.adjacency => (h ConstraintType.adjacency + 1) ^ 3
          | ConstraintType.transitionLeft => (h ConstraintType.transitionLeft + 1) ^ 2
          | ConstraintType.transitionRight => 1 := hprod_le
    _ = (h ConstraintType.booleanity + 1) ^ 3 *
          (h ConstraintType.adjacency + 1) ^ 3 *
          (h ConstraintType.transitionLeft + 1) ^ 2 := hprod_eval
    _ ≤ (κ + 1) ^ 8 := hprod_pow
    _ = withinProfileBound κ := by rfl

/-- The endpoint-augmented concrete family satisfies the live active-profile
budget directly.  The key point is that the sharpened endpoint dimensions are
`4,4,3` on the three active coordinates, while the dormant right coordinate
has zero mass in this slice. -/
theorem endpointAugmentedActiveProfileSubspaceBudget
    (n : ℕ) (hn4 : n ≥ 4) :
    EndpointAugmentedActiveProfileSubspaceBudget n hn4 := by
  intro h hadm htr _hactive
  constructor
  · exact cookLevinProfileSubspace_finite
      (admissibleToBounded hadm)
      (endpointAugmentedConcreteW n hn4)
      (endpointAugmentedConcreteW_finite n hn4)
  · have hprofile :
        Module.finrank ℚ
            ↥(cookLevinProfileSubspace
              (admissibleToBounded hadm)
              (endpointAugmentedConcreteW n hn4))
          ≤
        ∏ τ : ConstraintType, Nat.multichoose
          (Module.finrank ℚ ↥(endpointAugmentedConcreteW n hn4 τ))
          (h τ) := by
      simpa using
        cookLevinProfileSubspace_finrank_le_by_finrank
          (admissibleToBounded hadm)
          (endpointAugmentedConcreteW n hn4)
          (endpointAugmentedConcreteW_finite n hn4)
    have hdim_le : ∀ τ : ConstraintType,
        Module.finrank ℚ ↥(endpointAugmentedConcreteW n hn4 τ) ≤
          endpointAugmentedActiveProfileDim τ :=
      endpointAugmentedConcreteW_finrank_le_activeProfileDim n hn4
    have hmulti_mono :
        (∏ τ : ConstraintType, Nat.multichoose
          (Module.finrank ℚ ↥(endpointAugmentedConcreteW n hn4 τ))
          (h τ))
          ≤
        ∏ τ : ConstraintType,
          Nat.multichoose (endpointAugmentedActiveProfileDim τ) (h τ) := by
      refine Finset.prod_le_prod (fun _ _ => Nat.zero_le _) ?_
      intro τ _
      exact multichoose_mono_left _ _ _ (hdim_le τ)
    exact le_trans hprofile
      (le_trans hmulti_mono
        (endpointAugmentedActiveProfile_multichoose_le_withinProfileBound
          (Nat.log 2 n) h hadm htr))

/-- Corrected endpoint-augmented low-dimensional profile-span gate.

This is the endpoint-augmented retarget after the same-profile closure
obstruction: prove containment of the active Cook-Levin post-span in the
endpoint-augmented profile subspace, then use the checked `4,4,3` active
dimension budget to close the common-span profile. -/
theorem cookLevinAllBoundedProfileCommonSpanAtProfile_of_endpointAugmented_profileSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (h : ProfileHistogram)
    (hadm : ProfileAdmissible (Nat.log 2 n) h)
    (htr : h ConstraintType.transitionRight = 0)
    (hactive : ActiveProfileSupport h)
    (hProfileSpan :
      cookLevinPostSpanAt M n hn htb hns h ≤
        cookLevinProfileSubspace (admissibleToBounded hadm)
          (endpointAugmentedConcreteW n hn4)) :
    CookLevinAllBoundedProfileCommonSpanAtProfile M n hn htb hns h := by
  classical
  rcases endpointAugmentedActiveProfileSubspaceBudget n hn4
      h hadm htr hactive with
    ⟨hProfileFinite, hProfileBound⟩
  letI : Module.Finite ℚ
      ↥(cookLevinProfileSubspace (admissibleToBounded hadm)
        (endpointAugmentedConcreteW n hn4)) :=
    hProfileFinite
  have hmono :
      Module.finrank ℚ ↥(cookLevinPostSpanAt M n hn htb hns h)
        ≤ Module.finrank ℚ
            ↥(cookLevinProfileSubspace (admissibleToBounded hadm)
              (endpointAugmentedConcreteW n hn4)) :=
    Submodule.finrank_mono hProfileSpan
  have hdim_all :
      Module.finrank ℚ
          ↥(allBoundedProfilePostSpan
            (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn htb hns).get i)
            (cookLevinConstraintType M n hn htb hns)
            h)
        ≤ withinProfileBound (Nat.log 2 n) := by
    change
      Module.finrank ℚ ↥(cookLevinPostSpanAt M n hn htb hns h)
        ≤ withinProfileBound (Nat.log 2 n)
    exact le_trans hmono hProfileBound
  exact
    cookLevinAllBoundedProfileCommonSpanAtProfile_of_allBoundedProfilePostSpan_finrank
      M n hn htb hns h hdim_all

/-- A profile-local endpoint-augmented row embedding plus the explicit
active-profile budget closes the fixed common-span target. -/
theorem cookLevinAllBoundedProfileCommonSpanAtProfile_of_endpointAugmented_spanningAtProfile
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (h : ProfileHistogram)
    (hadm : ProfileAdmissible (Nat.log 2 n) h)
    (htr : h ConstraintType.transitionRight = 0)
    (hactive : ActiveProfileSupport h)
    (hBudget : EndpointAugmentedActiveProfileSubspaceBudget n hn4)
    (hSpanAt :
      CookLevinPerTypeSpanningAtBoundedProfile M n hn htb hns
        (endpointAugmentedConcreteW n hn4)
        (admissibleToBounded hadm)) :
    CookLevinAllBoundedProfileCommonSpanAtProfile M n hn htb hns h := by
  classical
  rcases hBudget h hadm htr hactive with ⟨hProfileFinite, hProfileBound⟩
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

/-- Charged target-profile cover version of the endpoint-augmented
active-profile common-span gate.

This avoids the false same-profile/self-targeting condition.  The source
post-span is first covered by charged/restricted rows into an admissible target
profile, then the charged closure theorem places that restricted span in the
target endpoint-augmented profile subspace. -/
theorem cookLevinAllBoundedProfileCommonSpanAtProfile_of_endpointAugmented_chargedTargetCover
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (charge : ProfileCharge n)
    (hn4 : n ≥ 4)
    (h : ProfileHistogram)
    (hadm : ProfileAdmissible (Nat.log 2 n) h)
    (hFactor :
      CookLevinFactorMemPerType M n hn htb hns
        (endpointAugmentedConcreteW n hn4))
    (hCharged :
      PerTypeShiftMlprojClosureCharged (n := n) charge
        (endpointAugmentedConcreteW n hn4))
    (hBudget : EndpointAugmentedActiveProfileSubspaceBudget n hn4)
    (hCover :
      CookLevinEndpointChargedTargetProfileCoverAt
        M n hn htb hns charge h hadm) :
    CookLevinAllBoundedProfileCommonSpanAtProfile M n hn htb hns h := by
  classical
  rcases hCover with
    ⟨bpTgt, hTgtAdm, hTgtTr, hTgtActive, hCoverLe⟩
  have hChargedLe :
      cookLevinChargedPostSpanAtTarget M n hn htb hns charge
          (admissibleToBounded hadm) bpTgt
        ≤ cookLevinProfileSubspace bpTgt
            (endpointAugmentedConcreteW n hn4) :=
    cookLevinChargedPostSpanAtTarget_le_profileSubspace_discharged
      M n hn htb hns (endpointAugmentedConcreteW n hn4) charge
      (admissibleToBounded hadm) bpTgt
      hFactor
      (endpointAugmentedConcreteW_derivClosurePerType n hn4)
      hCharged
  rcases hBudget bpTgt.toHistogram hTgtAdm hTgtTr hTgtActive with
    ⟨hProfileFinite, hProfileBound⟩
  letI : Module.Finite ℚ
      ↥(cookLevinProfileSubspace bpTgt
        (endpointAugmentedConcreteW n hn4)) :=
    hProfileFinite
  have hPostLe :
      cookLevinPostSpanAt M n hn htb hns h ≤
        cookLevinProfileSubspace bpTgt
          (endpointAugmentedConcreteW n hn4) :=
    le_trans hCoverLe hChargedLe
  have hmono :
      Module.finrank ℚ ↥(cookLevinPostSpanAt M n hn htb hns h)
        ≤ Module.finrank ℚ
            ↥(cookLevinProfileSubspace bpTgt
              (endpointAugmentedConcreteW n hn4)) :=
    Submodule.finrank_mono hPostLe
  have hdim_all :
      Module.finrank ℚ
          ↥(allBoundedProfilePostSpan
            (PaperFaithfulSeparation.cook_levin_compilation M n hn htb hns).partition
            (Nat.log 2 n) (Nat.log 2 n)
            (fun i => (cookLevinFactorList M n hn htb hns).get i)
            (cookLevinConstraintType M n hn htb hns)
            h)
        ≤ withinProfileBound (Nat.log 2 n) := by
    change
      Module.finrank ℚ ↥(cookLevinPostSpanAt M n hn htb hns h)
        ≤ withinProfileBound (Nat.log 2 n)
    exact le_trans hmono hProfileBound
  exact
    cookLevinAllBoundedProfileCommonSpanAtProfile_of_allBoundedProfilePostSpan_finrank
      M n hn htb hns h hdim_all

/-- Direct endpoint-augmented active profile span containments are enough for
the active type-case blockers.  This keeps the endpoint-augmented low-
dimensional route while bypassing the uncharged same-profile closure field
that is false at booleanity mass one. -/
theorem cookLevinActiveProfileTypeCaseBlockers_of_endpointAugmented_activeProfileSpan
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hProfileSpan :
      ∀ (h : ProfileHistogram)
        (hadm : ProfileAdmissible (Nat.log 2 n) h),
          h ConstraintType.transitionRight = 0 →
            ActiveProfileSupport h →
              cookLevinPostSpanAt M n hn htb hns h ≤
                cookLevinProfileSubspace (admissibleToBounded hadm)
                  (endpointAugmentedConcreteW n hn4)) :
    CookLevinActiveProfileTypeCaseBlockers M n hn htb hns := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro h hadm htr _hne hpos
    exact
      cookLevinAllBoundedProfileCommonSpanAtProfile_of_endpointAugmented_profileSpan
        M n hn htb hns hn4 h hadm htr (Or.inl hpos)
        (hProfileSpan h hadm htr (Or.inl hpos))
  · intro h hadm htr _hne hpos
    exact
      cookLevinAllBoundedProfileCommonSpanAtProfile_of_endpointAugmented_profileSpan
        M n hn htb hns hn4 h hadm htr (Or.inr (Or.inl hpos))
        (hProfileSpan h hadm htr (Or.inr (Or.inl hpos)))
  · intro h hadm htr _hne hpos
    exact
      cookLevinAllBoundedProfileCommonSpanAtProfile_of_endpointAugmented_profileSpan
        M n hn htb hns hn4 h hadm htr (Or.inr (Or.inr hpos))
        (hProfileSpan h hadm htr (Or.inr (Or.inr hpos)))

/-- Charged target-profile covers are enough for the active type-case
blockers.  This is the active bridge shape that avoids the refuted
self-targeting endpoint charge. -/
theorem cookLevinActiveProfileTypeCaseBlockers_of_endpointAugmented_chargedTargetCover
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (charge : ProfileCharge n)
    (hn4 : n ≥ 4)
    (hFactor :
      CookLevinFactorMemPerType M n hn htb hns
        (endpointAugmentedConcreteW n hn4))
    (hCharged :
      PerTypeShiftMlprojClosureCharged (n := n) charge
        (endpointAugmentedConcreteW n hn4))
    (hBudget : EndpointAugmentedActiveProfileSubspaceBudget n hn4)
    (hCover :
      ∀ (h : ProfileHistogram)
        (hadm : ProfileAdmissible (Nat.log 2 n) h),
          h ConstraintType.transitionRight = 0 →
            h ≠ zeroProfileHistogram →
              ActiveProfileSupport h →
                CookLevinEndpointChargedTargetProfileCoverAt
                  M n hn htb hns charge h hadm) :
    CookLevinActiveProfileTypeCaseBlockers M n hn htb hns := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro h hadm htr hne hpos
    exact
      cookLevinAllBoundedProfileCommonSpanAtProfile_of_endpointAugmented_chargedTargetCover
        M n hn htb hns charge hn4 h hadm hFactor hCharged hBudget
        (hCover h hadm htr hne (Or.inl hpos))
  · intro h hadm htr hne hpos
    exact
      cookLevinAllBoundedProfileCommonSpanAtProfile_of_endpointAugmented_chargedTargetCover
        M n hn htb hns charge hn4 h hadm hFactor hCharged hBudget
        (hCover h hadm htr hne (Or.inr (Or.inl hpos)))
  · intro h hadm htr hne hpos
    exact
      cookLevinAllBoundedProfileCommonSpanAtProfile_of_endpointAugmented_chargedTargetCover
        M n hn htb hns charge hn4 h hadm hFactor hCharged hBudget
        (hCover h hadm htr hne (Or.inr (Or.inr hpos)))

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

private theorem zero_ne_single_add_single_one
    {α : Type*} [DecidableEq α] (v w : α) :
    (0 : α →₀ ℕ) ≠ Finsupp.single v 1 + Finsupp.single w 1 := by
  intro h
  have hv := DFunLike.congr_fun h v
  rw [Finsupp.coe_zero, Pi.zero_apply, Finsupp.add_apply,
    Finsupp.single_apply, if_pos rfl] at hv
  by_cases hwv : w = v
  · rw [Finsupp.single_apply, if_pos hwv] at hv
    omega
  · rw [Finsupp.single_apply, if_neg hwv] at hv
    omega

private theorem single_one_ne_single_add_single_one
    {α : Type*} [DecidableEq α] (a v w : α) :
    Finsupp.single a 1 ≠ Finsupp.single v 1 + Finsupp.single w 1 := by
  intro h
  have hsum :
      (Finsupp.single a 1 : α →₀ ℕ).sum (fun _ m => m) =
        (Finsupp.single v 1 + Finsupp.single w 1 : α →₀ ℕ).sum
          (fun _ m => m) := by
    rw [h]
  rw [Finsupp.sum_add_index (by simp) (by intros; ring),
    Finsupp.sum_single_index (by rfl),
    Finsupp.sum_single_index (by rfl),
    Finsupp.sum_single_index (by rfl)] at hsum
  omega

private theorem single_two_ne_single_add_single_one_of_ne
    {α : Type*} [DecidableEq α] {a v : α} (hva : v ≠ a) :
    Finsupp.single a 2 ≠ Finsupp.single v 1 + Finsupp.single a 1 := by
  intro h
  have hv := DFunLike.congr_fun h v
  simp [Finsupp.add_apply, hva] at hv

private theorem isMultilinear_single_add_single_one
    {α : Type*} [DecidableEq α] {v w : α} (hvw : v ≠ w) :
    Finsupp.IsMultilinear
      (Finsupp.single v 1 + Finsupp.single w 1 : α →₀ ℕ) := by
  intro i
  by_cases hiv : i = v
  · subst i
    simp [Finsupp.add_apply, hvw.symm]
  · by_cases hiw : i = w
    · subst i
      simp [Finsupp.add_apply, hiv]
    · simp [Finsupp.add_apply, hiv, hiw]

private theorem concreteWEndpointSpan_coeff_endpoint0_cross_eq_zero_of_ne
    {n : ℕ} {hn4 : n ≥ 4} {v : Fin n}
    {p : MvPolynomial (Fin n) ℚ}
    (hp : p ∈ concreteWEndpointSpan n hn4) :
    MvPolynomial.coeff
        (Finsupp.single v 1 +
          Finsupp.single (concreteWEndpoint0 n hn4) 1) p = 0 := by
  unfold concreteWEndpointSpan at hp
  refine Submodule.span_induction
    (p := fun q _ =>
      MvPolynomial.coeff
        (Finsupp.single v 1 +
          Finsupp.single (concreteWEndpoint0 n hn4) 1) q = 0)
    ?_ ?_ ?_ ?_ hp
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · simp [MvPolynomial.coeff_one, zero_ne_single_add_single_one]
    · simp [MvPolynomial.coeff_X']
    · simp [MvPolynomial.coeff_X',
        single_one_ne_single_add_single_one]
  · simp
  · intro p q _ _ hp hq
    simp [hp, hq]
  · intro a p _ hp
    simp [hp]

private theorem concreteWCanonical_booleanity_coeff_endpoint0_cross_eq_zero_of_ne
    {n : ℕ} {hn4 : n ≥ 4} {v : Fin n}
    (hv0 : v ≠ concreteWEndpoint0 n hn4)
    {p : MvPolynomial (Fin n) ℚ}
    (hp : p ∈ concreteWCanonical n hn4 ConstraintType.booleanity) :
    MvPolynomial.coeff
        (Finsupp.single v 1 +
          Finsupp.single (concreteWEndpoint0 n hn4) 1) p = 0 := by
  unfold concreteWCanonical concreteW at hp
  unfold ambientPerTypeSpace at hp
  rw [Submodule.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  unfold perTypeInterfaceSpace at hq
  refine Submodule.span_induction
    (p := fun q _ =>
      MvPolynomial.coeff
        (Finsupp.single v 1 +
          Finsupp.single (concreteWEndpoint0 n hn4) 1)
        (MvPolynomial.rename
          (Fin.castLE hn4) q) = 0)
    ?_ ?_ ?_ ?_ hq
  · intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · simp [MvPolynomial.coeff_one, zero_ne_single_add_single_one]
    · have hrename :
          MvPolynomial.rename (Fin.castLE hn4)
              (MvPolynomial.X (0 : Fin 4)) =
            (MvPolynomial.X (Fin.castLE hn4 (0 : Fin 4)) :
              MvPolynomial (Fin n) ℚ) := by
        simp
      rw [hrename]
      simp [concreteWEndpoint0, MvPolynomial.coeff_X']
    · have hrename :
          MvPolynomial.rename (Fin.castLE hn4)
              ((MvPolynomial.X (0 : Fin 4)) ^ 2) =
            ((MvPolynomial.X (Fin.castLE hn4 (0 : Fin 4)) :
              MvPolynomial (Fin n) ℚ) ^ 2) := by
        simp
      rw [hrename]
      have hv0' : v ≠ Fin.castLE hn4 (0 : Fin 4) := by
        simpa [concreteWEndpoint0] using hv0
      simp [concreteWEndpoint0, MvPolynomial.X_pow_eq_monomial,
        single_two_ne_single_add_single_one_of_ne hv0']
  · simp
  · intro p q _ _ hp hq
    simpa [map_add, Fin.castLEEmb, hp, hq]
  · intro a p _ hp
    simpa [map_smul, Fin.castLEEmb, hp]

/-- Endpoint-augmented booleanity rows have no cross term between the fixed
boolean endpoint and any different variable. -/
theorem endpointAugmentedConcreteW_booleanity_coeff_endpoint0_cross_eq_zero_of_ne
    {n : ℕ} {hn4 : n ≥ 4} {v : Fin n}
    (hv0 : v ≠ concreteWEndpoint0 n hn4)
    {p : MvPolynomial (Fin n) ℚ}
    (hp : p ∈ endpointAugmentedConcreteW n hn4 ConstraintType.booleanity) :
    MvPolynomial.coeff
        (Finsupp.single v 1 +
          Finsupp.single (concreteWEndpoint0 n hn4) 1) p = 0 := by
  rw [endpointAugmentedConcreteW, Submodule.mem_sup] at hp
  obtain ⟨pc, hpc, pe, hpe, hp_eq⟩ := hp
  rw [← hp_eq]
  simp
    [concreteWCanonical_booleanity_coeff_endpoint0_cross_eq_zero_of_ne
     hv0 hpc,
     concreteWEndpointSpan_coeff_endpoint0_cross_eq_zero_of_ne hpe]

/-- The endpoint-augmented active same-profile closure is already false at the
mass-one booleanity profile.  A two-variable shift `X₂ * X₀` applied to the
unit derivative witness would have to remain in the one-booleanity profile
space, which collapses to the booleanity row; the cross coefficient separates
it from that row. -/
theorem not_endpointAugmentedConcreteW_shiftMlprojClosureAt_booleanity_mass_one
    (n : ℕ) (hn4 : n ≥ 4)
    (bp : BoundedProfile (Nat.log 2 n))
    (hbool : bp.toHistogram ConstraintType.booleanity = 1)
    (hother :
      ∀ τ : ConstraintType, τ ≠ ConstraintType.booleanity →
        bp.toHistogram τ = 0) :
    ¬ PerTypeShiftMlprojClosureAtBoundedProfile
        (endpointAugmentedConcreteW n hn4) bp := by
  classical
  intro hClosure
  let e0 : Fin n := concreteWEndpoint0 n hn4
  let e2 : Fin n := (Fin.castLEEmb hn4) (2 : Fin 4)
  have he20 : e2 ≠ e0 := by
    simp [e2, e0, concreteWEndpoint0]
  have hSlen : ([e2, e0] : List (Fin n)).length ≤ Nat.log 2 n := by
    have hlog : 2 ≤ Nat.log 2 n :=
      Nat.le_log_of_pow_le (by norm_num : 1 < 2) (by simpa using hn4)
    simpa using hlog
  have hshift :
      (MvPolynomial.X e2 * MvPolynomial.X e0 :
          MvPolynomial (Fin n) ℚ).vars ⊆
        ([e2, e0] : List (Fin n)).toFinset := by
    intro x hx
    have hx_or :=
      MvPolynomial.vars_mul (MvPolynomial.X e2)
        (MvPolynomial.X e0 : MvPolynomial (Fin n) ℚ) hx
    simpa [MvPolynomial.vars_X] using hx_or
  have honeW :
      (1 : MvPolynomial (Fin n) ℚ) ∈
        endpointAugmentedConcreteW n hn4 ConstraintType.booleanity := by
    unfold endpointAugmentedConcreteW
    refine Submodule.mem_sup_right ?_
    unfold concreteWEndpointSpan
    exact Submodule.subset_span (by simp)
  have hg_prod :
      ∃ (L : ℕ) (factors : Fin L → MvPolynomial (Fin n) ℚ)
        (constraintType : Fin L → ConstraintType)
        (d : Fin L → List (Fin n)),
        (∀ i, ∀ v ∈ d i, v ∈ ([e2, e0] : List (Fin n))) ∧
        (∀ i, iterDerivList (d i) (factors i) ∈
          endpointAugmentedConcreteW n hn4 (constraintType i)) ∧
        (1 : MvPolynomial (Fin n) ℚ) =
          Finset.univ.prod (fun i => iterDerivList (d i) (factors i)) ∧
        derivCountProfile constraintType d = bp.toHistogram ∧
        ∑ i : Fin L, (d i).length ≤ ([e2, e0] : List (Fin n)).length := by
    refine
      ⟨1, (fun _ => (MvPolynomial.X e0 : MvPolynomial (Fin n) ℚ)),
        (fun _ => ConstraintType.booleanity), (fun _ => [e0]),
        ?_, ?_, ?_, ?_, ?_⟩
    · intro i v hv
      simp at hv ⊢
      exact Or.inr hv
    · intro i
      simpa [SPDP.iterDerivList] using honeW
    · simp [SPDP.iterDerivList]
    · funext τ
      cases τ with
      | booleanity =>
          simpa [derivCountProfile, hbool]
      | adjacency =>
          simpa [derivCountProfile,
            hother ConstraintType.adjacency (by decide)]
      | transitionLeft =>
          simpa [derivCountProfile,
            hother ConstraintType.transitionLeft (by decide)]
      | transitionRight =>
          simpa [derivCountProfile,
            hother ConstraintType.transitionRight (by decide)]
    · simp
  have hmemProfile :
      mlProj ((MvPolynomial.X e2 * MvPolynomial.X e0 :
          MvPolynomial (Fin n) ℚ) * 1) ∈
        cookLevinProfileSubspace bp (endpointAugmentedConcreteW n hn4) :=
    hClosure [e2, e0] hSlen
      (MvPolynomial.X e2 * MvPolynomial.X e0) hshift
      (1 : MvPolynomial (Fin n) ℚ) hg_prod
  have hprofile_eq :
      cookLevinProfileSubspace bp (endpointAugmentedConcreteW n hn4) =
        endpointAugmentedConcreteW n hn4 ConstraintType.booleanity := by
    unfold cookLevinProfileSubspace
    exact
      PallLean.Paper93.Canonical.profileSubspace_of_mass_one_eq
        bp.toHistogram (endpointAugmentedConcreteW n hn4)
        ConstraintType.booleanity hbool hother
  have hmemW :
      mlProj ((MvPolynomial.X e2 * MvPolynomial.X e0 :
          MvPolynomial (Fin n) ℚ) * 1) ∈
        endpointAugmentedConcreteW n hn4 ConstraintType.booleanity := by
    simpa [hprofile_eq] using hmemProfile
  let α : Fin n →₀ ℕ := Finsupp.single e2 1 + Finsupp.single e0 1
  have hzero :
      MvPolynomial.coeff α
          (mlProj ((MvPolynomial.X e2 * MvPolynomial.X e0 :
            MvPolynomial (Fin n) ℚ) * 1)) = 0 := by
    simpa [α, e0] using
      endpointAugmentedConcreteW_booleanity_coeff_endpoint0_cross_eq_zero_of_ne
        (n := n) (hn4 := hn4) (v := e2) he20 hmemW
  have hα : Finsupp.IsMultilinear α := by
    simpa [α] using isMultilinear_single_add_single_one he20
  have hmono :
      (MvPolynomial.X e2 * MvPolynomial.X e0 :
          MvPolynomial (Fin n) ℚ) =
        MvPolynomial.monomial α (1 : ℚ) := by
    dsimp [α]
    show
      (MvPolynomial.monomial (Finsupp.single e2 1) (1 : ℚ) *
          MvPolynomial.monomial (Finsupp.single e0 1) (1 : ℚ) :
          MvPolynomial (Fin n) ℚ) =
        MvPolynomial.monomial
          (Finsupp.single e2 1 + Finsupp.single e0 1) (1 : ℚ)
    rw [MvPolynomial.monomial_mul, mul_one]
  have hone :
      MvPolynomial.coeff α
          (mlProj ((MvPolynomial.X e2 * MvPolynomial.X e0 :
            MvPolynomial (Fin n) ℚ) * 1)) = 1 := by
    rw [coeff_mlProj_of_isMultilinear_mono
      (((MvPolynomial.X e2 * MvPolynomial.X e0 :
        MvPolynomial (Fin n) ℚ) * 1)) α hα]
    rw [mul_one, hmono, MvPolynomial.coeff_monomial]
    simp
  rw [hone] at hzero
  norm_num at hzero

/-- The endpoint-augmented one-profile closure frontier itself is false at the
booleanity-mass-one active profile, because its same-profile shift/mlProj field
is exactly the obstructed field isolated above. -/
theorem not_EndpointAugmentedActiveProfileClosureAtProfile_booleanity_mass_one
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (bp : BoundedProfile (Nat.log 2 n))
    (hbool : bp.toHistogram ConstraintType.booleanity = 1)
    (hother :
      ∀ τ : ConstraintType, τ ≠ ConstraintType.booleanity →
        bp.toHistogram τ = 0) :
    ¬ EndpointAugmentedActiveProfileClosureAtProfile
        M n hn htb hns hn4 bp := by
  intro hClosure
  exact
    not_endpointAugmentedConcreteW_shiftMlprojClosureAt_booleanity_mass_one
      n hn4 bp hbool hother hClosure.2

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

/-- Any endpoint-augmented active frontier forces the fixed endpoint-augmented
H3 membership package.  Thus one actual compiled factor outside the fixed
endpoint target refutes this precise frontier; a row-insensitive or transported
active target is then required. -/
theorem not_EndpointAugmentedActiveProfileFrontier_of_factor_not_mem
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (h : ProfileHistogram)
    (hadm : ProfileAdmissible (Nat.log 2 n) h)
    (htr : h ConstraintType.transitionRight = 0)
    (hne : h ≠ zeroProfileHistogram)
    (hactive : ActiveProfileSupport h)
    (i : Fin (cookLevinFactorList M n hn htb hns).length)
    (hnot :
      (cookLevinFactorList M n hn htb hns).get i ∉
        endpointAugmentedConcreteW n hn4
          (cookLevinConstraintType M n hn htb hns i)) :
    ¬ EndpointAugmentedActiveProfileFrontier M n hn htb hns hn4 := by
  intro hFrontier
  rcases hFrontier with ⟨_hBudget, hProfile⟩
  exact hnot ((hProfile h hadm htr hne hactive).1 i)

/-- The uncharged endpoint-augmented active frontier cannot be proved as
stated: its same-profile shift/mlProj field is false at the active
booleanity-mass-one profile. -/
theorem not_EndpointAugmentedActiveProfileFrontier
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4) :
    ¬ EndpointAugmentedActiveProfileFrontier M n hn htb hns hn4 := by
  intro hFrontier
  rcases hFrontier with ⟨_hBudget, hProfile⟩
  let h : ProfileHistogram :=
    fun τ =>
      match τ with
      | ConstraintType.booleanity => 1
      | ConstraintType.adjacency => 0
      | ConstraintType.transitionLeft => 0
      | ConstraintType.transitionRight => 0
  have hlog : 1 ≤ Nat.log 2 n := by
    simpa using
      singleton_length_le_log_two_of_ge_four n hn4
        (concreteWEndpoint0 n hn4)
  have hadm : ProfileAdmissible (Nat.log 2 n) h := by
    simpa [ProfileAdmissible, profileMass, h] using hlog
  have htr : h ConstraintType.transitionRight = 0 := by
    simp [h]
  have hne : h ≠ zeroProfileHistogram := by
    intro hz
    have hb := congrFun hz ConstraintType.booleanity
    simp [h, zeroProfileHistogram] at hb
  have hactive : ActiveProfileSupport h := by
    simp [ActiveProfileSupport, h]
  have hClosure :
      EndpointAugmentedActiveProfileClosureAtProfile
        M n hn htb hns hn4 (admissibleToBounded hadm) :=
    hProfile h hadm htr hne hactive
  have hbool :
      (admissibleToBounded hadm).toHistogram
          ConstraintType.booleanity = 1 := by
    simp [h]
  have hother :
      ∀ τ : ConstraintType, τ ≠ ConstraintType.booleanity →
        (admissibleToBounded hadm).toHistogram τ = 0 := by
    intro τ hτ
    cases τ with
    | booleanity => exact False.elim (hτ rfl)
    | adjacency => simp [h]
    | transitionLeft => simp [h]
    | transitionRight => simp [h]
  exact
    not_endpointAugmentedConcreteW_shiftMlprojClosureAt_booleanity_mass_one
      n hn4 (admissibleToBounded hadm) hbool hother hClosure.2

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
        M n hn htb hns hn4 h hadm htr (Or.inl hpos) hBudget
        (cookLevinPerTypeSpanningAtBoundedProfile_endpointAugmented_of_closureAtProfile
          M n hn htb hns hn4 (admissibleToBounded hadm)
          (hProfile h hadm htr hne (Or.inl hpos)))
  · intro h hadm htr hne hpos
    exact
      cookLevinAllBoundedProfileCommonSpanAtProfile_of_endpointAugmented_spanningAtProfile
        M n hn htb hns hn4 h hadm htr (Or.inr (Or.inl hpos)) hBudget
        (cookLevinPerTypeSpanningAtBoundedProfile_endpointAugmented_of_closureAtProfile
          M n hn htb hns hn4 (admissibleToBounded hadm)
          (hProfile h hadm htr hne (Or.inr (Or.inl hpos))))
  · intro h hadm htr hne hpos
    exact
      cookLevinAllBoundedProfileCommonSpanAtProfile_of_endpointAugmented_spanningAtProfile
        M n hn htb hns hn4 h hadm htr (Or.inr (Or.inr hpos)) hBudget
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
        M n hn htb hns hn4 h hadm htr (Or.inl hpos) hBudget
        (cookLevinPerTypeSpanningAtBoundedProfile_endpointAugmented_of_chargedClosureAtProfile
          M n hn htb hns charge hn4 (admissibleToBounded hadm)
          (hProfile h hadm htr hne (Or.inl hpos)))
  · intro h hadm htr hne hpos
    exact
      cookLevinAllBoundedProfileCommonSpanAtProfile_of_endpointAugmented_spanningAtProfile
        M n hn htb hns hn4 h hadm htr (Or.inr (Or.inl hpos)) hBudget
        (cookLevinPerTypeSpanningAtBoundedProfile_endpointAugmented_of_chargedClosureAtProfile
          M n hn htb hns charge hn4 (admissibleToBounded hadm)
          (hProfile h hadm htr hne (Or.inr (Or.inl hpos))))
  · intro h hadm htr hne hpos
    exact
      cookLevinAllBoundedProfileCommonSpanAtProfile_of_endpointAugmented_spanningAtProfile
        M n hn htb hns hn4 h hadm htr (Or.inr (Or.inr hpos)) hBudget
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
#print axioms CookLevinFactorMemPerType_endpointAugmentedConcreteW_of_concreteW
#print axioms CookLevinFactorMemPerType_endpointAugmentedConcreteW_of_canonicalShapeWitnesses
#print axioms CookLevinFactorMemPerType_endpointAugmentedConcreteW_of_directBranchShapes_transport
#print axioms cookLevinPerTypeSpanningAtBoundedProfile_of_perTypeSpanning
#print axioms cookLevinProfileSubspace_contains_postSpan_at_bp_of_perTypeSpanningAtBoundedProfile
#print axioms perTypeShiftMlprojClosureAtBoundedProfile_of_global
#print axioms perTypeShiftMlprojClosureAtBoundedProfile_of_charged_self
#print axioms cookLevinPerTypeChargedSpanningAtBoundedProfileTarget_discharged
#print axioms cookLevinPostSpanAt_le_chargedTarget_of_chargedSpanningAtBoundedProfileTarget
#print axioms cookLevinChargedPostSpanAtTarget_le_profileSubspace_of_chargedSpanningAtBoundedProfileTarget
#print axioms cookLevinChargedPostSpanAtTarget_le_profileSubspace_discharged
#print axioms CookLevinEndpointChargedTargetProfileCoverAt_of_generatorCover
#print axioms cookLevinAllBoundedProfileCommonSpanAtProfile_of_endpointAugmented_chargedTargetCover
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_endpointAugmented_chargedTargetCover
#print axioms cookLevinPerTypeSpanningAtBoundedProfile_discharged
#print axioms endpointAugmentedActiveProfileSubspaceBudget_of_dim_le_three
#print axioms compiledCoefficientBasis_activeProfileSubspaceBudget
#print axioms one_mem_interfaceSpace_compiledBasis_activeType
#print axioms compiledBasis_booleanity_basicRows_mem
#print axioms compiledBasis_adjacency_basicRows_mem
#print axioms compiledBasis_transitionLeft_basicRow_mem
#print axioms cookLevinAllBoundedProfileCommonSpanAtProfile_of_interfaceAnonymousProfileSpan
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_interfaceAnonymous_activeProfileSpan
#print axioms cookLevinAllBoundedProfileCommonSpanAtProfile_of_endpointAugmented_profileSpan
#print axioms cookLevinAllBoundedProfileCommonSpanAtProfile_of_endpointAugmented_spanningAtProfile
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_endpointAugmented_activeProfileSpan
#print axioms cookLevinPerTypeSpanningAtBoundedProfile_endpointAugmented_of_closureAtProfile
#print axioms endpointAugmentedConcreteW_booleanity_coeff_endpoint0_cross_eq_zero_of_ne
#print axioms not_endpointAugmentedConcreteW_shiftMlprojClosureAt_booleanity_mass_one
#print axioms not_EndpointAugmentedActiveProfileClosureAtProfile_booleanity_mass_one
#print axioms not_EndpointAugmentedActiveProfileFrontier_of_factor_not_mem
#print axioms not_EndpointAugmentedActiveProfileFrontier
#print axioms cookLevinPerTypeSpanningAtBoundedProfile_endpointAugmented_of_chargedClosureAtProfile
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_endpointAugmentedActiveProfileFrontier
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_endpointAugmentedActiveProfileChargedFrontier
#print axioms cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_endpointAugmentedActiveProfileFrontier
#print axioms cookLevinAllBoundedProfileCommonSpanLiveProfileCases_of_endpointAugmentedActiveProfileChargedFrontier

end PallLean.Paper93.DeepMath.PathB
