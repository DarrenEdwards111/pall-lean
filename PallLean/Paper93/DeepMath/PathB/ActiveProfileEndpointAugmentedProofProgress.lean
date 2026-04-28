import PallLean.Paper93.DeepMath.PathB.ActiveProfileEndpointAugmentedProgress
import PallLean.Paper93.Closure.PerTypeClosure

/-!
# Active-profile endpoint-augmented proof progress

This file uses the direct active-profile span criteria from
`ActiveProfileEndpointAugmentedProgress` without going through the blocked
same-profile endpoint self-charge route.
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
open PallLean.SymTensorPowerDim (symPower)

attribute [local instance] Classical.dec

/-! ## Monotonicity into the endpoint-augmented target -/

/-- Symmetric powers are monotone under enlargement of the underlying
submodule. -/
theorem symPower_mono_of_le
    {n k : ℕ}
    {W W' : Submodule ℚ (MvPolynomial (Fin n) ℚ)}
    (hW : W ≤ W') :
    symPower ℚ k W ≤ symPower ℚ k W' := by
  classical
  unfold symPower
  refine Submodule.span_mono ?_
  rintro p ⟨f, hf, rfl⟩
  exact ⟨f, fun i => hW (hf i), rfl⟩

/-- Profile subspaces are monotone under pointwise enlargement of the per-type
family. -/
theorem profileSubspace_mono_of_le
    {n : ℕ} {h : ProfileHistogram}
    {W W' : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)}
    (hW : ∀ τ, W τ ≤ W' τ) :
    profileSubspace h W ≤ profileSubspace h W' := by
  classical
  unfold profileSubspace
  refine Submodule.span_mono ?_
  rintro p ⟨f, hf, rfl⟩
  exact ⟨f, fun τ => symPower_mono_of_le (hW τ) (hf τ), rfl⟩

/-- Cook-Levin profile subspaces inherit pointwise monotonicity of the per-type
family. -/
theorem cookLevinProfileSubspace_mono_of_le
    {n : ℕ} (bp : BoundedProfile (Nat.log 2 n))
    {W W' : ConstraintType → Submodule ℚ (MvPolynomial (Fin n) ℚ)}
    (hW : ∀ τ, W τ ≤ W' τ) :
    cookLevinProfileSubspace bp W ≤ cookLevinProfileSubspace bp W' := by
  unfold cookLevinProfileSubspace
  exact profileSubspace_mono_of_le hW

/-- The canonical concreteW family embeds pointwise into the
endpoint-augmented family. -/
theorem concreteWCanonical_le_endpointAugmentedConcreteW
    (n : ℕ) (hn4 : n ≥ 4) (τ : ConstraintType) :
    concreteWCanonical n hn4 τ ≤ endpointAugmentedConcreteW n hn4 τ := by
  intro p hp
  unfold endpointAugmentedConcreteW
  exact Submodule.mem_sup_left hp

/-- Therefore every canonical concreteW profile subspace embeds into the
corresponding endpoint-augmented profile subspace. -/
theorem cookLevinProfileSubspace_concreteWCanonical_le_endpointAugmentedConcreteW
    (n : ℕ) (hn4 : n ≥ 4)
    (bp : BoundedProfile (Nat.log 2 n)) :
    cookLevinProfileSubspace bp (concreteWCanonical n hn4) ≤
      cookLevinProfileSubspace bp (endpointAugmentedConcreteW n hn4) :=
  cookLevinProfileSubspace_mono_of_le bp
    (concreteWCanonical_le_endpointAugmentedConcreteW n hn4)

/-! ## Concrete row embeddings as endpoint-augmented active spans -/

/-- Existing concreteW row embeddings give the actual post-span containment
into the endpoint-augmented compiled target. -/
theorem cookLevinPostSpanAt_le_endpointAugmentedConcreteW_of_concreteW_rowEmbeddings
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (bp : BoundedProfile (Nat.log 2 n))
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    cookLevinPostSpanAt M n hn htb hns bp.toHistogram ≤
      cookLevinProfileSubspace bp (endpointAugmentedConcreteW n hn4) := by
  have hConcrete :
      cookLevinPostSpanAt M n hn htb hns bp.toHistogram ≤
        cookLevinProfileSubspace bp (concreteWCanonical n hn4) := by
    simpa [cookLevinPostSpanAt, concreteWCanonical] using
      PallLean.Paper93.Direct.cookLevinProfileSubspace_contains_postSpan_direct
        M n hn htb hns hn4 bp hRowEmbeddings
  exact le_trans hConcrete
    (cookLevinProfileSubspace_concreteWCanonical_le_endpointAugmentedConcreteW
      n hn4 bp)

/-- Existing concreteW row embeddings give the actual endpoint-augmented
per-profile spanning slice.

This is the proof-level active Route B gate: for a fixed bounded profile, the
per-generator concreteW containment is transported into the endpoint-augmented
profile space by the pointwise inclusion
`concreteWCanonical ≤ endpointAugmentedConcreteW`.  No same-profile endpoint
I5 or self-targeting charge is used. -/
theorem cookLevinPerTypeSpanningAtBoundedProfile_endpointAugmented_of_concreteW_rowEmbeddings
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (bp : BoundedProfile (Nat.log 2 n))
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    CookLevinPerTypeSpanningAtBoundedProfile M n hn htb hns
      (endpointAugmentedConcreteW n hn4) bp := by
  classical
  intro S hSlen shift hshift g hg
  have hConcrete :
      mlProj (shift * g) ∈
        cookLevinProfileSubspace bp (concreteWCanonical n hn4) := by
    have hSpanAt :
        CookLevinPerTypeSpanningAtBoundedProfile M n hn htb hns
          (concreteWCanonical n hn4) bp :=
      cookLevinPerTypeSpanningAtBoundedProfile_of_perTypeSpanning
        M n hn htb hns (concreteWCanonical n hn4) bp
        (by simpa [concreteWCanonical] using hRowEmbeddings)
    exact hSpanAt S hSlen shift hshift g hg
  exact
    cookLevinProfileSubspace_concreteWCanonical_le_endpointAugmentedConcreteW
      n hn4 bp hConcrete

/-- Existing concreteW row embeddings supply every active endpoint-augmented
per-profile spanning slice. -/
theorem endpointAugmented_spanningAtActiveProfiles_of_concreteW_rowEmbeddings
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    ∀ (h : ProfileHistogram)
      (hadm : ProfileAdmissible (Nat.log 2 n) h),
        h ConstraintType.transitionRight = 0 →
          ActiveProfileSupport h →
            CookLevinPerTypeSpanningAtBoundedProfile M n hn htb hns
              (endpointAugmentedConcreteW n hn4)
              (admissibleToBounded hadm) := by
  intro _h hadm _htr _hactive
  exact
    cookLevinPerTypeSpanningAtBoundedProfile_endpointAugmented_of_concreteW_rowEmbeddings
      M n hn htb hns hn4 (admissibleToBounded hadm) hRowEmbeddings

/-! ## Component constructor for the charged endpoint-active frontier -/

/-- Build the charged endpoint-active frontier from the actual local proof
components.

This is the proof-facing form of the paper route: canonical factor membership
is separated from product grouping, charged shift closure, multilinear
projection closure, and the active-profile self-targeting condition.  The
known false same-profile endpoint closure is not used. -/
theorem endpointAugmentedActiveProfileChargedFrontier_of_components
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (charge : ProfileCharge n) (hn4 : n ≥ 4)
    (hBudget : EndpointAugmentedActiveProfileSubspaceBudget n hn4)
    (hFactor :
      CookLevinFactorMemPerType M n hn htb hns
        (endpointAugmentedConcreteW n hn4))
    (hI1 :
      PerTypeProductGrouping (endpointAugmentedConcreteW n hn4))
    (hI2c :
      PerTypeChargedShiftClosure charge
        (endpointAugmentedConcreteW n hn4))
    (hI3 :
      PerTypeMlprojClosure (endpointAugmentedConcreteW n hn4))
    (hSelf :
      ∀ (h : ProfileHistogram)
        (hadm : ProfileAdmissible (Nat.log 2 n) h),
          h ConstraintType.transitionRight = 0 →
            h ≠ zeroProfileHistogram →
              ActiveProfileSupport h →
                ProfileChargeSelfAtBoundedProfile charge
                  (admissibleToBounded hadm)) :
    EndpointAugmentedActiveProfileChargedFrontier
      M n hn htb hns charge hn4 := by
  refine ⟨hBudget, ?_⟩
  intro h hadm htr hne hactive
  exact ⟨hFactor, hI1, hI2c, hI3, hSelf h hadm htr hne hactive⟩

/-- Canonical concreteW shape witnesses provide the factor-membership field
of the charged endpoint-active frontier. -/
theorem endpointAugmentedActiveProfileChargedFrontier_of_canonicalShape_components
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (charge : ProfileCharge n) (hn4 : n ≥ 4)
    (hBudget : EndpointAugmentedActiveProfileSubspaceBudget n hn4)
    (hShape :
      CookLevinCanonicalConcreteWShapeWitnesses M n hn htb hns hn4)
    (hI1 :
      PerTypeProductGrouping (endpointAugmentedConcreteW n hn4))
    (hI2c :
      PerTypeChargedShiftClosure charge
        (endpointAugmentedConcreteW n hn4))
    (hI3 :
      PerTypeMlprojClosure (endpointAugmentedConcreteW n hn4))
    (hSelf :
      ∀ (h : ProfileHistogram)
        (hadm : ProfileAdmissible (Nat.log 2 n) h),
          h ConstraintType.transitionRight = 0 →
            h ≠ zeroProfileHistogram →
              ActiveProfileSupport h →
                ProfileChargeSelfAtBoundedProfile charge
                  (admissibleToBounded hadm)) :
    EndpointAugmentedActiveProfileChargedFrontier
      M n hn htb hns charge hn4 :=
  endpointAugmentedActiveProfileChargedFrontier_of_components
    M n hn htb hns charge hn4 hBudget
    (CookLevinFactorMemPerType_endpointAugmentedConcreteW_of_canonicalShapeWitnesses
      M n hn htb hns hn4 hShape)
    hI1 hI2c hI3 hSelf

/-- Build the charged endpoint-active frontier from local components, using
the checked endpoint-augmented active-profile budget. -/
theorem endpointAugmentedActiveProfileChargedFrontier_of_components_checkedBudget
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (charge : ProfileCharge n) (hn4 : n ≥ 4)
    (hFactor :
      CookLevinFactorMemPerType M n hn htb hns
        (endpointAugmentedConcreteW n hn4))
    (hI1 :
      PerTypeProductGrouping (endpointAugmentedConcreteW n hn4))
    (hI2c :
      PerTypeChargedShiftClosure charge
        (endpointAugmentedConcreteW n hn4))
    (hI3 :
      PerTypeMlprojClosure (endpointAugmentedConcreteW n hn4))
    (hSelf :
      ∀ (h : ProfileHistogram)
        (hadm : ProfileAdmissible (Nat.log 2 n) h),
          h ConstraintType.transitionRight = 0 →
            h ≠ zeroProfileHistogram →
              ActiveProfileSupport h →
                ProfileChargeSelfAtBoundedProfile charge
                  (admissibleToBounded hadm)) :
    EndpointAugmentedActiveProfileChargedFrontier
      M n hn htb hns charge hn4 :=
  endpointAugmentedActiveProfileChargedFrontier_of_components
    M n hn htb hns charge hn4
    (endpointAugmentedActiveProfileSubspaceBudget n hn4)
    hFactor hI1 hI2c hI3 hSelf

/-- Canonical concreteW shape witnesses provide the factor-membership field,
while the endpoint-augmented active-profile budget is supplied by the checked
dimension theorem. -/
theorem endpointAugmentedActiveProfileChargedFrontier_of_canonicalShape_components_checkedBudget
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (charge : ProfileCharge n) (hn4 : n ≥ 4)
    (hShape :
      CookLevinCanonicalConcreteWShapeWitnesses M n hn htb hns hn4)
    (hI1 :
      PerTypeProductGrouping (endpointAugmentedConcreteW n hn4))
    (hI2c :
      PerTypeChargedShiftClosure charge
        (endpointAugmentedConcreteW n hn4))
    (hI3 :
      PerTypeMlprojClosure (endpointAugmentedConcreteW n hn4))
    (hSelf :
      ∀ (h : ProfileHistogram)
        (hadm : ProfileAdmissible (Nat.log 2 n) h),
          h ConstraintType.transitionRight = 0 →
            h ≠ zeroProfileHistogram →
              ActiveProfileSupport h →
                ProfileChargeSelfAtBoundedProfile charge
                  (admissibleToBounded hadm)) :
    EndpointAugmentedActiveProfileChargedFrontier
      M n hn htb hns charge hn4 :=
  endpointAugmentedActiveProfileChargedFrontier_of_canonicalShape_components
    M n hn htb hns charge hn4
    (endpointAugmentedActiveProfileSubspaceBudget n hn4)
    hShape hI1 hI2c hI3 hSelf

/-- ConcreteW row embeddings close the active blockers through the direct
endpoint-augmented post-span criterion. -/
theorem cookLevinActiveProfileTypeCaseBlockers_of_concreteWRowEmbeddings_endpointAugmented
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n) (hn4 : n ≥ 4)
    (hRowEmbeddings :
      PallLean.Paper93.Direct.CookLevinPerTypeRowEmbeddings_concreteW
        M n hn htb hns hn4) :
    CookLevinActiveProfileTypeCaseBlockers M n hn htb hns := by
  refine
    cookLevinActiveProfileTypeCaseBlockers_of_endpointAugmented_activeProfileSpan
      M n hn htb hns hn4 ?_
  intro h hadm _htr _hactive
  simpa using
    cookLevinPostSpanAt_le_endpointAugmentedConcreteW_of_concreteW_rowEmbeddings
      M n hn htb hns hn4 (admissibleToBounded hadm) hRowEmbeddings

/-! ## Active profile-local span obligations -/

/-- Interface-anonymous active profile row embeddings are the exact remaining
profile-local obligation needed by the direct compiled-basis route. -/
theorem cookLevinActiveProfileTypeCaseBlockers_of_interfaceAnonymous_spanningAtActiveProfiles
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B : BlockPartition n) (ℓ : ℕ)
    (hSpanAt :
      ∀ (h : ProfileHistogram)
        (hadm : ProfileAdmissible (Nat.log 2 n) h),
          h ConstraintType.transitionRight = 0 →
            ActiveProfileSupport h →
              CookLevinPerTypeSpanningAtBoundedProfile M n hn htb hns
                (fun τ =>
                  interfaceSpace_compiledBasis B (Nat.log 2 n) ℓ τ)
                (admissibleToBounded hadm)) :
    CookLevinActiveProfileTypeCaseBlockers M n hn htb hns := by
  refine
    cookLevinActiveProfileTypeCaseBlockers_of_interfaceAnonymous_activeProfileSpan
      M n hn htb hns B ℓ ?_
  intro h hadm htr hactive
  simpa using
    cookLevinProfileSubspace_contains_postSpan_at_bp_of_perTypeSpanningAtBoundedProfile
      M n hn htb hns
      (fun τ => interfaceSpace_compiledBasis B (Nat.log 2 n) ℓ τ)
      (admissibleToBounded hadm)
      (hSpanAt h hadm htr hactive)

/-- Endpoint-augmented active profile row embeddings are the exact remaining
profile-local obligation needed by the direct endpoint route. -/
theorem cookLevinActiveProfileTypeCaseBlockers_of_endpointAugmented_spanningAtActiveProfiles
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hSpanAt :
      ∀ (h : ProfileHistogram)
        (hadm : ProfileAdmissible (Nat.log 2 n) h),
          h ConstraintType.transitionRight = 0 →
            ActiveProfileSupport h →
              CookLevinPerTypeSpanningAtBoundedProfile M n hn htb hns
                (endpointAugmentedConcreteW n hn4)
                (admissibleToBounded hadm)) :
    CookLevinActiveProfileTypeCaseBlockers M n hn htb hns := by
  refine
    cookLevinActiveProfileTypeCaseBlockers_of_endpointAugmented_activeProfileSpan
      M n hn htb hns hn4 ?_
  intro h hadm htr hactive
  simpa using
    cookLevinProfileSubspace_contains_postSpan_at_bp_of_perTypeSpanningAtBoundedProfile
      M n hn htb hns (endpointAugmentedConcreteW n hn4)
      (admissibleToBounded hadm)
      (hSpanAt h hadm htr hactive)

/-- Charged endpoint-augmented local closure gives the exact active-profile
post-span containment needed by the low-dimensional profile-span route.

This is the smaller active/profile bridge below the full concreteW
row-embedding bundle: it uses charged endpoint-local closure and the checked
endpoint-augmented H4, and it does not assert the false uncharged
same-profile endpoint frontier. -/
theorem endpointAugmented_activeProfileSpan_of_chargedFrontier
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (charge : ProfileCharge n)
    (hn4 : n ≥ 4)
    (hFrontier :
      EndpointAugmentedActiveProfileChargedFrontier
        M n hn htb hns charge hn4) :
    ∀ (h : ProfileHistogram)
      (hadm : ProfileAdmissible (Nat.log 2 n) h),
        h ConstraintType.transitionRight = 0 →
          ActiveProfileSupport h →
            cookLevinPostSpanAt M n hn htb hns h ≤
              cookLevinProfileSubspace (admissibleToBounded hadm)
                (endpointAugmentedConcreteW n hn4) := by
  intro h hadm htr hactive
  rcases hFrontier with ⟨_hBudget, hProfile⟩
  have hne : h ≠ zeroProfileHistogram := by
    intro hz
    rcases hactive with hpos | hpos | hpos
    · simp [hz] at hpos
    · simp [hz] at hpos
    · simp [hz] at hpos
  have hSpanAt :
      CookLevinPerTypeSpanningAtBoundedProfile M n hn htb hns
        (endpointAugmentedConcreteW n hn4)
        (admissibleToBounded hadm) :=
    cookLevinPerTypeSpanningAtBoundedProfile_endpointAugmented_of_chargedClosureAtProfile
      M n hn htb hns charge hn4 (admissibleToBounded hadm)
      (hProfile h hadm htr hne hactive)
  simpa using
    cookLevinProfileSubspace_contains_postSpan_at_bp_of_perTypeSpanningAtBoundedProfile
      M n hn htb hns (endpointAugmentedConcreteW n hn4)
      (admissibleToBounded hadm) hSpanAt

/-- A full interface-anonymous per-type spanning package is a sufficient
source of the active profile-local compiled-basis span obligation. -/
theorem cookLevinActiveProfileTypeCaseBlockers_of_interfaceAnonymous_perTypeSpanning
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (B : BlockPartition n) (ℓ : ℕ)
    (hSpan :
      CookLevinPerTypeSpanning M n hn htb hns
        (fun τ =>
          interfaceSpace_compiledBasis B (Nat.log 2 n) ℓ τ)) :
    CookLevinActiveProfileTypeCaseBlockers M n hn htb hns :=
  cookLevinActiveProfileTypeCaseBlockers_of_interfaceAnonymous_spanningAtActiveProfiles
    M n hn htb hns B ℓ
    (fun _h hadm _htr _hactive =>
      cookLevinPerTypeSpanningAtBoundedProfile_of_perTypeSpanning
        M n hn htb hns
        (fun τ => interfaceSpace_compiledBasis B (Nat.log 2 n) ℓ τ)
        (admissibleToBounded hadm) hSpan)

/-- A full endpoint-augmented per-type spanning package is a sufficient source
of the active profile-local endpoint span obligation. -/
theorem cookLevinActiveProfileTypeCaseBlockers_of_endpointAugmented_perTypeSpanning
    (M : DTM) (n : ℕ) (hn : n ≥ 2)
    (htb : M.timeBound ≤ 4) (hns : M.numStates ≤ n)
    (hn4 : n ≥ 4)
    (hSpan :
      CookLevinPerTypeSpanning M n hn htb hns
        (endpointAugmentedConcreteW n hn4)) :
    CookLevinActiveProfileTypeCaseBlockers M n hn htb hns :=
  cookLevinActiveProfileTypeCaseBlockers_of_endpointAugmented_spanningAtActiveProfiles
    M n hn htb hns hn4
    (fun _h hadm _htr _hactive =>
      cookLevinPerTypeSpanningAtBoundedProfile_of_perTypeSpanning
        M n hn htb hns (endpointAugmentedConcreteW n hn4)
        (admissibleToBounded hadm) hSpan)

/-! ## Axiom audit anchors -/

#print axioms symPower_mono_of_le
#print axioms profileSubspace_mono_of_le
#print axioms cookLevinProfileSubspace_mono_of_le
#print axioms concreteWCanonical_le_endpointAugmentedConcreteW
#print axioms cookLevinProfileSubspace_concreteWCanonical_le_endpointAugmentedConcreteW
#print axioms endpointAugmentedActiveProfileChargedFrontier_of_components_checkedBudget
#print axioms endpointAugmentedActiveProfileChargedFrontier_of_canonicalShape_components_checkedBudget
#print axioms cookLevinPerTypeSpanningAtBoundedProfile_endpointAugmented_of_concreteW_rowEmbeddings
#print axioms endpointAugmented_spanningAtActiveProfiles_of_concreteW_rowEmbeddings
#print axioms cookLevinPostSpanAt_le_endpointAugmentedConcreteW_of_concreteW_rowEmbeddings
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_concreteWRowEmbeddings_endpointAugmented
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_interfaceAnonymous_spanningAtActiveProfiles
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_endpointAugmented_spanningAtActiveProfiles
#print axioms endpointAugmented_activeProfileSpan_of_chargedFrontier
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_interfaceAnonymous_perTypeSpanning
#print axioms cookLevinActiveProfileTypeCaseBlockers_of_endpointAugmented_perTypeSpanning

end PallLean.Paper93.DeepMath.PathB
