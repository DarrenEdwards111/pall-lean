import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import PallLean.Paper93.Lemma31ProfileSubspaceCompiledBasis

/-!
# Pi+ boundary quotient interface (Route W)

This file starts the quotient-facing Property-2 route.  The unquotiented
`allBoundedProfilePostSpan` lives in the actual polynomial ambient and retains
position/block multiplicity.  Route W inserts an explicit linear projection
before the post-span generators are counted.  Mathematically, this is the Lean
surface corresponding to the paper's boundary-identification language: rows are
compared after the positive-cone / boundary quotient has identified equivalent
local boundary configurations.

No concrete Cook--Levin quotient is claimed here.  The file only defines the
projected post-span, the induced boundary-equivalence relation, and the exact
certificate needed to recover the Lemma-31 `(κ+1)^8` within-profile bound after
projection.
-/

namespace PallLean.Paper93.DeepMath.PathC

open MvPolynomial
open SPDP
open MultilinearSPDP
open SymmetricPowerBound
open WithinProfileBound
open PallLean.Paper93

attribute [local instance] Classical.dec

/-- Boundary-equivalence induced by a quotient/projection map.  Two ambient rows
are equivalent when the selected boundary quotient sends them to the same
projected row. -/
def BoundaryEquivalent {N : Nat}
    (project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ)
    (p q : MvPolynomial (Fin N) ℚ) : Prop :=
  project p = project q

/-- The projection-induced boundary-equivalence relation is reflexive. -/
theorem boundaryEquivalent_refl {N : Nat}
    (project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ)
    (p : MvPolynomial (Fin N) ℚ) :
    BoundaryEquivalent project p p := by
  rfl

/-- The projection-induced boundary-equivalence relation is symmetric. -/
theorem boundaryEquivalent_symm {N : Nat}
    (project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ)
    {p q : MvPolynomial (Fin N) ℚ}
    (h : BoundaryEquivalent project p q) :
    BoundaryEquivalent project q p := by
  exact h.symm

/-- The projection-induced boundary-equivalence relation is transitive. -/
theorem boundaryEquivalent_trans {N : Nat}
    (project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ)
    {p q r : MvPolynomial (Fin N) ℚ}
    (hpq : BoundaryEquivalent project p q)
    (hqr : BoundaryEquivalent project q r) :
    BoundaryEquivalent project p r := by
  exact hpq.trans hqr

/-- Projected analogue of `allBoundedProfilePostSpan`: before taking the span,
every SPDP post-row `mlProj (shift * g)` is passed through the boundary quotient
`project`.  This is the object whose dimension should be controlled by the
paper's shared `W_τ` spaces. -/
noncomputable def projectedAllBoundedProfilePostSpan {N L : Nat}
    (_B : BlockPartition N) (κ _ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ)
    (h : ProfileHistogram) :
    Submodule ℚ (MvPolynomial (Fin N) ℚ) :=
  Submodule.span ℚ
    (⋃ (S : List (Fin N)) (_ : S.length ≤ κ)
       (shift : MvPolynomial (Fin N) ℚ) (_ : shift.vars ⊆ S.toFinset),
      (fun g => project (mlProj (shift * g))) ''
        boundedProfileClassifiedSet factors constraintType S h)

/-- A fixed projected bounded-profile slice is contained in the full projected
post-span. -/
theorem projectedBoundedProfilePostSpan_le_projectedAllBoundedProfilePostSpan
    {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ)
    (h : ProfileHistogram)
    (S : List (Fin N)) (hS : S.length ≤ κ)
    (shift : MvPolynomial (Fin N) ℚ) (hshift : shift.vars ⊆ S.toFinset) :
    Submodule.span ℚ
        ((fun g => project (mlProj (shift * g))) ''
          boundedProfileClassifiedSet factors constraintType S h) ≤
      projectedAllBoundedProfilePostSpan B κ ℓ factors constraintType project h := by
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨g, hg, rfl⟩
  apply Submodule.subset_span
  simp only [Set.mem_iUnion, Set.mem_image]
  exact ⟨S, hS, shift, hshift, g, hg, rfl⟩

/-- Projected within-profile finrank claim.  This is the Route-W replacement for
asking the unquotiented ambient post-span to have small dimension. -/
def ProjectedWithinProfileFinrankClaim {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ) : Prop :=
  ∀ h : ProfileHistogram,
    Module.finrank ℚ
        ↥(projectedAllBoundedProfilePostSpan
          B κ ℓ factors constraintType project h) ≤ withinProfileBound κ

/-- Exact Route-W structural seam: after projection, every profile-`h` post-row
is contained in the canonical compiled-basis profile subspace.  Lemma 31 then
supplies the dimension bound. -/
def ProjectedPostSpanProfileContainment {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ) : Prop :=
  ∀ h : ProfileHistogram,
    ProfileAdmissible κ h →
      projectedAllBoundedProfilePostSpan B κ ℓ factors constraintType project h ≤
        profileSubspace h
          (fun σ : ConstraintType => interfaceSpace_compiledBasis B κ ℓ σ)

/-! ## Natural-profile Route W surface

The first `projectedAllBoundedProfilePostSpan` socket indexes rows by the
Leibniz derivative-count profile attached to `g`.  That is useful when shifts do
not change the profile.  For the actual Route-W quotient, however, the row being
counted is the projected post-row `project (mlProj (shift * g))`; the profile
that controls Lemma 31 is therefore the **combined/natural row profile** after
including the shift and quotient effects.

The following surface records that profile explicitly through a classifier.  It
keeps the old bounded Leibniz generator set, but bins each projected generator
under `profile h S shift g`, i.e. under the profile of the actual projected row,
not merely the derivative-count profile of `g`. -/

/-- A classifier assigning the natural/combined Route-W profile to each
projected bounded Leibniz generator.  The admissibility field is the formal
version of “the row profile is bounded by the SPDP radius”: every generated row
indexed by a list `S` of length at most `κ` receives an admissible profile at
scale `κ`. -/
structure ProjectedPostRowProfileClassifier {N L : Nat}
    (κ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType) where
  profile :
    ProfileHistogram →
      List (Fin N) → MvPolynomial (Fin N) ℚ → MvPolynomial (Fin N) ℚ →
        ProfileHistogram
  profile_admissible :
    ∀ (h : ProfileHistogram)
      (S : List (Fin N)) (_hS : S.length ≤ κ)
      (shift : MvPolynomial (Fin N) ℚ) (_hshift : shift.vars ⊆ S.toFinset)
      (g : MvPolynomial (Fin N) ℚ),
        g ∈ boundedProfileClassifiedSet factors constraintType S h →
          ProfileAdmissible κ (profile h S shift g)

/-- Full Route-W projected post-span indexed by the natural profile of the
projected row.  A generator contributes to bucket `ρ` exactly when the natural
profile classifier assigns it profile `ρ`. -/
noncomputable def naturallyProfiledProjectedPostSpan {N L : Nat}
    (_B : BlockPartition N) (κ _ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ)
    (classifier : ProjectedPostRowProfileClassifier κ factors constraintType)
    (ρ : ProfileHistogram) :
    Submodule ℚ (MvPolynomial (Fin N) ℚ) :=
  Submodule.span ℚ
    (⋃ (h : ProfileHistogram)
       (S : List (Fin N)) (_ : S.length ≤ κ)
       (shift : MvPolynomial (Fin N) ℚ) (_ : shift.vars ⊆ S.toFinset),
      (fun g => project (mlProj (shift * g))) ''
        {g : MvPolynomial (Fin N) ℚ |
          g ∈ boundedProfileClassifiedSet factors constraintType S h ∧
          classifier.profile h S shift g = ρ})

/-- A fixed naturally-profiled generator slice is contained in its full natural
profile bucket. -/
theorem naturallyProfiledProjectedPostSpan_generator_mem
    {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ)
    (classifier : ProjectedPostRowProfileClassifier κ factors constraintType)
    (h ρ : ProfileHistogram)
    (S : List (Fin N)) (hS : S.length ≤ κ)
    (shift : MvPolynomial (Fin N) ℚ) (hshift : shift.vars ⊆ S.toFinset)
    (g : MvPolynomial (Fin N) ℚ)
    (hg : g ∈ boundedProfileClassifiedSet factors constraintType S h)
    (hρ : classifier.profile h S shift g = ρ) :
    project (mlProj (shift * g)) ∈
      naturallyProfiledProjectedPostSpan
        B κ ℓ factors constraintType project classifier ρ := by
  apply Submodule.subset_span
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq]
  exact ⟨h, S, hS, shift, hshift, g, ⟨hg, hρ⟩, rfl⟩

/-- Full Route-W structural seam with natural profiles: every projected row in
profile bucket `ρ` lies in the compiled-basis profile subspace for `ρ`. -/
def NaturallyProfiledProjectedPostSpanContainment {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ)
    (classifier : ProjectedPostRowProfileClassifier κ factors constraintType) : Prop :=
  ∀ ρ : ProfileHistogram,
    ProfileAdmissible κ ρ →
      naturallyProfiledProjectedPostSpan
          B κ ℓ factors constraintType project classifier ρ ≤
        profileSubspace ρ
          (fun σ : ConstraintType => interfaceSpace_compiledBasis B κ ℓ σ)

/-- Generator-level form of natural-profile containment.  This is the precise
place where the Cook--Levin local row work belongs: for each actual projected
post-row, using its assigned natural profile, exhibit membership in the matching
compiled-basis profile subspace. -/
def NaturallyProfiledProjectedGeneratorContainment {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ)
    (classifier : ProjectedPostRowProfileClassifier κ factors constraintType) : Prop :=
  ∀ (h : ProfileHistogram)
    (S : List (Fin N)) (_hS : S.length ≤ κ)
    (shift : MvPolynomial (Fin N) ℚ) (_hshift : shift.vars ⊆ S.toFinset)
    (g : MvPolynomial (Fin N) ℚ),
      g ∈ boundedProfileClassifiedSet factors constraintType S h →
        project (mlProj (shift * g)) ∈
          profileSubspace (classifier.profile h S shift g)
            (fun σ : ConstraintType => interfaceSpace_compiledBasis B κ ℓ σ)

/-- Generator-level natural-profile containment implies the span-level Route-W
containment socket. -/
theorem naturallyProfiledProjectedPostSpanContainment_of_generatorContainment
    {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ)
    (classifier : ProjectedPostRowProfileClassifier κ factors constraintType)
    (hgen : NaturallyProfiledProjectedGeneratorContainment
      B κ ℓ factors constraintType project classifier) :
    NaturallyProfiledProjectedPostSpanContainment
      B κ ℓ factors constraintType project classifier := by
  intro ρ _hρadm
  apply Submodule.span_le.mpr
  intro q hq
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq] at hq
  rcases hq with ⟨h, S, hS, shift, hshift, g, ⟨hg, hρ⟩, rfl⟩
  rw [← hρ]
  exact hgen h S hS shift hshift g hg

/-- Natural-profile projected within-profile finrank claim. -/
def NaturallyProfiledProjectedWithinProfileFinrankClaim {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ)
    (classifier : ProjectedPostRowProfileClassifier κ factors constraintType) : Prop :=
  ∀ ρ : ProfileHistogram,
    Module.finrank ℚ
        ↥(naturallyProfiledProjectedPostSpan
          B κ ℓ factors constraintType project classifier ρ) ≤ withinProfileBound κ

/-- Lemma-31 closeout for the natural-profile Route-W socket.  The
non-admissible buckets are zero by `classifier.profile_admissible`; admissible
buckets are bounded by the compiled-basis profile-subspace dimension theorem. -/
theorem naturallyProfiledProjectedWithinProfileFinrank_of_containment
    {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ)
    (classifier : ProjectedPostRowProfileClassifier κ factors constraintType)
    (hcontain : NaturallyProfiledProjectedPostSpanContainment
      B κ ℓ factors constraintType project classifier) :
    NaturallyProfiledProjectedWithinProfileFinrankClaim
      B κ ℓ factors constraintType project classifier := by
  intro ρ
  by_cases hρadm : ProfileAdmissible κ ρ
  · haveI hprofileFinite : Module.Finite ℚ
        ↥(profileSubspace ρ
          (fun σ : ConstraintType => interfaceSpace_compiledBasis B κ ℓ σ)) := by
      classical
      let W : ConstraintType → Submodule ℚ (MvPolynomial (Fin N) ℚ) :=
        fun σ => interfaceSpace_compiledBasis B κ ℓ σ
      set d : ConstraintType → ℕ := fun σ => Module.finrank ℚ ↥(W σ) with hd_def
      haveI hW_fin : ∀ σ, Module.Finite ℚ ↥(W σ) :=
        fun σ => interfaceSpace_compiledBasis_finite B κ ℓ σ
      let b : ∀ σ, Module.Basis (Fin (d σ)) ℚ ↥(W σ) :=
        fun σ => Module.finBasis ℚ ↥(W σ)
      have hsub : profileSubspace ρ W ≤
          Submodule.span ℚ
            (Set.range (profileSymProd W b : ProfileIndex ρ d → _)) :=
        profileSubspace_le_profileSymProd_span W b
      haveI hfin_big : Module.Finite ℚ
          ↥(Submodule.span ℚ
            (Set.range (profileSymProd W b : ProfileIndex ρ d → _))) := by
        apply Module.Finite.span_of_finite
        exact Set.finite_range _
      exact Module.Finite.of_injective (Submodule.inclusion hsub) (by
        intro x y hxy
        exact Subtype.ext (congrArg
          (fun z : ↥(Submodule.span ℚ
            (Set.range (profileSymProd W b : ProfileIndex ρ d → _))) =>
            (z : MvPolynomial (Fin N) ℚ)) hxy))
    exact (Submodule.finrank_mono (hcontain ρ hρadm)).trans
      (profileSubspace_compiledBasis_finrank_le_withinProfileBound B κ ℓ ρ hρadm)
  · have hspan_zero :
        naturallyProfiledProjectedPostSpan
            B κ ℓ factors constraintType project classifier ρ = ⊥ := by
      apply le_antisymm
      · apply Submodule.span_le.mpr
        intro q hq
        simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq] at hq
        rcases hq with ⟨h, S, hS, shift, hshift, g, ⟨hg, hprof⟩, rfl⟩
        have hadm := classifier.profile_admissible h S hS shift hshift g hg
        exact False.elim (hρadm (hprof ▸ hadm))
      · exact bot_le
    rw [hspan_zero]
    simp

/-- Bundled certificate for the natural-profile Route-W socket. -/
structure NaturallyProfiledBoundaryQuotientCompressionCertificate {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType) where
  project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ
  classifier : ProjectedPostRowProfileClassifier κ factors constraintType
  project_idempotent : project.comp project = project
  profile_containment :
    NaturallyProfiledProjectedPostSpanContainment
      B κ ℓ factors constraintType project classifier

/-- A natural-profile boundary quotient certificate gives the Route-W
within-profile finrank claim. -/
theorem naturallyProfiledProjectedWithinProfileFinrank_of_boundaryQuotientCertificate
    {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (cert : NaturallyProfiledBoundaryQuotientCompressionCertificate
      B κ ℓ factors constraintType) :
    NaturallyProfiledProjectedWithinProfileFinrankClaim
      B κ ℓ factors constraintType cert.project cert.classifier :=
  naturallyProfiledProjectedWithinProfileFinrank_of_containment
    B κ ℓ factors constraintType cert.project cert.classifier cert.profile_containment

/-- Lemma-31 closeout for Route W: projected profile containment into the shared
compiled-basis `W_τ` subspace gives the desired `(κ+1)^8` bound for every
admissible profile. -/
theorem projectedWithinProfileFinrank_of_profileContainment {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ)
    (hcontain : ProjectedPostSpanProfileContainment
      B κ ℓ factors constraintType project) :
    ProjectedWithinProfileFinrankClaim B κ ℓ factors constraintType project := by
  intro h
  by_cases hadm : ProfileAdmissible κ h
  · haveI hprofileFinite : Module.Finite ℚ
        ↥(profileSubspace h
          (fun σ : ConstraintType => interfaceSpace_compiledBasis B κ ℓ σ)) := by
      classical
      let W : ConstraintType → Submodule ℚ (MvPolynomial (Fin N) ℚ) :=
        fun σ => interfaceSpace_compiledBasis B κ ℓ σ
      set d : ConstraintType → ℕ := fun σ => Module.finrank ℚ ↥(W σ) with hd_def
      haveI hW_fin : ∀ σ, Module.Finite ℚ ↥(W σ) :=
        fun σ => interfaceSpace_compiledBasis_finite B κ ℓ σ
      let b : ∀ σ, Module.Basis (Fin (d σ)) ℚ ↥(W σ) :=
        fun σ => Module.finBasis ℚ ↥(W σ)
      have hsub : profileSubspace h W ≤
          Submodule.span ℚ
            (Set.range (profileSymProd W b : ProfileIndex h d → _)) :=
        profileSubspace_le_profileSymProd_span W b
      haveI hfin_big : Module.Finite ℚ
          ↥(Submodule.span ℚ
            (Set.range (profileSymProd W b : ProfileIndex h d → _))) := by
        apply Module.Finite.span_of_finite
        exact Set.finite_range _
      exact Module.Finite.of_injective (Submodule.inclusion hsub) (by
        intro x y hxy
        exact Subtype.ext (congrArg
          (fun z : ↥(Submodule.span ℚ
            (Set.range (profileSymProd W b : ProfileIndex h d → _))) =>
            (z : MvPolynomial (Fin N) ℚ)) hxy))
    exact (Submodule.finrank_mono (hcontain h hadm)).trans
      (profileSubspace_compiledBasis_finrank_le_withinProfileBound B κ ℓ h hadm)
  · -- The projected span is zero for non-admissible profiles because any
    -- classified generator has profile mass at most `S.length ≤ κ`.
    have hproj_zero :
        projectedAllBoundedProfilePostSpan B κ ℓ factors constraintType project h = ⊥ := by
      apply le_antisymm
      · apply Submodule.span_le.mpr
        intro q hq
        simp only [Set.mem_iUnion, Set.mem_image] at hq
        rcases hq with ⟨S, hS, shift, hshift, g, hg, rfl⟩
        have hSadm : ProfileAdmissible S.length h :=
          boundedProfileClassifiedSet_profile_admissible
            factors constraintType S h g hg
        have hkadm : ProfileAdmissible κ h := le_trans hSadm hS
        exact False.elim (hadm hkadm)
      · exact bot_le
    rw [hproj_zero]
    simp

/-- A bundled boundary quotient compression certificate for Route W.  The
idempotence field records that the map is a genuine projection/quotient; the
`profile_containment` field is the real mathematical content still to be proved
for Cook--Levin / `Pi+ᵦ` rows. -/
structure BoundaryQuotientCompressionCertificate {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType) where
  project : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ
  project_idempotent : project.comp project = project
  profile_containment :
    ProjectedPostSpanProfileContainment B κ ℓ factors constraintType project

/-- A Route-W boundary quotient certificate gives the projected within-profile
finrank claim. -/
theorem projectedWithinProfileFinrank_of_boundaryQuotientCertificate {N L : Nat}
    (B : BlockPartition N) (κ ℓ : Nat)
    (factors : Fin L → MvPolynomial (Fin N) ℚ)
    (constraintType : Fin L → ConstraintType)
    (cert : BoundaryQuotientCompressionCertificate B κ ℓ factors constraintType) :
    ProjectedWithinProfileFinrankClaim B κ ℓ factors constraintType cert.project :=
  projectedWithinProfileFinrank_of_profileContainment
    B κ ℓ factors constraintType cert.project cert.profile_containment

/-! ## Axiom audit anchors -/

#print axioms boundaryEquivalent_refl
#print axioms boundaryEquivalent_symm
#print axioms boundaryEquivalent_trans
#print axioms projectedBoundedProfilePostSpan_le_projectedAllBoundedProfilePostSpan
#print axioms naturallyProfiledProjectedPostSpan_generator_mem
#print axioms naturallyProfiledProjectedPostSpanContainment_of_generatorContainment
#print axioms naturallyProfiledProjectedWithinProfileFinrank_of_containment
#print axioms naturallyProfiledProjectedWithinProfileFinrank_of_boundaryQuotientCertificate
#print axioms projectedWithinProfileFinrank_of_profileContainment
#print axioms projectedWithinProfileFinrank_of_boundaryQuotientCertificate

end PallLean.Paper93.DeepMath.PathC
