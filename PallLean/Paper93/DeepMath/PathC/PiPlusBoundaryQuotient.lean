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
#print axioms projectedWithinProfileFinrank_of_profileContainment
#print axioms projectedWithinProfileFinrank_of_boundaryQuotientCertificate

end PallLean.Paper93.DeepMath.PathC
