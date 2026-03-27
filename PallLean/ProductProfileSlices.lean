import PallLean.ProfileCompressionRoute
import PallLean.Leibniz
import PallLean.MultilinearSPDP

/-!
# ProductProfileSlices

Concrete profile slices for product polynomials.

This file formalizes the slice decomposition at the level of derivative-allocation
products.  It proves the clean combinatorial fact that the span of all allocation
products is contained in the supremum of the profile slices obtained by grouping
allocations by their histograms.

This is one of the remaining ingredients needed for a full profile-compression
proof of the verifier-side SPDP bound.
-/

namespace ProductProfileSlices

open SPDP
open MultilinearSPDP
open ProfileCompressionRoute
open MvPolynomial

variable {n : ℕ} {F : Type*} [Field F] [Nontrivial F]

/-- The product corresponding to a derivative allocation. -/
noncomputable def allocProduct
    {κ m : ℕ}
    (factor : Fin m → MvPolynomial (Fin n) F)
    (S : List (Fin n)) (hS : S.length = κ)
    (α : DerivAlloc κ m) :
    MvPolynomial (Fin n) F :=
  ∏ i : Fin m, iterDerivList (allocatedDerivs S hS α i) (factor i)

/-- Shifted multilinearized allocation generator. -/
noncomputable def shiftedAllocGenerator
    {κ m : ℕ}
    (shift : MvPolynomial (Fin n) F)
    (factor : Fin m → MvPolynomial (Fin n) F)
    (S : List (Fin n)) (hS : S.length = κ)
    (α : DerivAlloc κ m) :
    MvPolynomial (Fin n) F :=
  mlProj (shift * allocProduct factor S hS α)

/-- The bounded profile index carried by an allocation. -/
noncomputable def allocProfileIndex
    {κ m w : ℕ}
    (α : DerivAlloc κ m)
    (hbounded : ∀ i, allocProfile α i ≤ w) :
    ProfileIndex m w :=
  fun i => ⟨allocProfile α i, hbounded i⟩

/-- The profile slice associated to a bounded profile. -/
noncomputable def profileSliceSubspace
    {κ m w : ℕ}
    (shift : MvPolynomial (Fin n) F)
    (factor : Fin m → MvPolynomial (Fin n) F)
    (S : List (Fin n)) (hS : S.length = κ)
    (ρ : ProfileIndex m w) :
    Submodule F (MvPolynomial (Fin n) F) :=
  Submodule.span F
    { q | ∃ (α : DerivAlloc κ m) (hbounded : ∀ i, allocProfile α i ≤ w),
        allocProfileIndex α hbounded = ρ ∧
        q = shiftedAllocGenerator shift factor S hS α }

/-- The family of all profile slices. -/
noncomputable def profileSliceFamily
    {κ m w : ℕ}
    (shift : MvPolynomial (Fin n) F)
    (factor : Fin m → MvPolynomial (Fin n) F)
    (S : List (Fin n)) (hS : S.length = κ) :
    ProfileSliceFamily n m w F :=
  fun ρ => profileSliceSubspace shift factor S hS ρ

/-- Span of all bounded allocation generators. -/
noncomputable def boundedAllocSpan
    {κ m w : ℕ}
    (shift : MvPolynomial (Fin n) F)
    (factor : Fin m → MvPolynomial (Fin n) F)
    (S : List (Fin n)) (hS : S.length = κ) :
    Submodule F (MvPolynomial (Fin n) F) :=
  Submodule.span F
    { q | ∃ (α : DerivAlloc κ m) (hbounded : ∀ i, allocProfile α i ≤ w),
        q = shiftedAllocGenerator shift factor S hS α }

/-- Each bounded allocation generator lies in its own profile slice. -/
theorem shiftedAllocGenerator_mem_profileSlice
    {κ m w : ℕ}
    (shift : MvPolynomial (Fin n) F)
    (factor : Fin m → MvPolynomial (Fin n) F)
    (S : List (Fin n)) (hS : S.length = κ)
    (α : DerivAlloc κ m)
    (hbounded : ∀ i, allocProfile α i ≤ w) :
    shiftedAllocGenerator shift factor S hS α ∈
      profileSliceSubspace shift factor S hS (allocProfileIndex α hbounded) := by
  apply Submodule.subset_span
  exact ⟨α, hbounded, rfl, rfl⟩

/-- The span of all bounded allocation generators is contained in the supremum of the profile slices. -/
theorem boundedAllocSpan_le_iSup_profileSlices
    {κ m w : ℕ}
    (shift : MvPolynomial (Fin n) F)
    (factor : Fin m → MvPolynomial (Fin n) F)
    (S : List (Fin n)) (hS : S.length = κ) :
    boundedAllocSpan shift factor S hS (w := w) ≤
      ⨆ ρ : ProfileIndex m w, profileSliceSubspace shift factor S hS ρ := by
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨α, hbounded, rfl⟩
  refine Submodule.mem_iSup_of_mem (allocProfileIndex α hbounded) ?_
  exact shiftedAllocGenerator_mem_profileSlice shift factor S hS α hbounded

end ProductProfileSlices
