import PallLean.VerifierProfileSlices
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# LocalFactorReduction

This file reduces the concrete verifier profile-slice dimension theorem to an
assembly bound from local factor-image spaces.

The point is to make the remaining irreducible step genuinely local:

* for each clause factor and derivative-count budget, bound the local image space;
* show the whole profile slice factors through an assembly space whose dimension is
  controlled by the product of those local dimensions.

We do **not** prove that final assembly theorem here. We formalize the exact theorem
shape so the remaining frontier is no longer a global verifier-slice statement.
-/

namespace LocalFactorReduction

open SPDP
open MultilinearSPDP
open Tseitin
open VerifierProfileSlices
open TseitinProfileReduction
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- Local clause-factor image spaces indexed by a profile count. -/
abbrev LocalFactorSpaceFamily (Φ : TseitinFormula) :=
  Fin Φ.clauses.length → Fin 5 → Submodule F (MvPolynomial (Fin (tseitinNumVars Φ)) F)

/-- Local dimension bounds for those spaces. -/
abbrev LocalFactorDimFamily (Φ : TseitinFormula) :=
  Fin Φ.clauses.length → Fin 5 → ℕ

/-- Product of the local dimension bounds along a profile. -/
noncomputable def profileLocalDimProduct
    (Φ : TseitinFormula)
    (localDim : LocalFactorDimFamily (F := F) Φ)
    (ρ : ProfileIndex Φ.clauses.length 4) : ℕ :=
  ∏ i : Fin Φ.clauses.length, localDim i (ρ i)

/--
Abstract local-factor assembly hypothesis for one concrete verifier profile slice.

Interpretation:

* `localSpace i k` is the image space contributed by clause factor `i` when it receives
  derivative-count `k`.
* `localDim i k` bounds the dimension of that local space.
* the concrete profile slice for `ρ` is contained in some assembly space whose dimension
  is bounded by the product of the local dimensions picked out by `ρ`.

This is the exact point where the remaining mathematics becomes local. -/
def VerifierProfileSliceFactorsThroughLocalImages
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (ρ : ProfileIndex Φ.clauses.length 4)
    (localSpace : LocalFactorSpaceFamily (F := F) Φ)
    (localDim : LocalFactorDimFamily (F := F) Φ) : Prop :=
  ∃ W : Submodule F (MvPolynomial (Fin (tseitinNumVars Φ)) F),
    profileSliceSubspace (F := F) (κ := κ) (m := Φ.clauses.length) (w := 4)
      shift (verifierFactor (F := F) Φ) S hS ρ ≤ W ∧
    (∀ i : Fin Φ.clauses.length, Module.finrank F (localSpace i (ρ i)) ≤ localDim i (ρ i)) ∧
    Module.finrank F W ≤ profileLocalDimProduct (F := F) Φ localDim ρ

/--
Once a concrete verifier profile slice factors through local image spaces, its dimension
is bounded by the product of the local dimensions. -/
theorem verifierProfileSlice_finrank_le_of_localFactorAssembly
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (ρ : ProfileIndex Φ.clauses.length 4)
    (localSpace : LocalFactorSpaceFamily (F := F) Φ)
    (localDim : LocalFactorDimFamily (F := F) Φ)
    (hfac : VerifierProfileSliceFactorsThroughLocalImages
      (F := F) Φ κ shift S hS ρ localSpace localDim) :
    Module.finrank F
      (profileSliceSubspace (F := F) (κ := κ) (m := Φ.clauses.length) (w := 4)
        shift (verifierFactor (F := F) Φ) S hS ρ)
      ≤ profileLocalDimProduct (F := F) Φ localDim ρ := by
  rcases hfac with ⟨W, hsub, _, hW⟩
  exact le_trans (Submodule.finrank_mono hsub) hW

/--
A packaged per-profile dimension reduction for the concrete verifier profile slices.

This is the theorem you can now use in the final Tseitin profile-compression route:
proving the per-profile dimension theorem reduces to proving the corresponding local
assembly hypothesis. -/
theorem verifierProfileSlice_dim_reduces_to_localAssembly
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (localSpace : LocalFactorSpaceFamily (F := F) Φ)
    (localDim : LocalFactorDimFamily (F := F) Φ)
    (hfac : ∀ ρ : ProfileIndex Φ.clauses.length 4,
      VerifierProfileSliceFactorsThroughLocalImages
        (F := F) Φ κ shift S hS ρ localSpace localDim) :
    ∀ ρ : ProfileIndex Φ.clauses.length 4,
      Module.finrank F
        (profileSliceSubspace (F := F) (κ := κ) (m := Φ.clauses.length) (w := 4)
          shift (verifierFactor (F := F) Φ) S hS ρ)
        ≤ profileLocalDimProduct (F := F) Φ localDim ρ := by
  intro ρ
  exact verifierProfileSlice_finrank_le_of_localFactorAssembly
    (F := F) Φ κ shift S hS ρ localSpace localDim (hfac ρ)

/--
A final polynomial-shape corollary: if the product of local factor dimensions is bounded
by `n^C` uniformly over profiles, then the concrete verifier profile slices satisfy the
same polynomial per-profile bound.
-/
theorem verifierProfileSlice_dim_poly_of_localAssembly
    (Φ : TseitinFormula)
    (κ : ℕ)
    (shift : MvPolynomial (Fin (tseitinNumVars Φ)) F)
    (S : List (Fin (tseitinNumVars Φ)))
    (hS : S.length = κ)
    (localSpace : LocalFactorSpaceFamily (F := F) Φ)
    (localDim : LocalFactorDimFamily (F := F) Φ)
    (C : ℕ)
    (hfac : ∀ ρ : ProfileIndex Φ.clauses.length 4,
      VerifierProfileSliceFactorsThroughLocalImages
        (F := F) Φ κ shift S hS ρ localSpace localDim)
    (hpoly : ∀ ρ : ProfileIndex Φ.clauses.length 4,
      profileLocalDimProduct (F := F) Φ localDim ρ ≤ Φ.graph.numVertices ^ C) :
    ∀ ρ : ProfileIndex Φ.clauses.length 4,
      Module.finrank F
        (profileSliceSubspace (F := F) (κ := κ) (m := Φ.clauses.length) (w := 4)
          shift (verifierFactor (F := F) Φ) S hS ρ)
        ≤ Φ.graph.numVertices ^ C := by
  intro ρ
  exact le_trans
    (verifierProfileSlice_finrank_le_of_localFactorAssembly
      (F := F) Φ κ shift S hS ρ localSpace localDim (hfac ρ))
    (hpoly ρ)

end LocalFactorReduction
