import PallLean.ProfileCompressionRoute
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# TseitinProfileReduction

This file formalizes the final algebraic reduction step of the verifier-side
profile-compression theorem.

It does **not** prove the concrete profile-slice coverage theorem or the concrete
per-profile dimension theorem for the Tseitin verifier. Instead, it proves that
once those two ingredients are supplied, the full verifier-side SPDP bound follows
by finite-dimensional subadditivity.

So the remaining frontier is reduced from one monolithic axiom

* `tseitin_spdp_rank_bound`

to the pair of mathematically meaningful obligations:

1. **coverage**: every multilinear blocked-SPDP generator lands in some profile slice;
2. **per-slice dimension**: each profile slice has uniformly polynomial dimension.
-/

namespace TseitinProfileReduction

open SPDP
open MultilinearSPDP
open ProfileCompressionRoute
open Tseitin
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- The full profile index type for width `w` and `m` factors. -/
abbrev ProfileIndex (m w : ℕ) := Fin m → Fin (w + 1)

/--
Abstract family of profile slices for a polynomial `p`.

These are the subspaces that, in the paper, collect generators having a fixed
profile / histogram type.
-/
abbrev ProfileSliceFamily (n m w : ℕ) (F : Type*) [Field F]
    := ProfileIndex m w → Submodule F (MvPolynomial (Fin n) F)

/--
Abstract coverage hypothesis: the whole multilinear blocked-SPDP subspace is
contained in the supremum of the profile slices.
-/
def ProfileSlicesCover {n m w : ℕ} {F : Type*} [Field F]
    (B : BlockPartition n) (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F)
    (V : ProfileSliceFamily n m w F) : Prop :=
  mlBlockedSpdpSubspace B κ ℓ p ≤ ⨆ ρ : ProfileIndex m w, V ρ

/--
Uniform per-slice dimension bound.
-/
def ProfileSlicesDimBound {n m w : ℕ} {F : Type*} [Field F]
    (D : ℕ) (V : ProfileSliceFamily n m w F) : Prop :=
  ∀ ρ : ProfileIndex m w, Module.finrank F (V ρ) ≤ D

/--
The profile-compression conclusion from coverage + per-slice dimension.
-/
theorem mlBlockedSpdpRank_le_of_profile_slices
    {n m w : ℕ}
    (B : BlockPartition n) (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) F)
    (V : ProfileSliceFamily n m w F)
    (D : ℕ)
    (hcover : ProfileSlicesCover B κ ℓ p V)
    (hdim : ProfileSlicesDimBound D V) :
    mlBlockedSpdpRank B κ ℓ p ≤ ((w + 1) ^ m) * D := by
  unfold mlBlockedSpdpRank ProfileSlicesCover ProfileSlicesDimBound
  let U : ProfileIndex m w → Submodule F (MvPolynomial (Fin n) F) := V
  have hmono : Module.finrank F (mlBlockedSpdpSubspace B κ ℓ p)
      ≤ Module.finrank F (⨆ ρ : ProfileIndex m w, U ρ) :=
    Submodule.finrank_mono hcover
  have hsum : Module.finrank F (⨆ ρ : ProfileIndex m w, U ρ)
      ≤ ∑ ρ : ProfileIndex m w, Module.finrank F (U ρ) :=
    finrank_iSup_fin_le (m := Fintype.card (ProfileIndex m w))
      (fun i => U (Fintype.equivFin (ProfileIndex m w).symm i))
  have hsum' :
      (∑ ρ : ProfileIndex m w, Module.finrank F (U ρ))
        ≤ ((w + 1) ^ m) * D := by
    have hcard : Fintype.card (ProfileIndex m w) = (w + 1) ^ m := by
      simp [ProfileIndex, Fintype.card_fun, Fintype.card_fin]
    calc
      (∑ ρ : ProfileIndex m w, Module.finrank F (U ρ))
          ≤ ∑ _ρ : ProfileIndex m w, D := by
            exact Finset.sum_le_sum (fun ρ _ => hdim ρ)
      _ = (Fintype.card (ProfileIndex m w)) * D := by
            simp
      _ = ((w + 1) ^ m) * D := by rw [hcard]
  exact le_trans hmono (le_trans (by
    simpa [U] using hsum) hsum')

/--
Tseitin-specialized reduction statement.

This theorem shows that the full verifier-side SPDP bound follows once one has:

* a profile-slice cover of the Tseitin multilinear blocked-SPDP space, and
* a uniform polynomial dimension bound on each slice.
-/
theorem tseitin_spdp_rank_bound_of_profile_slices
    (n : ℕ) (κ : ℕ)
    (m w D : ℕ)
    (V : ProfileSliceFamily (tseitinNumVars (tseitinAt n)) m w ℚ)
    (hcover : ProfileSlicesCover (tseitinPartition n) κ κ (tseitinPoly ℚ n) V)
    (hdim : ProfileSlicesDimBound D V) :
    mlBlockedSpdpRank (tseitinPartition n) κ κ (tseitinPoly ℚ n)
      ≤ ((w + 1) ^ m) * D :=
  mlBlockedSpdpRank_le_of_profile_slices (F := ℚ)
    (B := tseitinPartition n) (κ := κ) (ℓ := κ) (p := tseitinPoly ℚ n)
    (V := V) (D := D) hcover hdim

/--
A convenient corollary in the polynomial target shape used on the verifier side.
-/
theorem tseitin_spdp_rank_bound_of_profile_slices_poly
    (n : ℕ) (κ : ℕ)
    (m w D C : ℕ)
    (V : ProfileSliceFamily (tseitinNumVars (tseitinAt n)) m w ℚ)
    (hcover : ProfileSlicesCover (tseitinPartition n) κ κ (tseitinPoly ℚ n) V)
    (hdim : ProfileSlicesDimBound D V)
    (hpoly : ((w + 1) ^ m) * D ≤ n ^ C) :
    mlBlockedSpdpRank (tseitinPartition n) κ κ (tseitinPoly ℚ n)
      ≤ n ^ C := by
  exact le_trans
    (tseitin_spdp_rank_bound_of_profile_slices n κ m w D V hcover hdim)
    hpoly

end TseitinProfileReduction
