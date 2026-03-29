import PallLean.LocalAmbientReduction
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# SupportAmbientBasisReduction

This file reduces the ambient finrank bound to a finite squarefree-monomial spanning theorem.

For a support set `T`, the multilinear ambient should be spanned by the squarefree monomials
supported on subsets of `T`.  Once that spanning theorem is available, the finrank bound follows
from the cardinality of the squarefree support family.
-/

namespace SupportAmbientBasisReduction

open SPDP
open MultilinearSPDP
open LocalAmbientReduction
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- A squarefree monomial indexed by a support subset `U ⊆ T`. -/
noncomputable def squarefreeMonomial
    {n : ℕ}
    (U : Finset (Fin n)) :
    MvPolynomial (Fin n) F :=
  ∏ u in U, (X u : MvPolynomial (Fin n) F)

/-- The finite family of squarefree monomials on subsets of `T`. -/
noncomputable def squarefreeFamily
    {n : ℕ}
    (T : Finset (Fin n)) :
    Finset (MvPolynomial (Fin n) F) :=
  T.powerset.image (fun U => squarefreeMonomial (F := F) U)

/-- Abstract spanning theorem for the support-restricted multilinear ambient. -/
def SupportAmbientSpannedBySquarefree
    {n : ℕ}
    (T : Finset (Fin n)) : Prop :=
  supportMultilinearAmbient (F := F) T ≤
    Submodule.span F (↑(squarefreeFamily (F := F) T) : Set (MvPolynomial (Fin n) F))

/-- If the ambient is spanned by the finite squarefree family, its finrank is bounded by that cardinality. -/
theorem supportAmbient_finrank_le_squarefreeFamily_card
    {n : ℕ}
    (T : Finset (Fin n))
    (hspan : SupportAmbientSpannedBySquarefree (F := F) T) :
    Module.finrank F (supportMultilinearAmbient (F := F) T) ≤ (squarefreeFamily (F := F) T).card := by
  have hfinite : Module.Finite F
      (Submodule.span F (↑(squarefreeFamily (F := F) T) : Set (MvPolynomial (Fin n) F))) :=
    Module.Finite.span_of_finite F ((squarefreeFamily (F := F) T).finite_toSet)
  have hmono := Submodule.finrank_mono hspan
  have hspan_card :
      Module.finrank F (Submodule.span F (↑(squarefreeFamily (F := F) T) : Set (MvPolynomial (Fin n) F)))
        ≤ (squarefreeFamily (F := F) T).card := by
    exact Submodule.finrank_span_set_le_card ((squarefreeFamily (F := F) T).finite_toSet)
  exact le_trans hmono hspan_card

/-- Cardinality of the squarefree family is bounded by `2 ^ |T|`. -/
theorem squarefreeFamily_card_le_pow
    {n : ℕ}
    (T : Finset (Fin n)) :
    (squarefreeFamily (F := F) T).card ≤ 2 ^ T.card := by
  unfold squarefreeFamily
  calc
    (T.powerset.image (fun U => squarefreeMonomial (F := F) U)).card ≤ T.powerset.card :=
      Finset.card_image_le
    _ = 2 ^ T.card := by simp

/-- Therefore the ambient finrank bound reduces to a `2^|T|` estimate. -/
theorem supportAmbient_finrank_le_pow_of_squarefree
    {n : ℕ}
    (T : Finset (Fin n))
    (hspan : SupportAmbientSpannedBySquarefree (F := F) T) :
    Module.finrank F (supportMultilinearAmbient (F := F) T) ≤ 2 ^ T.card := by
  exact le_trans
    (supportAmbient_finrank_le_squarefreeFamily_card (F := F) T hspan)
    (squarefreeFamily_card_le_pow (F := F) T)

/-- In the width-4 regime, the abstract squarefree spanning theorem implies the desired ambient bound. -/
theorem supportAmbient_finrankBound_of_squarefree
    {n : ℕ}
    (hsquarefree : ∀ T : Finset (Fin n), SupportAmbientSpannedBySquarefree (F := F) T) :
    SupportAmbientFinrankBound (F := F) (n := n) := by
  intro T hT
  have hpow := supportAmbient_finrank_le_pow_of_squarefree (F := F) T (hsquarefree T)
  have : 2 ^ T.card ≤ 16 := by
    calc
      2 ^ T.card ≤ 2 ^ 4 := Nat.pow_le_pow_right (by omega) hT
      _ = 16 := by norm_num
  exact le_trans hpow this

end SupportAmbientBasisReduction
