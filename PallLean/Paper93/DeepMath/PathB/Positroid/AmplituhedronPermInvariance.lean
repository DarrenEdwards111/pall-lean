import PallLean.Paper93.DeepMath.PathB.Positroid.TNNMatrixDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.EquivFin

/-!
# Permutation invariance of principal-TNN

If `A` is principal-TNN and `σ : Fin n ≃ Fin n` is a permutation, then the
"conjugated" matrix `A.submatrix σ σ` is again principal-TNN. The argument is
purely combinatorial: the principal submatrix of `A.submatrix σ σ` indexed by
`J` coincides, after a bijective relabeling of the index subtype, with the
principal submatrix of `A` indexed by the image `J' = J.map σ.toEmbedding`.
The determinant is invariant under such a relabeling
(`Matrix.det_submatrix_equiv_self`), so non-negativity transfers.

This expresses the conjugation-invariance of the amplituhedron gauge property:
permuting the rows and columns of a gauge matrix simultaneously merely relabels
the family of principal minors and leaves their values unchanged.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

/-- Principal-TNN is preserved under simultaneous row/column permutation
`A ↦ A.submatrix σ σ`. -/
theorem IsPrincipalTNN.submatrix_equiv {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsPrincipalTNN A) (σ : Fin n ≃ Fin n) :
    IsPrincipalTNN (A.submatrix σ σ) := by
  intro J
  -- Step 1: rewrite `(A.submatrix σ σ).submatrix (val) (val)` as `A.submatrix (σ ∘ val) (σ ∘ val)`
  have h_eq :
      (A.submatrix σ σ).submatrix
          (fun i : J => (i.val : Fin n)) (fun j : J => (j.val : Fin n))
        = A.submatrix (fun i : J => σ i.val) (fun j : J => σ j.val) := by
    ext i j
    rfl
  rw [h_eq]
  -- Step 2: package the image J' = J.map σ.toEmbedding and a bijection J ≃ J'
  let J' : Finset (Fin n) := J.map σ.toEmbedding
  have hImg : ∀ x : J, σ x.val ∈ J' := by
    intro x
    refine Finset.mem_map.mpr ?_
    exact ⟨x.val, x.property, rfl⟩
  let τ : J → J' := fun x => ⟨σ x.val, hImg x⟩
  have hτ_inj : Function.Injective τ := by
    intro a b h
    have h1 : σ a.val = σ b.val := Subtype.ext_iff.mp h
    have h2 : a.val = b.val := σ.injective h1
    exact Subtype.ext h2
  -- Step 3: equal cardinality of subtypes via |J| = |J'| (Finset.card_map)
  have hCardFinset : J.card = J'.card := by
    show J.card = (J.map σ.toEmbedding).card
    rw [Finset.card_map]
  have hCardFin : Fintype.card J = Fintype.card J' := by
    -- Both Fintype.card subsumes Finset.card via Fintype.card_coe.
    rw [Fintype.card_coe, Fintype.card_coe]
    exact hCardFinset
  -- Step 4: injective + equal-cardinality ⇒ bijective
  have hτ_bij : Function.Bijective τ :=
    (Fintype.bijective_iff_injective_and_card τ).mpr ⟨hτ_inj, hCardFin⟩
  let τ_equiv : J ≃ J' := Equiv.ofBijective τ hτ_bij
  -- Step 5: rewrite the inner submatrix as a (τ_equiv, τ_equiv)-reindex of the
  -- principal submatrix at J'
  have h_outer :
      A.submatrix (fun i : J => σ i.val) (fun j : J => σ j.val)
        =
      (A.submatrix (fun i : J' => (i.val : Fin n))
                   (fun j : J' => (j.val : Fin n))).submatrix τ_equiv τ_equiv := by
    ext i j
    rfl
  rw [h_outer]
  -- Step 6: a same-equivalence reindex preserves the determinant
  rw [Matrix.det_submatrix_equiv_self]
  exact hA J'

/-- Principal-TP is preserved under simultaneous row/column permutation. -/
theorem IsPrincipalTP.submatrix_equiv {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsPrincipalTP A) (σ : Fin n ≃ Fin n) :
    IsPrincipalTP (A.submatrix σ σ) := by
  intro J
  have h_eq :
      (A.submatrix σ σ).submatrix
          (fun i : J => (i.val : Fin n)) (fun j : J => (j.val : Fin n))
        = A.submatrix (fun i : J => σ i.val) (fun j : J => σ j.val) := by
    ext i j
    rfl
  rw [h_eq]
  let J' : Finset (Fin n) := J.map σ.toEmbedding
  have hImg : ∀ x : J, σ x.val ∈ J' := by
    intro x
    refine Finset.mem_map.mpr ?_
    exact ⟨x.val, x.property, rfl⟩
  let τ : J → J' := fun x => ⟨σ x.val, hImg x⟩
  have hτ_inj : Function.Injective τ := by
    intro a b h
    have h1 : σ a.val = σ b.val := Subtype.ext_iff.mp h
    have h2 : a.val = b.val := σ.injective h1
    exact Subtype.ext h2
  have hCardFinset : J.card = J'.card := by
    show J.card = (J.map σ.toEmbedding).card
    rw [Finset.card_map]
  have hCardFin : Fintype.card J = Fintype.card J' := by
    rw [Fintype.card_coe, Fintype.card_coe]
    exact hCardFinset
  have hτ_bij : Function.Bijective τ :=
    (Fintype.bijective_iff_injective_and_card τ).mpr ⟨hτ_inj, hCardFin⟩
  let τ_equiv : J ≃ J' := Equiv.ofBijective τ hτ_bij
  have h_outer :
      A.submatrix (fun i : J => σ i.val) (fun j : J => σ j.val)
        =
      (A.submatrix (fun i : J' => (i.val : Fin n))
                   (fun j : J' => (j.val : Fin n))).submatrix τ_equiv τ_equiv := by
    ext i j
    rfl
  rw [h_outer]
  rw [Matrix.det_submatrix_equiv_self]
  exact hA J'

end PallLean.Paper93.DeepMath.PathB.Positroid
