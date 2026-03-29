import PallLean.AmbientMonomialReduction

/-!
# SquarefreeMonomialIdentityReduction

Final atomic reduction on the ambient side.

For a multilinear monomial `monomial α a`, the only real content left is that it equals
`a • squarefreeMonomial α.support`. Once that identity is proved, the monomial is trivially
in the squarefree family span whenever `α.support ⊆ T`.
-/

namespace SquarefreeMonomialIdentityReduction

open SPDP
open MultilinearSPDP
open SupportAmbientBasisReduction
open AmbientMonomialReduction
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- Atomic monomial identity for multilinear exponent vectors. -/
def MultilinearMonomialEqSquarefree {n : ℕ} : Prop :=
  ∀ (α : Fin n →₀ ℕ) (a : F),
    Finsupp.IsMultilinear α →
    MvPolynomial.monomial α a = a • squarefreeMonomial (F := F) α.support

/-- The atomic monomial identity implies the ambient monomialwise squarefree-span theorem. -/
theorem squarefreeMonomialInFamilySpan_of_identity
    {n : ℕ}
    (T : Finset (Fin n))
    (hmonoId : MultilinearMonomialEqSquarefree (F := F) (n := n)) :
    SquarefreeMonomialInFamilySpan (F := F) T := by
  intro α a hml hsupp
  rw [hmonoId α a hml]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  change squarefreeMonomial (F := F) α.support ∈ ↑(squarefreeFamily (F := F) T)
  unfold squarefreeFamily
  apply Finset.mem_image.mpr
  refine ⟨α.support, ?_, rfl⟩
  exact Finset.mem_powerset.mpr (by
    intro i hi
    exact hsupp i hi)

end SquarefreeMonomialIdentityReduction
