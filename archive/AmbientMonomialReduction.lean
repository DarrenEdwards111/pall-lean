import PallLean.SquarefreeGeneratorReduction

/-!
# AmbientMonomialReduction

Paper-faithful final reduction of the local ambient theorem.

A multilinear polynomial with support contained in `T` is a sum of monomials whose
exponent vectors are squarefree and whose supports lie in `T`.  Therefore, to prove the
ambient squarefree-spanning theorem, it is enough to prove the monomialwise statement:

* every multilinear monomial supported in `T` belongs to the squarefree span on `T`.
-/

namespace AmbientMonomialReduction

open SPDP
open MultilinearSPDP
open LocalAmbientReduction
open SupportAmbientBasisReduction
open SquarefreeGeneratorReduction
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- Monomialwise squarefree support theorem. -/
def SquarefreeMonomialInFamilySpan {n : ℕ} (T : Finset (Fin n)) : Prop :=
  ∀ (α : Fin n →₀ ℕ) (a : F),
    Finsupp.IsMultilinear α →
    (∀ i ∈ α.support, i ∈ T) →
    MvPolynomial.monomial α a ∈
      Submodule.span F (↑(squarefreeFamily (F := F) T) : Set (MvPolynomial (Fin n) F))

/-- If every multilinear supported monomial lies in the squarefree family span,
then every ambient generator does too. -/
theorem ambientGeneratorInSquarefreeSpan_of_monomialwise
    {n : ℕ}
    (T : Finset (Fin n))
    (hmono : SquarefreeMonomialInFamilySpan (F := F) T) :
    AmbientGeneratorInSquarefreeSpan (F := F) T := by
  intro q hml hvars
  rw [MvPolynomial.as_sum q]
  apply Submodule.sum_mem
  intro α hα
  apply hmono α (MvPolynomial.coeff α q)
  · intro i
    exact hml α hα i
  · intro i hi
    have : i ∈ q.vars := by
      rw [MvPolynomial.mem_vars]
      exact ⟨α, hα, hi⟩
    exact hvars this

end AmbientMonomialReduction
