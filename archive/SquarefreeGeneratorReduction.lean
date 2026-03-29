import PallLean.SupportAmbientBasisReduction

/-!
# SquarefreeGeneratorReduction

This file shrinks the remaining ambient frontier from a global spanning theorem to a
single generatorwise squarefree-expansion theorem.

Instead of proving directly that the whole support-restricted multilinear ambient is spanned
by squarefree monomials, it is enough to prove that each generator of that ambient lies in the
squarefree span.
-/

namespace SquarefreeGeneratorReduction

open SPDP
open MultilinearSPDP
open LocalAmbientReduction
open SupportAmbientBasisReduction
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- Generatorwise squarefree-expansion theorem for the support ambient. -/
def AmbientGeneratorInSquarefreeSpan {n : ℕ} (T : Finset (Fin n)) : Prop :=
  ∀ q : MvPolynomial (Fin n) F,
    IsMultilinear q →
    q.vars ⊆ T →
    q ∈ Submodule.span F (↑(squarefreeFamily (F := F) T) : Set (MvPolynomial (Fin n) F))

/-- The global squarefree spanning theorem follows from the generatorwise version. -/
theorem supportAmbientSpannedBySquarefree_of_generatorwise
    {n : ℕ}
    (T : Finset (Fin n))
    (hgen : AmbientGeneratorInSquarefreeSpan (F := F) T) :
    SupportAmbientSpannedBySquarefree (F := F) T := by
  unfold SupportAmbientSpannedBySquarefree supportMultilinearAmbient
  apply Submodule.span_le.mpr
  intro q hq
  rcases hq with ⟨hqml, hqvars⟩
  exact hgen q hqml hqvars

end SquarefreeGeneratorReduction
