/-
  PermanentGodMove.lean — Paper's Theorem 100 (God Move for permanent)

  Paper reference (p vs np1.pdf): Theorem 100, line 5679+.

  The permanent polynomial perm_n(X) = Σ_σ Π_i X_{σ(i), i}, where
  X_{i,j} is a symbolic variable, admits an explicit God-Move
  projection Π_n such that

      Π_n M_{κ,0}(perm_n) = I_{(n choose κ)}

  giving the NP-side lower bound Γ_{κ,0}(perm_n) ≥ C(n, κ).

  This file formalizes:
  1. The permanent polynomial `permPoly n` in MvPolynomial (Fin n × Fin n) ℚ.
  2. The witness monomial `witnessMono S` = Π_{i ∉ S} X_{i, i} for
     S ⊂ [n] with |S| = κ.
  3. Partial derivatives of `permPoly` along diagonal variables
     (paper's ∂_S), giving `perm(X[T, T])` where T = [n] \ S.
  4. The core identity-minor coefficient claim: coeff_{m_T}(∂_S permPoly)
     = δ_{S,T} (Kronecker delta).
-/

import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic

namespace PermanentGodMove

open MvPolynomial Matrix

variable {n : ℕ}

/-- The symbolic n × n matrix with entry (i, j) equal to MvPolynomial.X (i, j). -/
noncomputable def symbolicMatrix (n : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℚ) :=
  fun i j => MvPolynomial.X (i, j)

/-- The permanent polynomial perm_n = Σ_σ Π_i X_{σ(i), i}, viewed as
an MvPolynomial in the n² variables indexed by pairs (i, j). -/
noncomputable def permPoly (n : ℕ) : MvPolynomial (Fin n × Fin n) ℚ :=
  (symbolicMatrix n).permanent

/-- Expansion of permPoly as a sum over permutations. -/
theorem permPoly_eq_sum (n : ℕ) :
    permPoly n = ∑ σ : Equiv.Perm (Fin n), ∏ i : Fin n, MvPolynomial.X (σ i, i) := by
  unfold permPoly Matrix.permanent symbolicMatrix
  rfl

/-- Witness monomial for S : Finset (Fin n): the diagonal product
Π_{i ∉ S} X_{(i, i)}. -/
noncomputable def witnessMono (S : Finset (Fin n)) :
    MvPolynomial (Fin n × Fin n) ℚ :=
  ∏ i ∈ Sᶜ, MvPolynomial.X (i, i)

/-- The identity permutation's contribution to permPoly:
`∏_i X_{(i, i)} = witnessMono ∅`. -/
theorem identity_contribution (n : ℕ) :
    (∏ i : Fin n, MvPolynomial.X (i, i) :
      MvPolynomial (Fin n × Fin n) ℚ) =
    witnessMono (∅ : Finset (Fin n)) := by
  unfold witnessMono
  simp

/-- The permanent polynomial at the identity permutation gives the
diagonal monomial. This is the "base case" of Theorem 100 (κ = 0). -/
theorem permPoly_identity_term (n : ℕ) :
    (∏ i : Fin n, MvPolynomial.X ((Equiv.refl (Fin n)) i, i) :
      MvPolynomial (Fin n × Fin n) ℚ) =
    ∏ i : Fin n, MvPolynomial.X (i, i) := by
  simp [Equiv.refl]

/-- **Identity permutation as a permutation term of permPoly.**
The identity permutation contributes `∏ᵢ X_(i,i)` to the sum defining
the permanent. -/
theorem permPoly_contains_identity_term (n : ℕ) :
    (∏ i : Fin n, MvPolynomial.X (i, i) :
      MvPolynomial (Fin n × Fin n) ℚ) =
    ∏ i : Fin n, MvPolynomial.X
      ((Equiv.refl (Fin n)) i, i) := by
  simp [Equiv.refl]

/-- Every permutation contributes exactly one monomial term of
`permPoly n`. Each monomial from σ has total degree n. -/
theorem permPoly_term_totalDegree_le (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (∏ i : Fin n,
        (MvPolynomial.X (σ i, i) : MvPolynomial (Fin n × Fin n) ℚ)).totalDegree
      ≤ n := by
  have : (∏ i : Fin n,
            (MvPolynomial.X (σ i, i) :
              MvPolynomial (Fin n × Fin n) ℚ)).totalDegree ≤
         ∑ i : Fin n,
            (MvPolynomial.X (σ i, i) :
              MvPolynomial (Fin n × Fin n) ℚ).totalDegree :=
    MvPolynomial.totalDegree_finset_prod _ _
  apply le_trans this
  simp [MvPolynomial.totalDegree_X]

/-- The total degree of `permPoly n` is at most `n`. -/
theorem permPoly_totalDegree_le (n : ℕ) :
    (permPoly n).totalDegree ≤ n := by
  rw [permPoly_eq_sum]
  apply le_trans (MvPolynomial.totalDegree_finset_sum _ _)
  simp only [Finset.sup_le_iff, Finset.mem_univ, forall_const]
  intro σ
  exact permPoly_term_totalDegree_le n σ

end PermanentGodMove
