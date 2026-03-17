/-
  Permanent.lean — The Permanent Polynomial (NP-side hard family)

  The permanent of an n×n matrix is the canonical VNP-complete polynomial.
  Paper Theorem 94: Γ_{κ,ℓ}(perm_n) is exponential.

  perm_n(x₁₁, ..., x_nn) = ∑_{σ ∈ S_n} ∏_{i=1}^{n} x_{i,σ(i)}

  This polynomial has n² variables and degree n. Its SPDP rank is
  exponential (≥ n! or ≥ 2^{n/4}), providing the NP-side lower bound.
-/
import Mathlib.Tactic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.RingTheory.MvPolynomial.Basic

namespace Permanent

open MvPolynomial Finset

/-- Matrix entry variable: (i, j) for row i, column j. -/
abbrev MatVar (m : ℕ) := Fin m × Fin m

/-- The permanent polynomial on m×m matrices over a commutative ring.
    perm_m = ∑_{σ ∈ S_m} ∏_{i} X_{(i, σ(i))} -/
noncomputable def permPoly (m : ℕ) (R : Type*) [CommRing R] :
    MvPolynomial (MatVar m) R :=
  ∑ σ : Equiv.Perm (Fin m), ∏ i : Fin m, X (i, σ i)

/-- The permanent as a Boolean decision problem:
    Given an n×n 0/1 matrix A and a target value t,
    does perm(A) = t?

    This is in NP: the witness is the set of permutations
    contributing to the sum (or equivalently, a perfect matching
    decomposition). Verification is polynomial-time. -/
def permDecision (m : ℕ) : (Fin (m * m + m) → Bool) → Bool :=
  fun input =>
    -- First m² bits encode the matrix, last m bits encode target
    -- This is a placeholder; the actual encoding would parse input
    -- and check perm(A) = t
    false  -- placeholder

/-- The permanent family as a Boolean function family.
    For the separation, we need a specific Boolean encoding that
    captures the permanent's algebraic hardness. -/
def permFamily : (n : ℕ) → ((Fin n → Bool) → Bool) :=
  fun n => fun _ => false  -- placeholder; real encoding TBD

/-- Flat index bound for reindexing (i,j) → i*m+j. -/
private lemma flat_index_bound {m : ℕ} (i j : Fin m) :
    i.val * m + j.val < m * m := by
  have hi := i.isLt; have hj := j.isLt
  calc i.val * m + j.val < i.val * m + m := by omega
    _ = (i.val + 1) * m := by ring
    _ ≤ m * m := by nlinarith

/-- Permanent polynomial reindexed to flat Fin(m*m) variable space.
    Maps (i,j) → i*m+j. -/
noncomputable def permPolyFlat (m : ℕ) : MvPolynomial (Fin (m * m)) ℚ :=
  MvPolynomial.rename (fun ij : MatVar m =>
    ⟨ij.1.val * m + ij.2.val, flat_index_bound ij.1 ij.2⟩) (permPoly m ℚ)

end Permanent
