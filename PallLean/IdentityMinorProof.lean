import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
/-!
# N3: Identity Minor Forces Rank Lower Bound — PROVED
-/

namespace IdentityMinorProof

open Matrix

set_option maxHeartbeats 400000

/-- If a matrix A : Matrix r c R has a submatrix equal to the identity
    of size m, then rank(A) ≥ m.

    rank_submatrix_le says: rank(A.submatrix f e) ≤ rank(A)
      where f : rows' → rows, e : cols' ≃ cols
    rank_one says: rank (1 : Matrix k k R) = Fintype.card k -/
theorem rank_ge_of_identity_minor
    {R : Type*} [CommRing R] [Nontrivial R]
    {r c : Type*} [Fintype r] [Fintype c] [DecidableEq r] [DecidableEq c]
    (m : ℕ)
    (A : Matrix r c R)
    -- f selects rows, e bijects cols
    (f : Fin m → r) (e : Fin m ≃ c)
    (h_id : A.submatrix f e = 1) :
    A.rank ≥ m := by
  have h1 : (A.submatrix f e).rank ≤ A.rank := rank_submatrix_le f e A
  rw [h_id, rank_one, Fintype.card_fin] at h1
  exact h1

end IdentityMinorProof
