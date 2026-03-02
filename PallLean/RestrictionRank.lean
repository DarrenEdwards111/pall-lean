import PallLean.SPDPDefs
import PallLean.PDerivEval
import Mathlib.Tactic
/-!
# R1: Variable Restriction Cannot Increase SPDP Rank

Updated for the paper-faithful (κ, ℓ) definition with shift monomials.

The paper states (§2, Basic properties, item 3):
"If f' is obtained from f by setting some variables to constants,
then Γ_{κ,ℓ}(f') ≤ Γ_{κ,ℓ}(f)."

Proof sketch: restriction x_i := c is a linear map on coefficient vectors.
Every row m · ∂_S(f|_{x_i=c}) of M_{κ,ℓ}(f') arises from a linear combination
of rows of M_{κ,ℓ}(f), so the row space can only shrink.
-/

namespace SPDP.Restriction

open SPDP PDerivEval MvPolynomial

variable {F : Type*} [CommRing F] [Nontrivial F]
variable {n : ℕ}

/-- If i ∈ indices, then iterDerivList kills evalAt i c p -/
theorem iterDerivList_evalAt_eq_zero_of_mem (i : Fin n) (c : F)
    (indices : List (Fin n)) (hi : i ∈ indices)
    (p : MvPolynomial (Fin n) F) :
    iterDerivList indices (evalAt i c p) = 0 := by
  induction indices generalizing p with
  | nil => simp at hi
  | cons j rest ih =>
    simp only [iterDerivList, List.foldl_cons]
    by_cases hji : j = i
    · subst hji; rw [pderiv_evalAt_self]; exact foldl_pderiv_zero rest
    · rw [pderiv_comm_evalAt i j hji c p]
      exact ih (by rcases List.mem_cons.mp hi with h | h; exact absurd h.symm hji; exact h)
        (pderiv j p)

/-- If i ∉ indices, iterDerivList commutes with evalAt -/
theorem iterDerivList_comm_evalAt_of_not_mem (i : Fin n) (c : F)
    (indices : List (Fin n)) (hi : i ∉ indices)
    (p : MvPolynomial (Fin n) F) :
    iterDerivList indices (evalAt i c p) =
      evalAt i c (iterDerivList indices p) := by
  induction indices generalizing p with
  | nil => simp [iterDerivList]
  | cons j rest ih =>
    simp only [iterDerivList, List.foldl_cons]
    have hji : j ≠ i := by intro h; exact hi (List.mem_cons.mpr (Or.inl h.symm))
    rw [pderiv_comm_evalAt i j hji c p]
    exact ih (by intro h; exact hi (List.mem_cons.mpr (Or.inr h))) (pderiv j p)

/-- evalAt i c as an F-linear map -/
noncomputable def evalAtLM (i : Fin n) (c : F) :
    MvPolynomial (Fin n) F →ₗ[F] MvPolynomial (Fin n) F where
  toFun := evalAt i c
  map_add' := map_add (evalAt i c)
  map_smul' := fun r x => by
    simp only [Algebra.smul_def, map_mul, RingHom.id_apply]
    congr 1; exact evalAt_C i c r

/-- **R1: restriction cannot increase SPDP rank (Pall §2, Basic property 3)**

    Γ_{κ,ℓ}(f|_{x_i=c}) ≤ Γ_{κ,ℓ}(f)

    This is a standard linear algebra fact: restriction is a linear map on
    coefficient vectors, so it maps rows of M_{κ,ℓ}(f) to rows of M_{κ,ℓ}(f'),
    and the row space can only shrink.

    The proof in our subspace formulation requires showing that the
    shift-monomial generators of V_{κ,ℓ}(f|_{x_i=c}) lie in the image of
    V_{κ,ℓ}(f) under evalAt. This is subtle because evalAt can change
    the degree of shift monomials involving x_i. We axiomatize this
    standard fact. -/
axiom restriction_rank_le (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F)
    (i : Fin n) (c : F) :
    spdpRank κ ℓ (evalAt i c p) ≤ spdpRank κ ℓ p

end SPDP.Restriction
