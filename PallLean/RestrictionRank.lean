import PallLean.SPDPRankDef
import PallLean.PDerivEval
import Mathlib.Tactic
/-!
# R1: Variable Restriction Cannot Increase SPDP Rank

Key insight: pderiv j commutes with evalAt i for j ≠ i (proved in PDerivEval).
For j = i, pderiv i kills the restricted variable, giving 0.
Either way, the SPDP generators of p|_{x_i=c} are images of generators of p.
-/

namespace SPDP.Restriction

open SPDP.Concrete PDerivEval MvPolynomial

variable {F : Type*} [CommRing F] [Nontrivial F]
variable {n : ℕ}

/-- evalAt as a linear map -/
noncomputable def evalLin (i : Fin n) (c : F) :
    MvPolynomial (Fin n) F →ₗ[F] MvPolynomial (Fin n) F where
  toFun := evalAt i c
  map_add' := map_add _
  map_smul' := fun r x => by
    simp only [RingHom.id_apply, Algebra.smul_def, map_mul, evalAt_C]

/-- iterDerivList using only indices ≠ i commutes with evalAt i -/
theorem iterDerivList_comm_evalAt_ne (i : Fin n) (c : F)
    (indices : List (Fin n)) (h_ne : ∀ j ∈ indices, j ≠ i)
    (p : MvPolynomial (Fin n) F) :
    iterDerivList indices (evalAt i c p) = evalAt i c (iterDerivList indices p) := by
  induction indices generalizing p with
  | nil => simp [iterDerivList]
  | cons j rest ih =>
    simp only [iterDerivList, List.foldl_cons]
    have hj : j ≠ i := h_ne j (List.mem_cons_self _ _)
    rw [pderiv_comm_evalAt i j hj c p]
    exact ih (fun k hk => h_ne k (List.mem_cons_of_mem _ hk)) _

/-- For a general index list (possibly containing i), the SPDP generator
    m · iterDerivList indices (evalAt i c p) is in the image of evalLin applied
    to some element of the original SPDP subspace.

    When the list contains i: pderiv i (evalAt i c p) = evalAt i c (pderiv i p)
    is NOT true in general. But pderiv i (C c · q) involves the chain rule
    and the contribution from the i-direction is zero after restriction.

    The correct approach: use that iterDerivList on (evalAt p) is a polynomial
    in the image of evalAt (because evalAt is surjective onto the subring of
    polynomials not involving x_i, and all pderiv outputs after evalAt are in
    that subring). -/

/-- **R1**: restriction_rank_le.
    Full proof requires showing the SPDP subspace of p|_{x_i=c} is contained in
    the image of the SPDP subspace of p under evalLin.
    The containment holds because each generator maps correctly, but the
    general case with i ∈ S needs careful tracking through the Leibniz rule. -/
theorem restriction_rank_le (κ : ℕ) (p : MvPolynomial (Fin n) F)
    (i : Fin n) (c : F) :
    spdpRankConcrete κ (evalAt i c p) ≤ spdpRankConcrete κ p := by
  -- Approach: the evalAt map sends the SPDP subspace of p into a subspace
  -- that contains the SPDP subspace of (evalAt p).
  -- This is because ∂_S(evalAt p) is in the image of evalAt for each S:
  -- - For indices j ≠ i in S: commutation gives evalAt(∂_j p)
  -- - For index i in S: ∂_i(evalAt p) = 0 (evalAt p doesn't depend on x_i)
  --   and 0 = evalAt(0) is in the image
  -- So each generator m · ∂_S(evalAt p) = evalAt(m') · evalAt(∂_S' p) for some S', m'
  -- This means the subspace is contained in the image, and image has dim ≤ original.
  sorry

end SPDP.Restriction
