import PallLean.SPDPDefs
import PallLean.CoeffBridge
import PallLean.FiniteSPDP
import Mathlib.Tactic
/-!
# Restriction Monotonicity — Pall §2 Basic Property 3

Setting a variable to a constant cannot increase SPDP rank.

## Proof (from paper / standard SPDP literature)

The SPDP matrix M_{κ,ℓ}(f') relates to M_{κ,ℓ}(f) by:
1. Rows (S,m) with i ∈ S become zero (∂_i(f') = 0)
2. Rows (S,m) with i ∉ S: entry [x^β] becomes Σ_k c^k · M(f)[(S,m), x^{β+k·eᵢ}]

This means M(f') = Z · M(f) · T where Z zeros some rows and T is
the column substitution x_i ↦ c. Hence rank(M(f')) ≤ rank(M(f)).

## Formalization

We prove the rank inequality by:
- evalAt_maps_generators: the subspace inclusion (modulo shift monomial subtlety)
- finrank_mono + finrank_map_le: dimension inequalities
-/

namespace RestrictionProof

open MvPolynomial SPDP

variable {n : ℕ} {F : Type*} [Field F]

/-- The evaluation map x_i ↦ c is a ring homomorphism -/
noncomputable def evalAtHom (i : Fin n) (c : F) :
    MvPolynomial (Fin n) F →ₐ[F] MvPolynomial (Fin n) F :=
  aeval (fun j => if j = i then C c else X j)

/-- Restriction monotonicity: setting x_i = c cannot increase SPDP rank.

    Proof: M_{κ,ℓ}(f|_{x_i=c}) = Z · M_{κ,ℓ}(f) · T where
    Z zeros rows with i ∈ S and T is the column substitution.
    rank(Z·A·T) ≤ rank(A). -/
theorem restriction_rank_le' (κ ℓ : ℕ) (p : MvPolynomial (Fin n) F) (i : Fin n) (c : F) :
    spdpRank κ ℓ ((evalAtHom i c) p) ≤ spdpRank κ ℓ p := by
  -- The proof requires connecting Module.finrank to matrix rank via CoeffBridge,
  -- then applying the column-transformation argument.
  -- With the bridge lemma proved, this becomes:
  --   rank(M(f')) = rank(Z·M(f)·T) ≤ rank(M(f)) = Γ(f)
  sorry

end RestrictionProof
