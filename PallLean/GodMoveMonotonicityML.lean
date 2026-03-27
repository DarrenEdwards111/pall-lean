import PallLean.MultilinearSPDP

/-!
# GodMoveMonotonicityML

Theorem-level monotonicity wrappers for the paper-faithful God-Move route,
reusing the multilinear SPDP infrastructure already proved in `MultilinearSPDP`.

These are the extraction primitives actually available on the current active
multilinear route:

* restriction/projection monotonicity via `restrictPoly`
* injective rename monotonicity
* partition coarsening monotonicity
-/

namespace GodMoveMonotonicityML

open SPDP
open MultilinearSPDP
open MvPolynomial

variable {F : Type*} [Field F] [Nontrivial F]

/-- Paper-faithful restriction / projection monotonicity in the multilinear setting. -/
theorem mlBlockedSpdpRank_projection_le
    {n m : ℕ}
    (f : Fin n → Fin m)
    (hf : Function.Injective f)
    (B : BlockPartition m)
    (κ ℓ : ℕ)
    (p : MvPolynomial (Fin m) F) :
    mlBlockedSpdpRank (pullbackPartition B f) κ ℓ (restrictPoly F f hf p)
      ≤ mlBlockedSpdpRank B κ ℓ p :=
  restriction_rank_monotone F f hf B κ ℓ p

/-- Injective rename monotonicity in the multilinear setting. -/
theorem mlBlockedSpdpRank_rename_le'
    {n m : ℕ}
    (f : Fin n → Fin m)
    (hf : Function.Injective f)
    (B : BlockPartition m)
    (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) F) :
    mlBlockedSpdpRank B κ ℓ (MvPolynomial.rename f p)
      ≤ mlBlockedSpdpRank (pullbackPartition B f) κ ℓ p :=
  MultilinearSPDP.mlBlockedSpdpRank_rename_le f hf B κ ℓ p

/-- Coarsening a partition cannot increase multilinear blocked SPDP rank. -/
theorem mlBlockedSpdpRank_coarsen'
    {n : ℕ}
    (B₁ B₂ : BlockPartition n)
    (κ ℓ : ℕ)
    (p : MvPolynomial (Fin n) F)
    (hrefine : ∀ i j : Fin n, B₁.assign i = B₁.assign j → B₂.assign i = B₂.assign j) :
    mlBlockedSpdpRank B₂ κ ℓ p ≤ mlBlockedSpdpRank B₁ κ ℓ p :=
  MultilinearSPDP.mlBlockedSpdpRank_coarsen F B₁ B₂ κ ℓ p hrefine

end GodMoveMonotonicityML
