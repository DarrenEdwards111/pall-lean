import PallLean.SPDPDefs
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# GodMoveMonotonicity

Paper-faithful monotonicity primitives for the God-Move / extraction route.

These are intentionally stated as standalone theorem hooks so the extraction layer
can be developed independently of the active OBDD/Tseitin route on `main`.

They mirror the paper's decomposition of the extraction map into rank-nonincreasing
operations: projection, restriction, and injective rename.
-/

namespace GodMoveMonotonicity

open SPDP
open MvPolynomial

variable {F : Type*} [Field F]

/-- A block-local projection/restriction map from a compiled variable space to a
smaller clause-sheet variable space. -/
variable {n m : ℕ}

/--
Paper-faithful monotonicity primitive:
block-local projection does not increase blocked SPDP rank.
-/
axiom blockedSpdpRank_projection_le
    (Bsrc : BlockPartition n)
    (Btgt : BlockPartition m)
    (κ ℓ : ℕ)
    (proj : MvPolynomial (Fin n) F →ₐ[F] MvPolynomial (Fin m) F)
    (p : MvPolynomial (Fin n) F) :
    blockedSpdpRank Btgt κ ℓ (proj p) ≤ blockedSpdpRank Bsrc κ ℓ p

/--
Paper-faithful monotonicity primitive:
block-local restriction/partial evaluation does not increase blocked SPDP rank.
-/
axiom blockedSpdpRank_restriction_le
    (B : BlockPartition n)
    (κ ℓ : ℕ)
    (restrict : MvPolynomial (Fin n) F →ₐ[F] MvPolynomial (Fin n) F)
    (p : MvPolynomial (Fin n) F) :
    blockedSpdpRank B κ ℓ (restrict p) ≤ blockedSpdpRank B κ ℓ p

/--
Paper-faithful monotonicity primitive:
injective rename preserves / does not increase blocked SPDP rank.
-/
axiom blockedSpdpRank_rename_le
    (Bsrc : BlockPartition n)
    (Btgt : BlockPartition m)
    (κ ℓ : ℕ)
    (ρ : Fin n → Fin m)
    (hρ : Function.Injective ρ)
    (p : MvPolynomial (Fin n) F) :
    blockedSpdpRank Btgt κ ℓ (MvPolynomial.rename ρ p) ≤ blockedSpdpRank Bsrc κ ℓ p

end GodMoveMonotonicity
