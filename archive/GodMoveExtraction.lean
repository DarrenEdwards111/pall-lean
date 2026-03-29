import PallLean.SPDPDefs
import PallLean.GodMoveMonotonicity
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# GodMoveExtraction

Paper-faithful scaffold for the extraction theorem / God-Move.

This file packages the extraction route the paper actually uses:

1. A semantic extraction map from the compiled polynomial to the embedded NP hard object.
2. Rank monotonicity of the extraction map via projection / restriction / rename.
3. The resulting inequality needed on the separation path.

It is intentionally isolated from the current `main` proof route so it can be
completed independently and then wired into the active theorem chain.
-/

namespace GodMoveExtraction

open SPDP
open MvPolynomial
open GodMoveMonotonicity

variable {F : Type*} [Field F]

/-- Data of a paper-faithful God-Move extraction instance. -/
structure GodMoveData (n m : ℕ) where
  compiledPart : BlockPartition n
  hardPart : BlockPartition m
  κ : ℕ
  ℓ : ℕ
  proj : MvPolynomial (Fin n) F →ₐ[F] MvPolynomial (Fin m) F
  compiledPoly : MvPolynomial (Fin n) F
  hardPoly : MvPolynomial (Fin m) F
  semantic : proj compiledPoly = hardPoly

variable {n m : ℕ}

/--
The extracted hard object has rank at most the compiled polynomial.

This is the usable God-Move inequality on the active separation path.
-/
theorem godMove_extraction_rank_monotone
    (D : GodMoveData (F := F) n m) :
    blockedSpdpRank D.hardPart D.κ D.ℓ D.hardPoly ≤
      blockedSpdpRank D.compiledPart D.κ D.ℓ D.compiledPoly := by
  simpa [D.semantic] using
    (blockedSpdpRank_projection_le
      (F := F)
      (Bsrc := D.compiledPart)
      (Btgt := D.hardPart)
      (κ := D.κ)
      (ℓ := D.ℓ)
      (proj := D.proj)
      (p := D.compiledPoly))

/--
A version specialized to the common same-space situation where the hard object
has already been renamed into the compiled variable space.
-/
structure SameSpaceGodMoveData (n : ℕ) where
  part : BlockPartition n
  κ : ℕ
  ℓ : ℕ
  restrict : MvPolynomial (Fin n) F →ₐ[F] MvPolynomial (Fin n) F
  compiledPoly : MvPolynomial (Fin n) F
  hardPoly : MvPolynomial (Fin n) F
  semantic : restrict compiledPoly = hardPoly

/-- Same-space God-Move inequality. -/
theorem godMove_extraction_rank_monotone_sameSpace
    (D : SameSpaceGodMoveData (F := F) n) :
    blockedSpdpRank D.part D.κ D.ℓ D.hardPoly ≤
      blockedSpdpRank D.part D.κ D.ℓ D.compiledPoly := by
  simpa [D.semantic] using
    (blockedSpdpRank_restriction_le
      (F := F)
      (B := D.part)
      (κ := D.κ)
      (ℓ := D.ℓ)
      (restrict := D.restrict)
      (p := D.compiledPoly))

end GodMoveExtraction
