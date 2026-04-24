/-
  PallLean/Paper93/Substantive/ConcretePiStar.lean

  W4 — Concrete non-trivial Π⋆ as an explicit projection onto the span
  of the constant polynomial `1`.  This realises a rank-1 idempotent
  `ℚ`-linear endomorphism of `MvPolynomial (Fin N) ℚ` whose range is
  the ℚ-span of `{1}` and whose action is `p ↦ constantCoeff p • 1`.
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Span.Basic

namespace PallLean.Paper93.Substantive

open MvPolynomial

/-- Π⋆: project to the constant polynomial span `{1}`.

    This is a rank-1 ℚ-linear projection: it sends a multivariate
    polynomial `p` over `ℚ` to `constantCoeff p • 1`.  Its range is the
    ℚ-span of `1` and it is idempotent. -/
noncomputable def piStarConcrete (N : ℕ) :
    MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ where
  toFun p := (constantCoeff p) • (1 : MvPolynomial (Fin N) ℚ)
  map_add' p q := by
    simp [map_add, add_smul]
  map_smul' r p := by
    simp [smul_eq_mul, mul_smul]

/-- `Π⋆` is idempotent: applying it twice equals applying it once.

    The constant coefficient of `c • 1` is `c`, so the second
    application returns `c • 1` unchanged. -/
theorem piStarConcrete_idempotent (N : ℕ) :
    (piStarConcrete N).comp (piStarConcrete N) = piStarConcrete N := by
  refine LinearMap.ext (fun p => ?_)
  -- Unfold the definition on both sides.
  show constantCoeff ((constantCoeff p) • (1 : MvPolynomial (Fin N) ℚ)) •
        (1 : MvPolynomial (Fin N) ℚ) =
      (constantCoeff p) • (1 : MvPolynomial (Fin N) ℚ)
  -- `constantCoeff` commutes with scalar multiplication, and
  -- `constantCoeff 1 = 1`.
  rw [MvPolynomial.constantCoeff_smul, map_one, smul_eq_mul, mul_one]

/-- The range of `Π⋆` is the ℚ-linear span of the constant polynomial
    `1`.  We prove this by bidirectional inclusion.

    - Any element in `range Π⋆` has the form `constantCoeff p • 1`,
      which is a scalar multiple of `1`, hence in `span {1}`.
    - Any element `c • 1` of `span {1}` is the image of the constant
      polynomial `C c` under `Π⋆`, since `constantCoeff (C c) = c`. -/
theorem piStarConcrete_range (N : ℕ) :
    LinearMap.range (piStarConcrete N) =
      Submodule.span ℚ {(1 : MvPolynomial (Fin N) ℚ)} := by
  apply le_antisymm
  · -- range ⊆ span {1}
    rintro q ⟨p, hp⟩
    -- `piStarConcrete N p = constantCoeff p • 1`.
    have hq : q = (constantCoeff p) • (1 : MvPolynomial (Fin N) ℚ) := by
      simpa [piStarConcrete] using hp.symm
    rw [hq]
    -- A scalar multiple of `1` lies in `span ℚ {1}`.
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_singleton _))
  · -- span {1} ⊆ range
    rw [Submodule.span_le]
    intro q hq
    -- `q ∈ {1}`, so `q = 1`.
    rcases hq with rfl
    -- Show `1 ∈ range (piStarConcrete N)`.  Witness: the constant
    -- polynomial `C 1 = 1`, whose constant coefficient is `1`.
    refine ⟨(C 1 : MvPolynomial (Fin N) ℚ), ?_⟩
    show (constantCoeff (C 1 : MvPolynomial (Fin N) ℚ)) •
          (1 : MvPolynomial (Fin N) ℚ) =
        (1 : MvPolynomial (Fin N) ℚ)
    rw [MvPolynomial.constantCoeff_C, one_smul]

end PallLean.Paper93.Substantive
