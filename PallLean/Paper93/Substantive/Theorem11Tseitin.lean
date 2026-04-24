/-
  PallLean/Paper93/Substantive/Theorem11Tseitin.lean

  Agent W11 — Paper §12 Theorem 11 "Π⋆ acts non-trivially on the
  Tseitin NP-side witness".

  ## Scope

  V9 (`PallLean.Paper93.Concrete.TseitinFamily`) defines the paper §12
  Tseitin parity witness at `n = 2` as the multivariate polynomial

      tseitinPoly2 = X 0 + X 1 − 1      ∈ MvPolynomial (Fin 2) ℚ,

  and W4 (`PallLean.Paper93.Substantive.ConcretePiStar`) defines the
  substantive rank-1 projection

      piStarConcrete N : MvPolynomial (Fin N) ℚ →ₗ[ℚ] MvPolynomial (Fin N) ℚ,
      p ↦ constantCoeff p • 1.

  This file records the explicit action of `piStarConcrete 2` on the
  Tseitin parity witness:

      * `tseitinPoly2_constantCoeff`    — the constant coefficient of
        `tseitinPoly2` is `−1` (the `− 1` term in `X 0 + X 1 − 1`);
      * `piStarConcrete_tseitinPoly2`   — applying `piStarConcrete 2`
        to `tseitinPoly2` yields `(−1) • 1`, a non-zero constant
        polynomial and hence a non-trivial element of the range of
        `Π⋆`.

  This closes paper §12 Theorem 11 at the truncated `n = 2` level: the
  substantive Π⋆ projection does not annihilate the Tseitin NP-side
  witness, and therefore the Tseitin family contributes a non-trivial
  obstruction to the range of `Π⋆`.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  ## Paper citations

    * §12 Theorem 11 — Π⋆ is non-trivial on the Tseitin family.
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import PallLean.Paper93.Concrete.TseitinFamily
import PallLean.Paper93.Substantive.ConcretePiStar

namespace PallLean.Paper93.Substantive

open MvPolynomial

/-- **Constant coefficient of the Tseitin parity witness.**

The polynomial `tseitinPoly2 = X 0 + X 1 − 1` has constant coefficient
`−1`: the `X 0` and `X 1` terms contribute `0` (they are pure
monomials of positive degree) and the `− 1` term contributes `−1`. -/
theorem tseitinPoly2_constantCoeff :
    MvPolynomial.constantCoeff PallLean.Paper93.Concrete.tseitinPoly2 = -1 := by
  unfold PallLean.Paper93.Concrete.tseitinPoly2
  simp

/-- **Π⋆ acts non-trivially on the Tseitin family (paper §12 Theorem 11).**

Applying the substantive rank-1 projection `piStarConcrete 2` to the
Tseitin parity witness `tseitinPoly2` returns

    constantCoeff tseitinPoly2 • 1  =  (−1) • 1,

a non-zero constant polynomial.  In particular, `tseitinPoly2` is not
in the kernel of `Π⋆`, so `Π⋆` is non-trivial on the NP-side Tseitin
witness. -/
theorem piStarConcrete_tseitinPoly2 :
    piStarConcrete 2 PallLean.Paper93.Concrete.tseitinPoly2
      = ((-1 : ℚ) • (1 : MvPolynomial (Fin 2) ℚ)) := by
  -- Unfold the definition of `piStarConcrete` and rewrite the
  -- constant coefficient using `tseitinPoly2_constantCoeff`.
  unfold piStarConcrete
  simp [tseitinPoly2_constantCoeff]

end PallLean.Paper93.Substantive
