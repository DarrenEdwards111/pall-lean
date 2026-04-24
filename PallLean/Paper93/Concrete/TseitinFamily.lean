/-
  PallLean/Paper93/Concrete/TseitinFamily.lean

  Agent V9 — Paper §12 NP-side witness: concrete Tseitin polynomial
  family over the cycle graph.

  ## Scope

  This file records a concrete Tseitin-style polynomial witness and
  proves it is non-zero. Concretely, we define:

    * `tseitinPoly2`   — the paper §12 Tseitin parity witness for the
                         2-cycle: `X 0 + X 1 - 1` over `ℚ`, which
                         encodes `x₀ ≠ x₁` under Boolean assignments
                         with an odd charge at vertex `0`;
    * `tseitinFamily`  — the `n`-indexed family, which at `n = 2`
                         specialises to `tseitinPoly2` (renamed into
                         `MvPolynomial (Fin n) ℚ`) and is zero
                         otherwise.

  The core non-triviality fact `tseitinPoly2_ne_zero` is the basic
  NP-side witness used by paper §12: the Tseitin parity constraint on
  the even cycle is a non-trivial polynomial obstruction.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  ## Paper citations

    * §12 — Tseitin family as the NP-side witness on the cycle graph.
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Rename

namespace PallLean.Paper93.Concrete

open MvPolynomial

/-- **Tseitin parity constraint on the 2-cycle.**

On the cycle `C₂` with vertex set `{0,1}` and the single edge
`{0,1}` duplicated, the Tseitin parity encoding with odd charge at
vertex `0` reduces to the constraint `x₀ ≠ x₁`. As a polynomial
identity over `ℚ` with the Boolean embedding `{0,1} ↪ ℚ`, this is
captured by

```
  tseitinPoly2 = X 0 + X 1 - 1,
```

which vanishes exactly on the two valid assignments
`(x₀,x₁) = (0,1)` and `(1,0)`. This is the paper §12 NP-side
witness specialised to `n = 2`. -/
noncomputable def tseitinPoly2 : MvPolynomial (Fin 2) ℚ :=
  (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ)
    + (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ)
    - (1 : MvPolynomial (Fin 2) ℚ)

/-- **Non-triviality of the 2-cycle Tseitin witness.**

The polynomial `tseitinPoly2 = X 0 + X 1 - 1` is not the zero
polynomial in `MvPolynomial (Fin 2) ℚ`. We prove this by exhibiting
the coefficient at the monomial `X 0` (i.e. at the finsupp
`Finsupp.single 0 1`), which is `1` in `tseitinPoly2` and `0` in the
zero polynomial. -/
theorem tseitinPoly2_ne_zero : tseitinPoly2 ≠ 0 := by
  intro h
  -- The coefficient of `tseitinPoly2` at the monomial `X 0`
  -- (i.e. at `Finsupp.single 0 1`) is `1`; equating it to the
  -- coefficient of `0` at that monomial yields `1 = 0` in `ℚ`.
  have hcoeff :
      (MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 1) tseitinPoly2 : ℚ) =
        MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 1) (0 : MvPolynomial (Fin 2) ℚ) := by
    rw [h]
  -- Reduce the LHS coefficient of `X 0 + X 1 - 1` at `single 0 1`.
  -- We have:
  --   coeff (single 0 1) (X 0) = 1
  --   coeff (single 0 1) (X 1) = 0   (different support)
  --   coeff (single 0 1) (1)   = 0   (constant term)
  -- so the total is `1 + 0 - 0 = 1 ≠ 0 = coeff (single 0 1) 0`.
  have hX0 :
      (MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 1)
        (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) : ℚ) = 1 := by
    rw [MvPolynomial.coeff_X']
    simp
  have hX1 :
      (MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 1)
        (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℚ) : ℚ) = 0 := by
    rw [MvPolynomial.coeff_X']
    have hne : (Finsupp.single (1 : Fin 2) 1) ≠ (Finsupp.single (0 : Fin 2) 1) := by
      intro hEq
      have := congrArg (fun f => f (1 : Fin 2)) hEq
      simp at this
    simp [hne]
  have hOne :
      (MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 1)
        (1 : MvPolynomial (Fin 2) ℚ) : ℚ) = 0 := by
    rw [MvPolynomial.coeff_one]
    have : (Finsupp.single (0 : Fin 2) 1) ≠ (0 : Fin 2 →₀ ℕ) := by
      intro hEq
      have := congrArg (fun f => f (0 : Fin 2)) hEq
      simp at this
    simp [this.symm]
  have hZero :
      (MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 1) (0 : MvPolynomial (Fin 2) ℚ) : ℚ) = 0 := by
    simp
  -- Now compute the coefficient of `tseitinPoly2`:
  --   coeff (single 0 1) (X 0 + X 1 - 1)
  --     = coeff (single 0 1) (X 0) + coeff (single 0 1) (X 1)
  --       - coeff (single 0 1) 1
  --     = 1 + 0 - 0 = 1.
  have hLhs :
      (MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 1) tseitinPoly2 : ℚ) = 1 := by
    unfold tseitinPoly2
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_add]
    rw [hX0, hX1, hOne]
    ring
  -- Combine: `1 = 0` in `ℚ`, contradiction.
  rw [hLhs, hZero] at hcoeff
  exact (one_ne_zero : (1 : ℚ) ≠ 0) hcoeff

/-- **Tseitin family indexed by problem size `n`.**

At `n = 2`, this is `tseitinPoly2` renamed into `MvPolynomial (Fin n) ℚ`
via `Fin.castLE` (the canonical inclusion `Fin 2 ↪ Fin n` when
`2 ≤ n`, here trivially `2 ≤ 2`). For `n ≠ 2`, we return the zero
polynomial as a stub. -/
noncomputable def tseitinFamily (n : ℕ) : MvPolynomial (Fin n) ℚ :=
  if h : n = 2 then
    MvPolynomial.rename (Fin.castLE (by omega : 2 ≤ n)) tseitinPoly2
  else
    0

end PallLean.Paper93.Concrete
