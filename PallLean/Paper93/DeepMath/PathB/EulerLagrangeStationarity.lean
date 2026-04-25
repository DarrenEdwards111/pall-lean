import PallLean.Paper93.DeepMath.LPS.CompleteGraphAdj
import PallLean.Paper93.DeepMath.LPS.CompleteGraphEig
import PallLean.Paper93.DeepMath.LPS.CompleteGraphSecondEig
import PallLean.Paper93.DeepMath.LPS.KnLaplacianEig
import PallLean.Paper93.DeepMath.LPS.KnLaplacianConstKernel
import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianDef
import PallLean.Paper93.DeepMath.PathB.KnLaplacianKernel
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
# First-variation identities for the N-Frame kinetic term

This file proves the *formal first-variation identities* for the kinetic
(α-)term of the N-Frame Lagrangian on the complete graph `K_n`.

## Scope

The Lagrangian variation `δ_Φ S_NF = 0` from the paper yields
`α · L_{G_n} Φ = (β/2) · χ · ∂sgn(Φ)`. The right-hand side involves
`sgn`, which is **not** differentiable, so we restrict to the kinetic
(α-)term and prove the algebraic identity for its gradient only.

We do **not** prove existence of stationary points or full
Euler–Lagrange optimality; we do **not** involve the parity (`sgn`) or
barrier (`logdet`) terms.

## Methodological choice

To avoid invoking `MvPolynomial.derivative` / `fderiv` machinery, we
define the partial derivative `kineticTerm_partialDeriv` *directly* as
the closed-form algebraic expression `2 α · ∑_{j ≠ i}(Φ_i − Φ_j)` that
ordinary calculus would yield for the polynomial
`α · ∑_{j ≠ i}(Φ_i − Φ_j)²`. The remaining identities (2)–(4) are then
proved as algebraic identities, *not* as differential calculus theorems.

## Main results

* `kineticTerm_partialDeriv`: closed-form definition `2 α · ∑_{j ≠ i}(Φ_i − Φ_j)`.
* `kineticTerm_partialDeriv_eq_two_alpha_diff`: the partial derivative equals
  `2 α · ((n − 1) · Φ_i − ∑_{j ≠ i} Φ_j)`.
* `kineticTerm_gradient_eq_laplacian_action`: the gradient of the kinetic
  term equals `2 α · (L Φ)_i` componentwise, where `L = laplacian (completeAdj n)`.
* `kineticTerm_grad_zero_iff_kernel`: stationarity in `Φ` is equivalent to
  `Φ ∈ ker L_{K_n}`.
* `constant_field_in_kernel`: every constant field lies in the kernel of
  `L_{K_n}`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GraphSpectral
open PallLean.Paper93.DeepMath.LPS
open Matrix

/-!
### (1) Partial derivative of the kinetic term, by closed form

The kinetic term on `K_n` is `α · ∑_{j ≠ i}(Φ_i − Φ_j)²`. Its formal
partial derivative `∂/∂Φ_i` (as a polynomial in `Φ`) is
`2 α · ∑_{j ≠ i}(Φ_i − Φ_j)`. We take this closed form as the
*definition* of `kineticTerm_partialDeriv`, avoiding `fderiv` machinery.
-/

/-- Partial derivative `∂/∂Φ_i` of the kinetic term
`α · ∑_{j ≠ i}(Φ_i − Φ_j)²` on the complete graph `K_n`, defined
directly as the closed-form algebraic expression
`2 α · ∑_{j ≠ i}(Φ_i − Φ_j)`.

We use the indicator-form `if i = j then 0 else (Φ i − Φ j)` to encode
the restriction `j ≠ i`, matching the conventions used elsewhere for
`completeAdj n`. -/
def kineticTerm_partialDeriv (α : ℝ) (n : ℕ) (i : Fin n) (Φ : Fin n → ℝ) : ℝ :=
  2 * α * ∑ j, (if i = j then (0 : ℝ) else (Φ i - Φ j))

/-- **Closed-form expansion of the kinetic-term partial derivative.**

The closed-form definition `2 α · ∑_{j ≠ i}(Φ_i − Φ_j)` rewrites to
`2 α · ((n − 1) · Φ_i − ∑_{j ≠ i} Φ_j)`, which is what classical
calculus on the polynomial `α · ∑_{j ≠ i}(Φ_i − Φ_j)²` would deliver
after expanding `(Φ_i − Φ_j) · 2`.

This is a purely algebraic identity over the reals. -/
theorem kineticTerm_partialDeriv_eq_two_alpha_diff (α : ℝ) (n : ℕ)
    (i : Fin n) (Φ : Fin n → ℝ) :
    kineticTerm_partialDeriv α n i Φ
      = 2 * α * (((n : ℝ) - 1) * Φ i
                  - ∑ j, (if i = j then (0 : ℝ) else Φ j)) := by
  -- Rewrite each summand `if i = j then 0 else (Φ i − Φ j)` as
  -- `(if i = j then 0 else Φ i) − (if i = j then 0 else Φ j)`.
  unfold kineticTerm_partialDeriv
  have hpt : ∀ j : Fin n,
      (if i = j then (0 : ℝ) else (Φ i - Φ j))
        = (if i = j then (0 : ℝ) else Φ i)
              - (if i = j then (0 : ℝ) else Φ j) := by
    intro j
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  -- Sum-of-difference becomes difference-of-sums.
  have hsum :
      (∑ j, (if i = j then (0 : ℝ) else (Φ i - Φ j)))
        = (∑ j, (if i = j then (0 : ℝ) else Φ i))
            - ∑ j, (if i = j then (0 : ℝ) else Φ j) := by
    calc  (∑ j, (if i = j then (0 : ℝ) else (Φ i - Φ j)))
        = ∑ j, ((if i = j then (0 : ℝ) else Φ i)
                  - (if i = j then (0 : ℝ) else Φ j)) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              exact hpt j
      _ = (∑ j, (if i = j then (0 : ℝ) else Φ i))
            - ∑ j, (if i = j then (0 : ℝ) else Φ j) := by
              rw [Finset.sum_sub_distrib]
  -- Evaluate `∑ j, (if i = j then 0 else Φ i) = (n − 1) · Φ i`.
  have hcoeff :
      (∑ j : Fin n, (if i = j then (0 : ℝ) else Φ i))
        = ((n : ℝ) - 1) * Φ i := by
    -- Rewrite `if i = j then 0 else Φ i = Φ i − (if i = j then Φ i else 0)`.
    have hcoeff_pt : ∀ j : Fin n,
        (if i = j then (0 : ℝ) else Φ i)
          = Φ i - (if i = j then Φ i else 0) := by
      intro j
      by_cases hij : i = j
      · simp [hij]
      · simp [hij]
    calc  (∑ j : Fin n, (if i = j then (0 : ℝ) else Φ i))
        = ∑ j : Fin n, (Φ i - (if i = j then Φ i else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro j _
              exact hcoeff_pt j
      _ = (∑ _j : Fin n, Φ i)
            - ∑ j : Fin n, (if i = j then Φ i else 0) := by
              rw [Finset.sum_sub_distrib]
      _ = (n : ℝ) * Φ i - Φ i := by
              have h_const :
                  (∑ _j : Fin n, Φ i) = (n : ℝ) * Φ i := by
                simp [Finset.sum_const, Finset.card_univ,
                      Fintype.card_fin, mul_comm]
              have h_delta :
                  (∑ j : Fin n, (if i = j then Φ i else 0)) = Φ i := by
                simp [Finset.sum_ite_eq, Finset.mem_univ]
              rw [h_const, h_delta]
      _ = ((n : ℝ) - 1) * Φ i := by ring
  rw [hsum, hcoeff]

/-!
### (2) Gradient equals Laplacian action

The Laplacian of the complete graph `K_n` acts on `Φ` as
`(L Φ)_i = (n − 1) · Φ_i − ∑_{j ≠ i} Φ_j`. Combining with
`kineticTerm_partialDeriv_eq_two_alpha_diff` we obtain the desired
identity `kineticTerm_partialDeriv α n i Φ = 2 α · (L Φ)_i`.
-/

/-- Helper: `(completeAdj n *ᵥ Φ) i = ∑ j, (if i = j then 0 else Φ j)`.

This unfolds `mulVec` against the complete-graph adjacency and rewrites
`(if i = j then 0 else 1) * Φ j` to `if i = j then 0 else Φ j`. -/
private theorem completeAdj_mulVec_eq_sum_offdiag
    (n : ℕ) (Φ : Fin n → ℝ) (i : Fin n) :
    (completeAdj n).mulVec Φ i
      = ∑ j, (if i = j then (0 : ℝ) else Φ j) := by
  -- Unfold `mulVec` and `completeAdj`.
  simp only [completeAdj, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl ?_
  intro j _
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

/-- **Gradient = Laplacian action (closed graph form).**

The closed-form partial derivative
`kineticTerm_partialDeriv α n i Φ` equals `2 α · (L Φ)_i`, where
`L = laplacian (completeAdj n)` is the Laplacian of `K_n`. This is the
algebraic content of the Euler–Lagrange identity
`α · L_{G_n} Φ` for the kinetic term. -/
theorem kineticTerm_gradient_eq_laplacian_action
    (α : ℝ) (n : ℕ) (Φ : Fin n → ℝ) (i : Fin n) :
    kineticTerm_partialDeriv α n i Φ
      = 2 * α * ((laplacian (completeAdj n)).mulVec Φ i) := by
  -- Expand the partial derivative via `kineticTerm_partialDeriv_eq_two_alpha_diff`.
  rw [kineticTerm_partialDeriv_eq_two_alpha_diff α n i Φ]
  -- Compute `(L Φ) i` directly.
  have hL :
      (laplacian (completeAdj n)).mulVec Φ i
        = ((n : ℝ) - 1) * Φ i
            - ∑ j, (if i = j then (0 : ℝ) else Φ j) := by
    -- Unfold `laplacian` and split the difference.
    unfold laplacian
    rw [Matrix.sub_mulVec, Pi.sub_apply]
    -- Diagonal part: `(D *ᵥ Φ) i = (rowSum (completeAdj n)) i · Φ i = (n − 1) · Φ i`.
    rw [Matrix.mulVec_diagonal]
    have hrow : rowSum (completeAdj n) i = (n : ℝ) - 1 := by
      unfold rowSum
      exact completeAdj_rowSum n i
    rw [hrow]
    -- Adjacency part rewrites via the helper.
    rw [completeAdj_mulVec_eq_sum_offdiag n Φ i]
  -- Substitute the Laplacian formula and conclude.
  rw [hL]

/-!
### (3) Stationarity ⟺ kernel of the Laplacian

Combining (2) with the assumption `α ≠ 0` we obtain the equivalence
between the gradient-zero condition and `Φ ∈ ker L_{K_n}`.
-/

/-- **Stationarity in `Φ` ⟺ `Φ ∈ ker L_{K_n}`.**

For `α ≠ 0`, every component of the kinetic-term gradient vanishes at
`Φ` iff `(L Φ) = 0`, where `L = laplacian (completeAdj n)`. This is the
algebraic Euler–Lagrange equation `α · L_{G_n} Φ = 0` for the kinetic
term restricted to the case `α ≠ 0`. -/
theorem kineticTerm_grad_zero_iff_kernel
    (α : ℝ) (n : ℕ) (hα : α ≠ 0) (Φ : Fin n → ℝ) :
    (∀ i, kineticTerm_partialDeriv α n i Φ = 0)
      ↔ (laplacian (completeAdj n)).mulVec Φ = 0 := by
  constructor
  · -- (→) Gradient zero everywhere implies `L Φ = 0`.
    intro hzero
    funext i
    -- Specialise `kineticTerm_gradient_eq_laplacian_action`.
    have h := kineticTerm_gradient_eq_laplacian_action α n Φ i
    -- Combine with `hzero i` to read `2 α · (L Φ) i = 0`.
    rw [hzero i] at h
    -- `h : 0 = 2 * α * (L Φ) i`. Solve for `(L Φ) i`.
    have h' : 2 * α * ((laplacian (completeAdj n)).mulVec Φ i) = 0 := h.symm
    have h2α : (2 * α) ≠ 0 := mul_ne_zero (by norm_num) hα
    have hLi : (laplacian (completeAdj n)).mulVec Φ i = 0 := by
      -- From `2 α · (L Φ) i = 0` and `2 α ≠ 0`, conclude `(L Φ) i = 0`.
      rcases mul_eq_zero.mp h' with h2αzero | hLizero
      · exact absurd h2αzero h2α
      · exact hLizero
    -- `(0 : Fin n → ℝ) i = 0`.
    show (laplacian (completeAdj n)).mulVec Φ i = (0 : Fin n → ℝ) i
    simpa using hLi
  · -- (←) `L Φ = 0` implies the gradient is zero everywhere.
    intro hLΦ i
    -- Specialise `kineticTerm_gradient_eq_laplacian_action`.
    have h := kineticTerm_gradient_eq_laplacian_action α n Φ i
    -- Read off `(L Φ) i = 0` from the assumption.
    have hLi : (laplacian (completeAdj n)).mulVec Φ i = 0 := by
      have := congrArg (fun f : Fin n → ℝ => f i) hLΦ
      simpa using this
    rw [h, hLi]
    ring

/-!
### (4) Constant fields are in the kernel of `L_{K_n}`

This is a direct re-export of `laplacian_completeAdj_mulVec_const` in
`KnLaplacianKernel.lean`, recorded under a name aligned with the
Euler–Lagrange first-variation discussion.
-/

/-- **Constant fields are in the kernel of `L_{K_n}`.**

For any real constant `c`, the constant vector `(fun _ => c)` lies in
the kernel of the Laplacian of the complete graph `K_n`. Combined with
`kineticTerm_grad_zero_iff_kernel`, this shows that constant fields
satisfy the kinetic-term Euler–Lagrange equation. -/
theorem constant_field_in_kernel (n : ℕ) (c : ℝ) :
    (laplacian (completeAdj n)).mulVec (fun _ : Fin n => c) = 0 := by
  -- Rewrite the right-hand side as the Pi-zero function.
  have h := laplacian_completeAdj_mulVec_const n c
  funext i
  have hi := congrArg (fun f : Fin n → ℝ => f i) h
  simpa using hi

end PallLean.Paper93.DeepMath.PathB
