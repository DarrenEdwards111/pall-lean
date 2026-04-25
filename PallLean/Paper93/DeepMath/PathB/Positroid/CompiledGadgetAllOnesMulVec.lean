import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetEigenvalueAlpha
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetAllOnesEigenvector
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

/-!
# Matrix-level eigenvalue identity for the all-ones vector

We recast the entrywise eigenvector relation
`compiledGadget_mulVec_one : (compiledGadget α n).mulVec (fun _ => 1)
                                = fun _ => α`
into the clean matrix-level form
`(compiledGadget α n).mulVec (Function.const (Fin n) 1)
    = α • Function.const (Fin n) 1`,
where `α • _` is the natural `Pi`-scalar action on the function-valued
vector. This is the "Route~A"-shaped statement matching the standard
`A · v = α • v` template required by the spectral theorem.

We also produce the existence form
`∃ v : Fin n → ℝ, v ≠ 0 ∧ (compiledGadget α n).mulVec v = α • v`,
using `v = Function.const (Fin n) 1`. The nonvanishing of `v` requires
`n ≥ 1`; in the present formulation we discharge that case-split
internally via `Nat.eq_zero_or_pos`, so the statement is uniform in
`n : ℕ`. (When `n = 0`, the type `Fin 0 → ℝ` collapses to a singleton,
and the existence statement is *vacuously satisfied* by the unique
function `(default : Fin 0 → ℝ)` — but that function is the zero
function, so we cannot use it; instead, we package the nondegenerate
`n ≥ 1` case as the headline result and provide a uniform-in-`n`
fallback by requiring the hypothesis `1 ≤ n` in the existence theorem.)

The two main results are:

* `compiledGadget_mulVec_allOnes_smul`: the matrix-level identity
  `mulVec (Function.const _ 1) = α • Function.const _ 1`. This holds
  for all `n : ℕ` (vacuously when `n = 0`, since both sides are the
  unique function on `Fin 0`).

* `compiledGadget_allOnes_eigenvector_form`: the existence form with
  hypothesis `1 ≤ n`, providing a *nonzero* eigenvector with eigenvalue
  `α`. This is the form consumed by spectral-theorem-style packaging
  (e.g.\ "α is an eigenvalue of compiledGadget α n").
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.PathB

/-- **Matrix-level all-ones eigenvalue identity.**

For every `α : ℝ` and `n : ℕ`,
`(compiledGadget α n).mulVec (Function.const (Fin n) 1)
    = α • Function.const (Fin n) 1`.

This is the matrix-level (Route~A) form of the eigenvalue identity
proved entrywise in `compiledGadget_mulVec_one`. The right-hand side is
the `Pi`-scalar action `α • _` on the constant-`1` function, which
coincides pointwise with `Function.const (Fin n) α`.

Proof: rewrite the left-hand side via
`compiledGadget_allOnes_eigenvector` (which gives
`mulVec (Function.const _ 1) = fun _ => α`), then check pointwise that
`α • Function.const (Fin n) 1 = fun _ => α`. -/
theorem compiledGadget_mulVec_allOnes_smul (α : ℝ) (n : ℕ) :
    (compiledGadget α n).mulVec (Function.const (Fin n) (1 : ℝ))
      = α • Function.const (Fin n) (1 : ℝ) := by
  -- Step 1: the LHS equals `fun _ => α` by the entrywise eigenvector
  -- identity (in `Function.const` form).
  have hLHS :
      (compiledGadget α n).mulVec (Function.const (Fin n) (1 : ℝ))
        = fun _ : Fin n => α :=
    compiledGadget_allOnes_eigenvector α n
  -- Step 2: pointwise check that the RHS equals `fun _ => α`.
  have hRHS :
      (α • Function.const (Fin n) (1 : ℝ)) = fun _ : Fin n => α := by
    funext i
    -- `Pi.smul_apply` reduces `(α • f) i` to `α • f i`.
    show α • (Function.const (Fin n) (1 : ℝ) i) = α
    -- `Function.const _ 1 i = 1`, so this is `α • 1 = α`.
    show α • (1 : ℝ) = α
    -- Reduces to `α * 1 = α`.
    simp
  -- Combine: LHS = (fun _ => α) = RHS.
  rw [hLHS, hRHS]

/-- **Existence of a nonzero all-ones eigenvector (matrix-level form).**

For any `α : ℝ` and any `n ≥ 1`, the explicit all-ones vector
`Function.const (Fin n) 1 : Fin n → ℝ` is a *nonzero* eigenvector of
`compiledGadget α n` with eigenvalue `α`, in the matrix-level form
`mulVec v = α • v`. This is the existence form needed for the spectral
theorem.

The hypothesis `1 ≤ n` is necessary because, in `Fin 0 → ℝ`, every
function (including the all-ones constant) coincides with the zero
function; we cannot produce a nonzero vector in that degenerate case.

The witness vector is `v := Function.const (Fin n) 1`. Nonvanishing of
`v` follows from evaluating at `⟨0, hn⟩`, which gives `1 ≠ 0`. The
eigenvalue identity follows from
`compiledGadget_mulVec_allOnes_smul`. -/
theorem compiledGadget_allOnes_eigenvector_form
    (α : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∃ v : Fin n → ℝ, v ≠ 0 ∧ (compiledGadget α n).mulVec v = α • v := by
  refine ⟨Function.const (Fin n) (1 : ℝ), ?_, ?_⟩
  · -- Nonvanishing of `Function.const (Fin n) 1` at index `⟨0, hn⟩`:
    -- evaluating both sides of `Function.const _ 1 = 0` gives `1 = 0`.
    intro h
    have hzero :
        Function.const (Fin n) (1 : ℝ) ⟨0, hn⟩
          = (0 : Fin n → ℝ) ⟨0, hn⟩ := congrFun h ⟨0, hn⟩
    -- The LHS reduces to `1`, the RHS to `0`.
    have h1 : (1 : ℝ) = 0 := hzero
    exact one_ne_zero h1
  · -- Apply the matrix-level eigenvalue identity.
    exact compiledGadget_mulVec_allOnes_smul α n

end PallLean.Paper93.DeepMath.PathB.Positroid
