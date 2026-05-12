import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.LPS.CompleteGraphAdj
import PallLean.Paper93.DeepMath.LPS.KnLaplacianConstKernel
import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# All-ones vector is an eigenvector of `compiledGadget α n` with eigenvalue `α`

We prove that the all-ones vector `v = (1, …, 1) : Fin n → ℝ` is an
eigenvector of the compiled gadget matrix `compiledGadget α n` with
eigenvalue `α`. Mathematically:

    `(α • I + L_{K_n}) · 1 = α • 1 + L_{K_n} · 1 = α • 1 + 0 = α • 1`,

where the kernel containment `L_{K_n} · 1 = 0` is the standard fact that
the all-ones vector lies in the kernel of any graph Laplacian (here the
complete-graph Laplacian on `Fin n`).

The proof is a direct splitting via `Matrix.add_mulVec`, evaluating the
identity contribution `(α • I) · 1 = α • 1` pointwise, and citing the
existing lemma `completeAdj_laplacian_ones` for `L · 1 = 0`.

A nonemptiness corollary `exists_eigenvector_alpha` is also derived,
producing a nonzero eigenvector for `α` at any `n ≥ 1`.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.LPS
open PallLean.Paper93.DeepMath.GraphSpectral

/-- **Eigenvector relation for the compiled gadget.**

The all-ones vector `(fun _ => 1)` is an eigenvector of
`compiledGadget α n = α • I + L_{K_n}` with eigenvalue `α`. The
Laplacian contribution vanishes because the all-ones vector lies in the
kernel of every graph Laplacian (here `completeAdj_laplacian_ones`),
leaving only the identity contribution `α • 1`.

Proof outline:
1. Split `(α • I + L) · v` via `Matrix.add_mulVec`.
2. Evaluate `(α • I) · 1` pointwise: `(α • I).mulVec 1 i = α`.
3. Apply `completeAdj_laplacian_ones` to discharge `L · 1 = 0`.
4. Combine: `α + 0 = α`.
-/
theorem compiledGadget_mulVec_one (α : ℝ) (n : ℕ) :
    (compiledGadget α n).mulVec (fun _ => (1 : ℝ)) = (fun _ => α) := by
  funext i
  -- Unfold `compiledGadget` to `α • I + L_{K_n}`.
  unfold compiledGadget
  -- Split the `mulVec` over the sum.
  rw [Matrix.add_mulVec]
  -- The Laplacian piece is zero on the all-ones vector.
  have h_lap : (laplacian (completeAdj n)).mulVec (fun _ : Fin n => (1 : ℝ))
                  = (0 : Fin n → ℝ) :=
    completeAdj_laplacian_ones n
  -- Evaluate pointwise at `i`.
  show ((α • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec (fun _ => (1 : ℝ))) i
        + ((laplacian (completeAdj n)).mulVec (fun _ => (1 : ℝ))) i
      = α
  rw [h_lap]
  -- Now: `((α • I).mulVec 1) i + 0 i = α`.
  show ((α • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec (fun _ => (1 : ℝ))) i
        + (0 : Fin n → ℝ) i
      = α
  -- The right-hand side is `0` by `Pi.zero_apply`, so the goal collapses
  -- to `((α • I).mulVec 1) i = α`.
  rw [Pi.zero_apply, add_zero]
  -- Compute `(α • I).mulVec 1`: pull the scalar out, then apply `1.mulVec 1 = 1`.
  rw [Matrix.smul_mulVec]
  -- Goal: `(α • ((1 : Matrix _ _ ℝ).mulVec (fun _ => 1))) i = α`.
  show (α • ((1 : Matrix (Fin n) (Fin n) ℝ).mulVec (fun _ => (1 : ℝ)))) i = α
  rw [Matrix.one_mulVec]
  -- Goal: `(α • (fun _ => (1 : ℝ))) i = α`.
  show α • ((fun _ : Fin n => (1 : ℝ)) i) = α
  -- Reduces to `α * 1 = α`.
  simp

/-- **Existence of a nonzero eigenvector with eigenvalue `α`.**

For any `n ≥ 1`, the all-ones vector `(fun _ => 1) : Fin n → ℝ` is a
nonzero eigenvector of `compiledGadget α n` with eigenvalue `α`. This
packages `compiledGadget_mulVec_one` together with the nonvanishing of
the all-ones vector at index `⟨0, hn⟩`. -/
theorem exists_eigenvector_alpha (α : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∃ v : Fin n → ℝ, v ≠ 0 ∧ (compiledGadget α n).mulVec v = α • v := by
  refine ⟨fun _ => (1 : ℝ), ?_, ?_⟩
  · -- The all-ones vector is not the zero function: evaluating at `⟨0, hn⟩`
    -- gives `1 ≠ 0`.
    intro h
    have hzero : (fun _ : Fin n => (1 : ℝ)) ⟨0, hn⟩
                  = (0 : Fin n → ℝ) ⟨0, hn⟩ := congrFun h ⟨0, hn⟩
    -- The left-hand side reduces to `1`, the right-hand side to `0`.
    have h1 : (1 : ℝ) = 0 := hzero
    exact one_ne_zero h1
  · -- Apply the eigenvector relation and rewrite `α • (fun _ => 1) = (fun _ => α)`.
    have heig : (compiledGadget α n).mulVec (fun _ => (1 : ℝ)) = (fun _ => α) :=
      compiledGadget_mulVec_one α n
    rw [heig]
    -- Goal: `(fun _ => α) = α • (fun _ => 1)`.
    funext i
    show α = (α • (fun _ : Fin n => (1 : ℝ))) i
    show α = α • ((fun _ : Fin n => (1 : ℝ)) i)
    simp

end PallLean.Paper93.DeepMath.PathB
