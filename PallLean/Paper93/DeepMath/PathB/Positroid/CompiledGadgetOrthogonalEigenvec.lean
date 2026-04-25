import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.LPS.CompleteGraphAdj
import PallLean.Paper93.DeepMath.LPS.KnLaplacianEig
import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Sum-zero eigenvectors of the compiled gadget have eigenvalue `α + n`

We prove that any sum-zero vector `v : Fin n → ℝ` (i.e. one with
`∑ i, v i = 0`) is an eigenvector of the compiled gadget matrix
`compiledGadget α n` with eigenvalue `α + n`. Mathematically:

    `(α • I + L_{K_n}) · v = α • v + L_{K_n} · v = α • v + n • v
        = (α + n) • v`,

where the K_n-Laplacian eigenvalue identity `L_{K_n} · v = n • v` on the
sum-zero subspace is the existing lemma
`completeAdj_laplacian_sumZero_eigen` from `KnLaplacianEig.lean`.

This is the "orthogonal" companion of `compiledGadget_mulVec_one`
(eigenvalue `α` on the all-ones direction): together, the two cover the
spectral decomposition of `compiledGadget α n` as
`α` (multiplicity 1, on the all-ones line) and `α + n` (multiplicity
`n - 1`, on the sum-zero hyperplane).

The proof is a direct splitting via `Matrix.add_mulVec`, evaluating the
identity contribution `(α • I) · v = α • v` pointwise, and citing the
existing lemma `completeAdj_laplacian_sumZero_eigen` for `L · v = n • v`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.LPS
open PallLean.Paper93.DeepMath.GraphSpectral

/-- **Sum-zero eigenvector relation for the compiled gadget.**

Any sum-zero vector `v : Fin n → ℝ` (i.e. `∑ i, v i = 0`) is an
eigenvector of `compiledGadget α n = α • I + L_{K_n}` with eigenvalue
`α + n`. The Laplacian contribution evaluates to `n • v` on the
sum-zero subspace (via `completeAdj_laplacian_sumZero_eigen`),
combining with the identity contribution `α • v` to give `(α + n) • v`.

Proof outline:
1. Split `(α • I + L) · v` via `Matrix.add_mulVec`.
2. Evaluate `(α • I) · v` pointwise: `(α • I).mulVec v i = α * v i`.
3. Apply `completeAdj_laplacian_sumZero_eigen` to reduce
   `L · v = n • v`.
4. Combine pointwise: `α * v i + n * v i = (α + n) * v i`. -/
theorem compiledGadget_mulVec_sumZero (α : ℝ) (n : ℕ) (v : Fin n → ℝ)
    (hv : ∑ i, v i = 0) :
    (compiledGadget α n).mulVec v = (α + (n : ℝ)) • v := by
  funext i
  -- Unfold `compiledGadget` to `α • I + L_{K_n}`.
  unfold compiledGadget
  -- Split the `mulVec` over the sum.
  rw [Matrix.add_mulVec]
  -- The Laplacian piece on a sum-zero vector returns `n • v`.
  have h_lap : (laplacian (completeAdj n)).mulVec v = (n : ℝ) • v :=
    completeAdj_laplacian_sumZero_eigen n v hv
  -- Evaluate pointwise at `i`.
  show ((α • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec v) i
        + ((laplacian (completeAdj n)).mulVec v) i
      = ((α + (n : ℝ)) • v) i
  rw [h_lap]
  -- Compute the identity contribution: `(α • I).mulVec v = α • v`.
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  -- Goal: `(α • v) i + ((n : ℝ) • v) i = ((α + n) • v) i`.
  show (α • v) i + ((n : ℝ) • v) i = ((α + (n : ℝ)) • v) i
  -- Reduce all `Pi`-smuls to scalar multiplication.
  show α * v i + (n : ℝ) * v i = (α + (n : ℝ)) * v i
  ring

/-- **Existence of a nonzero sum-zero eigenvector with eigenvalue `α + n`.**

For any `n ≥ 2`, there exists a nonzero sum-zero vector `v : Fin n → ℝ`
which is an eigenvector of `compiledGadget α n` with eigenvalue
`α + n`. We exhibit `v = e_0 - e_1`, which has sum zero and is nonzero
at index `0`. -/
theorem exists_eigenvector_alpha_plus_n (α : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    ∃ v : Fin n → ℝ, v ≠ 0 ∧
      (compiledGadget α n).mulVec v = (α + (n : ℝ)) • v := by
  -- Indices `0` and `1`, both well-defined since `n ≥ 2`.
  have h0 : 0 < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn
  have h1 : 1 < n := lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hn
  let i0 : Fin n := ⟨0, h0⟩
  let i1 : Fin n := ⟨1, h1⟩
  -- The candidate vector: `v = e_{i0} - e_{i1}`, i.e.
  -- `v j = (if j = i0 then 1 else 0) - (if j = i1 then 1 else 0)`.
  refine
    ⟨fun j => (if j = i0 then (1 : ℝ) else 0) - (if j = i1 then (1 : ℝ) else 0),
      ?_, ?_⟩
  · -- Nonzero: at index `i0` the value is `1 - 0 = 1 ≠ 0`,
    -- since `i0 ≠ i1` (as `0 ≠ 1` in `Fin n`).
    intro hzero
    have hi0_ne_i1 : i0 ≠ i1 := by
      intro hij
      have : (0 : ℕ) = 1 := Fin.mk.inj_iff.mp hij
      exact (by decide : (0 : ℕ) ≠ 1) this
    have hat_i0 :
        (fun j : Fin n => (if j = i0 then (1 : ℝ) else 0)
                            - (if j = i1 then (1 : ℝ) else 0)) i0
          = (0 : Fin n → ℝ) i0 := congrFun hzero i0
    -- LHS reduces to `1 - 0 = 1`, RHS to `0`.
    have hlhs :
        (fun j : Fin n => (if j = i0 then (1 : ℝ) else 0)
                            - (if j = i1 then (1 : ℝ) else 0)) i0 = 1 := by
      show (if i0 = i0 then (1 : ℝ) else 0)
              - (if i0 = i1 then (1 : ℝ) else 0) = 1
      rw [if_pos rfl, if_neg hi0_ne_i1]; ring
    have : (1 : ℝ) = 0 := by
      rw [← hlhs]; exact hat_i0
    exact one_ne_zero this
  · -- Apply the sum-zero eigenvector relation. First check sum-zero.
    have hi0_ne_i1 : i0 ≠ i1 := by
      intro hij
      have : (0 : ℕ) = 1 := Fin.mk.inj_iff.mp hij
      exact (by decide : (0 : ℕ) ≠ 1) this
    have hsum :
        ∑ j : Fin n,
            ((if j = i0 then (1 : ℝ) else 0) - (if j = i1 then (1 : ℝ) else 0))
          = 0 := by
      rw [Finset.sum_sub_distrib]
      have h_i0 :
          (∑ j : Fin n, (if j = i0 then (1 : ℝ) else 0)) = 1 := by
        simp [Finset.sum_ite_eq', Finset.mem_univ]
      have h_i1 :
          (∑ j : Fin n, (if j = i1 then (1 : ℝ) else 0)) = 1 := by
        simp [Finset.sum_ite_eq', Finset.mem_univ]
      rw [h_i0, h_i1]; ring
    exact compiledGadget_mulVec_sumZero α n _ hsum

end PallLean.Paper93.DeepMath.PathB.Positroid
