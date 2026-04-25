import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetMatrixIdentity
import PallLean.Paper93.DeepMath.PathB.Positroid.CompiledGadgetRankSpecific
import PallLean.Paper93.DeepMath.PathB.CompiledGadgetRankPos
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetRankLeN
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Rank-one update structure of the compiled gadget

We package the structural identity

  `compiledGadget α n = (α + n) • I_n − J_n`

(where `J_n = Matrix.vecMulVec 1 1` is the all-ones rank-1 outer product
`1 · 1ᵀ`) as a *rank-one update* statement: the compiled gadget is the
scalar matrix `(α + n) • I_n` minus a rank ≤ 1 perturbation.

This is the structural input to the spectral / matrix-determinant
lemma path used in the Route C ⇒ Route A bridge for the truncated
NS / gadget construction, where the closed-form determinant
`det = α (α + n)^{n-1}` is read off from a rank-one update.

The three lemmas in this file are:

* `compiledGadget_eq_smul_one_sub_outer` — the matrix identity
  `compiledGadget α n = (α + n) • I_n − J_n`.

* `compiledGadget_rank_at_least_n_minus_one` — for `α > 0`, `n ≥ 1`,
  the rank of the compiled gadget is at least `n - 1`, even though the
  all-ones direction `1 ∈ ker((α+n) • I − J)` could have absorbed
  one rank.

* `compiledGadget_rank_eq_smul_id_rank` — for `α > 0`, `n ≥ 1`,
  the rank of `compiledGadget α n` equals the rank of
  `(α + n) • I_n` (both are full rank `n`). In particular the column
  spaces, having the same finite rank in a finite-dimensional space,
  coincide as `⊤`.

The first lemma is a direct re-export of the matrix identity proved
in `CompiledGadgetMatrixIdentity`. The second is an immediate
consequence of `compiledGadget_rank_full`. The third also follows
from `compiledGadget_rank_full` together with `Matrix.rank_one`.
-/

namespace PallLean.Paper93.DeepMath.PathB.Positroid

open PallLean.Paper93.DeepMath.PathB
open PallLean.Paper93.DeepMath.GadgetRank
open Matrix

/-- **Rank-one update structural identity for the compiled gadget.**

The compiled gadget decomposes as the scalar matrix `(α + n) • I_n`
minus the all-ones rank-1 outer product
`J_n = Matrix.vecMulVec 1 1 = 1 · 1ᵀ`:

  `compiledGadget α n = (α + n) • I_n − J_n`.

This is just `compiledGadget_matrix_identity` re-exported for the
spectral / matrix-determinant lemma route. -/
theorem compiledGadget_eq_smul_one_sub_outer (α : ℝ) (n : ℕ) :
    compiledGadget α n
      = (α + (n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ)
          - Matrix.vecMulVec (Function.const (Fin n) (1 : ℝ))
              (Function.const (Fin n) (1 : ℝ)) :=
  compiledGadget_matrix_identity α n

/-- **Rank lower bound for the compiled gadget.**

For `α > 0` and `n ≥ 1`, the rank of the compiled gadget is at least
`n - 1`. Heuristically: even though the all-ones direction
`1 ∈ ℝⁿ` could in principle be absorbed by the rank-1 perturbation
`J_n = 1 · 1ᵀ`, the orthogonal complement of `1` (of dimension `n - 1`)
remains in the image of `(α + n) • I_n`, contributing `n - 1` ranks.

In fact, under `α > 0`, the compiled gadget is positive definite
(`compiledGadget_posDef`) and hence of full rank `n` (which is
trivially `≥ n - 1`). We give the proof via this stronger fact. -/
theorem compiledGadget_rank_at_least_n_minus_one
    (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 1 ≤ n) :
    (compiledGadget α n).rank ≥ n - 1 := by
  -- Full rank under positivity.
  have hfull : (compiledGadget α n).rank = n :=
    compiledGadget_rank_full α n hα hn
  -- `n ≥ n - 1` for natural numbers.
  have hsub : n - 1 ≤ n := Nat.sub_le n 1
  -- Combine.
  rw [ge_iff_le, hfull]
  exact hsub

/-- **Rank equality with the scalar block of the rank-one update.**

For `α > 0` and `n ≥ 1`, the compiled gadget has the same rank as the
scalar matrix `(α + n) • I_n` that appears in the rank-one update
`compiledGadget α n = (α + n) • I_n − J_n`. Indeed both ranks equal
`n`:

* `compiledGadget α n` has rank `n` by `compiledGadget_rank_full`
  (positive definiteness, hence invertibility).
* `(α + n) • I_n = (1 : Matrix (Fin n) (Fin n) ℝ)` (after renormalisation)
  has rank `n` as soon as `α + n ≠ 0`, since for `α > 0` and `n ≥ 1`
  we have `α + n > 0`, so `(α + n) • I_n` is invertible.

In a finite-dimensional space `ℝⁿ`, two square matrices of equal full
rank `n` necessarily have column space equal to all of `ℝⁿ`; hence
they share their column space (`= ⊤`). This is the rank-one-update
column-space stability statement on the `α > 0` branch. -/
theorem compiledGadget_rank_eq_smul_id_rank
    (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 1 ≤ n) :
    (compiledGadget α n).rank
      = ((α + (n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ)).rank := by
  -- LHS: full rank by the positive-definite argument.
  have hcg : (compiledGadget α n).rank = n :=
    compiledGadget_rank_full α n hα hn
  -- RHS: `(α + n) • I_n` is invertible for `α > 0`, `n ≥ 1`, hence has
  -- rank `n`.
  -- We use `IsUnit ((α + n) • I)` ⇒ rank = card.
  have hαn_pos : 0 < α + (n : ℝ) := by
    have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    linarith
  have hαn_ne : α + (n : ℝ) ≠ 0 := ne_of_gt hαn_pos
  -- Construct the inverse `(α + n)⁻¹ • I` and show this matrix is a unit.
  have hisUnit :
      IsUnit ((α + (n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    -- Equivalent to `(α + n) • 1 = ((α + n) : ℝ) • 1` smul-of-identity
    -- being a unit. Build the inverse directly.
    refine ⟨⟨(α + (n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ),
              (α + (n : ℝ))⁻¹ • (1 : Matrix (Fin n) (Fin n) ℝ),
              ?_, ?_⟩, rfl⟩
    · -- Forward: `((α+n) • 1) * ((α+n)⁻¹ • 1) = 1`.
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
          mul_inv_cancel₀ hαn_ne, one_smul]
    · -- Backward: `((α+n)⁻¹ • 1) * ((α+n) • 1) = 1`.
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
          inv_mul_cancel₀ hαn_ne, one_smul]
  have hsi : ((α + (n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ)).rank = n := by
    have := Matrix.rank_of_isUnit
              ((α + (n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ)) hisUnit
    simpa [Fintype.card_fin] using this
  -- Combine the two equalities.
  rw [hcg, hsi]

end PallLean.Paper93.DeepMath.PathB.Positroid
