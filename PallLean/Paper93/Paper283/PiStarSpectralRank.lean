/-
  PallLean/Paper93/Paper283/PiStarSpectralRank.lean

  Paper §28.3 — Rank-monotonicity (column-span containment) of the
  linear map `piStarFromMatrix P`, viewed as matrix-action on the
  Hilbert realisation of the state space.

  ## Scope (Z11)

  We expose two paper-faithful, kernel-only facts about the Π⋆
  packaging `piStarFromMatrix` introduced in
  `PiStarSpectral.lean`:

    * `piStarFromMatrix_range_le` — the range of the linear action
      of a projection matrix `P` on `Fin N → ℝ` is contained in the
      span of the column-vectors `P.mulVec (Pi.single i 1)`
      (i.e.\ the span of the columns of `P`). This is the
      ``range-is-column-span'' fact, specialised here to the
      mulVec action used by `piStarFromMatrix`.

    * `piStarFromMatrix_identity_range_top` — for the identity
      projection, the range is the whole ambient space `⊤`.

  Together, these two facts give the standard rank-monotonicity
  picture: the range of `Π⋆` sits inside the column-span of the
  projection matrix, and for the full-rank (identity) projection
  the range saturates the ambient space.

  ## Kernel-only

    * No `sorry`.
    * No bespoke axioms.
    * Verified by `lake build`.

  ## Paper citations

    * §28.3 p. 137–138 — dominant-eigenspace construction of Π⋆
      from the stationary A-matrix.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Pi
import PallLean.Paper93.Paper283.PiStarSpectral

namespace PallLean.Paper93.Paper283

open Matrix
open scoped BigOperators

/-- **Paper §28.3 p. 137–138 — Range-is-column-span containment.**

The range of the linear map `piStarFromMatrix P` on `Fin N → ℝ` is
contained in the `ℝ`-span of the vectors `P.mulVec (Pi.single i 1)`
(the columns of `P`, viewed as elements of `Fin N → ℝ`). This is
the standard ``range = column-span'' fact, and provides the
rank-monotonicity picture for Π⋆: `range(Π⋆ · x) ⊆ span(columns of P)`.
-/
theorem piStarFromMatrix_range_le {N : ℕ}
    (P : Matrix (Fin N) (Fin N) ℝ) :
    LinearMap.range (piStarFromMatrix P) ≤
    Submodule.span ℝ (Set.range (fun i => P.mulVec (Pi.single i 1))) := by
  classical
  -- Any element of the range is of the form `P.mulVec x`;
  -- decompose `x = ∑ i, (x i) • Pi.single i 1` and use linearity
  -- of `mulVec` to realise the value as a linear combination of the
  -- designated spanning set.
  rintro y ⟨x, rfl⟩
  -- Goal: `piStarFromMatrix P x ∈ span ℝ (Set.range …)`
  -- Unfold `piStarFromMatrix` to expose its `mulVec` action.
  change P.mulVec x ∈ Submodule.span ℝ (Set.range (fun i => P.mulVec (Pi.single i 1)))
  -- Expand `x` as a canonical-basis sum and push `mulVec` through the sum.
  have hx : x = ∑ i, (x i) • (Pi.single (M := fun _ : Fin N ↦ ℝ) i 1) :=
    pi_eq_sum_univ' x
  rw [hx]
  -- Distribute `mulVec` over the finite sum and the scalar multiples.
  have hsum : P.mulVec (∑ i, (x i) • (Pi.single (M := fun _ : Fin N ↦ ℝ) i 1))
      = ∑ i, (x i) • P.mulVec (Pi.single (M := fun _ : Fin N ↦ ℝ) i 1) := by
    classical
    induction (Finset.univ : Finset (Fin N)) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      simp [Finset.sum_insert ha, Matrix.mulVec_add, Matrix.mulVec_smul, ih]
  rw [hsum]
  -- Each summand `(x i) • P.mulVec (Pi.single i 1)` is in the span
  -- because `P.mulVec (Pi.single i 1)` belongs to the designated set.
  refine Submodule.sum_mem _ ?_
  intro i _hi
  refine Submodule.smul_mem _ (x i) ?_
  exact Submodule.subset_span ⟨i, rfl⟩

/-- **Paper §28.3 p. 137–138 — Full-rank specialisation.**

For the identity projection matrix, the range of
`piStarFromMatrix` saturates the whole ambient space `⊤`. This is
the full-rank vertex of the rank-monotonicity statement. -/
theorem piStarFromMatrix_identity_range_top (N : ℕ) [Nonempty (Fin N)] :
    LinearMap.range (piStarFromMatrix (1 : Matrix (Fin N) (Fin N) ℝ)) = ⊤ := by
  -- Surjectivity: every `x` is hit by itself, since
  -- `piStarFromMatrix 1 x = (1 : Matrix …).mulVec x = x`.
  refine LinearMap.range_eq_top.mpr ?_
  intro x
  refine ⟨x, ?_⟩
  exact piStarFromMatrix_identity N x

/-! ## Kernel-only axiom trace -/

#print axioms piStarFromMatrix_range_le
#print axioms piStarFromMatrix_identity_range_top

end PallLean.Paper93.Paper283
