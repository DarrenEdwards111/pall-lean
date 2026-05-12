import PallLean.Paper93.DeepMath.PathB.GaugePropertyDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetDef
import PallLean.Paper93.DeepMath.GadgetRank.CompiledGadgetPSD
import PallLean.Paper93.DeepMath.GraphSpectral.LaplacianPSDNonnegSymm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Principal minor of the compiled gadget at the empty subset

This file proves two facts about the compiled gadget
`compiledGadget α n := α • I + L_{K_n}`:

1. The principal minor at the empty subset `(∅ : Finset (Fin n))` equals `1`.
   This is a direct consequence of `Matrix.det_isEmpty`: the submatrix indexed
   by the (empty) subtype `↥(∅ : Finset (Fin n))` is a `0×0` matrix whose
   determinant is `1`.

2. As a corollary, `compiledGadget α n` satisfies `IsAmplituhedronGauge` for
   the trivial empty family `(∅ : Finset (Finset (Fin n)))`. The
   universally-quantified principal-minor condition is discharged vacuously,
   so the only nontrivial obligation is positive definiteness, which we
   establish directly from `α > 0`, the Laplacian PSD lemma, and
   `Matrix.PosDef.add_posSemidef`.

These two results push Route C ⇒ Route A for the truncated NS model in the
trivially-empty determining-family case.
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank
open PallLean.Paper93.DeepMath.GraphSpectral
open PallLean.Paper93.DeepMath.LPS

/-- The principal minor of `compiledGadget α n` at the empty subset of `Fin n`
    equals `1`. The submatrix is indexed by the empty subtype `↥∅`, hence is
    a `0×0` matrix with determinant `1`. -/
theorem compiledGadget_minor_empty (α : ℝ) (n : ℕ) :
    ((compiledGadget α n).submatrix
      (fun (i : (∅ : Finset (Fin n))) => i.val)
      (fun (j : (∅ : Finset (Fin n))) => j.val)).det = 1 := by
  -- `↥(∅ : Finset (Fin n))` is `IsEmpty` via `Finset.instIsEmpty`, so the
  -- submatrix is `0×0`, and `Matrix.det_isEmpty` gives det = 1.
  exact Matrix.det_isEmpty

/-- Local helper: `compiledGadget α n` is positive definite when `α > 0` and
    `1 ≤ n`. Proof:
    `compiledGadget α n = α • I + L_{K_n}` with `α • I` PosDef (since
    `α > 0`) and the Laplacian `L_{K_n}` PosSemidef (since `completeAdj n` is
    symmetric with nonnegative entries). The sum of a PosDef matrix and a
    PosSemidef matrix is PosDef. -/
theorem compiledGadget_posDef_local (α : ℝ) (n : ℕ) (hα : 0 < α) (_hn : 1 ≤ n) :
    (compiledGadget α n).PosDef := by
  -- Identity is PosDef; smul by a positive scalar preserves PosDef.
  have h_alpha_I : (α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef :=
    Matrix.PosDef.one.smul hα
  -- The complete-graph adjacency is symmetric with nonneg entries, so its
  -- Laplacian is PosSemidef.
  have h_sym : (completeAdj n).IsSymm := completeAdj_symm n
  have h_nn : ∀ i j, 0 ≤ completeAdj n i j := by
    intros i j
    unfold completeAdj
    by_cases h : i = j
    · simp [h]
    · simp [h]
  have h_lap : (laplacian (completeAdj n)).PosSemidef :=
    laplacian_posSemidef_of_symm_nonneg (completeAdj n) h_sym h_nn
  -- compiledGadget α n = α • I + laplacian (completeAdj n)
  unfold compiledGadget
  exact h_alpha_I.add_posSemidef h_lap

/-- The compiled gadget `compiledGadget α n` satisfies `IsAmplituhedronGauge`
    for the trivial empty family `(∅ : Finset (Finset (Fin n)))`.

    The principal-minor obligation is discharged vacuously (no `J ∈ ∅`), so
    the only real content is positive definiteness, supplied by
    `compiledGadget_posDef_local`. -/
theorem compiledGadget_isAmplituhedronGauge_empty_family (α : ℝ) (n : ℕ)
    (hα : 0 < α) (hn : 1 ≤ n) :
    IsAmplituhedronGauge (compiledGadget α n) (∅ : Finset (Finset (Fin n))) := by
  refine ⟨compiledGadget_posDef_local α n hα hn, ?_⟩
  intros J hJ
  exact absurd hJ (Finset.notMem_empty J)

end PallLean.Paper93.DeepMath.PathB
