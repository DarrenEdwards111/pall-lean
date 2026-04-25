import PallLean.Paper93.DeepMath.PathB.CompiledGadgetPosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

/-!
# Full rank of the compiled gadget under positivity

The compiled gadget `compiledGadget α n := α • I + L_{K_n}` has full rank `n`
when `α > 0` and `n ≥ 1`. The proof goes:

  1. The sibling `CompiledGadgetPosDef` file establishes
     `compiledGadget_posDef : (compiledGadget α n).PosDef` for `α > 0`,
     `n ≥ 1`. (Strictly, the inline construction works for all `n`, but the
     downstream Path B convention carries `1 ≤ n`.)
  2. Any `PosDef` matrix over a field is invertible
     (`Matrix.PosDef.isUnit`).
  3. An invertible `n × n` matrix has rank `Fintype.card (Fin n) = n`
     (`Matrix.rank_of_isUnit`).
-/

namespace PallLean.Paper93.DeepMath.PathB

open PallLean.Paper93.DeepMath.GadgetRank

/-- The compiled gadget is invertible whenever `α > 0` and `n ≥ 1`. This is
the bridge from `PosDef` (sibling file) to `IsUnit`, used to extract full
rank below. -/
theorem compiledGadget_isUnit (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 1 ≤ n) :
    IsUnit (compiledGadget α n) :=
  (compiledGadget_posDef α n hα hn).isUnit

/-- **Full-rank theorem for the compiled gadget.**
For `α > 0` and `n ≥ 1`, the compiled gadget `α • I + L_{K_n}` has rank
exactly `n`. The argument is `PosDef ⇒ IsUnit ⇒ rank = Fintype.card (Fin n) = n`,
using `Matrix.PosDef.isUnit` and `Matrix.rank_of_isUnit` from Mathlib together
with the sibling `compiledGadget_posDef` lemma. -/
theorem compiledGadget_rank_full (α : ℝ) (n : ℕ) (hα : 0 < α) (hn : 1 ≤ n) :
    (compiledGadget α n).rank = n := by
  have h_isUnit : IsUnit (compiledGadget α n) :=
    compiledGadget_isUnit α n hα hn
  have h_rank : (compiledGadget α n).rank = Fintype.card (Fin n) :=
    Matrix.rank_of_isUnit (compiledGadget α n) h_isUnit
  rw [h_rank, Fintype.card_fin]

end PallLean.Paper93.DeepMath.PathB
