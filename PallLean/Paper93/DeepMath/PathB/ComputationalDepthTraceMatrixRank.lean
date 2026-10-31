import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTraceSpaceKill
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.ZMod.Basic

/-!
# The computation-tableau rank proxy: definition and domination

A concrete structural measure of a computation, per the falsification-first program: view the trace
`traceObj M t x : List (List Bool)` as a Boolean matrix (rows = configurations, columns = tape
cells) over `𝔽₂`, and take its **rank**.

This file supplies only the *definition* and the *cash-out (domination) side*:

* `traceRank` — the `𝔽₂`-rank of the tableau (width `rowMax` = the max configuration length).
* `traceRank_le_rows` / `traceRank_le_rowMax` — rank is at most the number of rows *and* at most the
  width (`Matrix.rank_le_card_height/width`).
* `traceRank_sizeDominated` — hence `traceRank ≤ rowMax ≤ traceSize`: **size-dominated**, so
  generically sound for free (`traceRank_genSound`).

The width bound `traceRank ≤ rowMax` is the crucial structural fact: **tableau rank is bounded by
space**, not time.  Its consequences for the hard side are pursued (adversarially) in
`TraceMatrixRankRobustness`.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TraceMatrixRank

open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.SeparationNoGo (InvGenSound)
open PallLean.Paper93.DeepMath.PathB.TraceMeasureSchema
open PallLean.Paper93.DeepMath.PathB.TraceSpaceKill (rowMax sizeDominated_rowMax)

/-- `𝔽₂ = ZMod 2` is a field. -/
instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The computation tableau as an `𝔽₂` matrix: rows are configurations, columns are tape cells
(padded to width `rowMax`). -/
noncomputable def tableauMat (tr : List (List Bool)) :
    Matrix (Fin tr.length) (Fin (rowMax tr)) (ZMod 2) :=
  fun i j => if (tr.getD (i : ℕ) []).getD (j : ℕ) false then 1 else 0

/-- **The tableau-rank measure**: the `𝔽₂`-rank of the computation tableau. -/
noncomputable def traceRank (tr : List (List Bool)) : ℕ := (tableauMat tr).rank

/-- Rank is at most the number of rows (configurations). -/
theorem traceRank_le_rows (tr : List (List Bool)) : traceRank tr ≤ tr.length :=
  (Matrix.rank_le_card_height _).trans_eq (Fintype.card_fin _)

/-- **Rank is at most the width = `rowMax` = space.**  The crucial structural fact: tableau rank is
a *space* measure. -/
theorem traceRank_le_rowMax (tr : List (List Bool)) : traceRank tr ≤ rowMax tr :=
  (Matrix.rank_le_card_width _).trans_eq (Fintype.card_fin _)

/-- **The tableau rank is size-dominated** (via the width bound `≤ rowMax ≤ traceSize`), hence a
legitimate poly-dominated proxy. -/
theorem traceRank_sizeDominated : SizeDominated traceRank :=
  fun tr => (traceRank_le_rowMax tr).trans (sizeDominated_rowMax tr)

/-- **The cash-out side holds for free.**  Size-domination makes the tableau-rank invariant
generically sound: every polynomial-time decider has a polynomially-bounded tableau rank. -/
theorem traceRank_genSound : InvGenSound (traceInv traceRank) :=
  traceInv_genSound traceRank traceRank_sizeDominated

end PallLean.Paper93.DeepMath.PathB.TraceMatrixRank
