import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTraceRowCountCeiling
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.ZMod.Basic

/-!
# Named cross-row functionals are capped: trace-rank over F₂ and transitions

The two most natural "cross-row correlation" candidates — the ones a super-additive escape would most
plausibly be — turn out to be capped at time, because each is at most the trace's row count.

* **Trace-rank over F₂** (`traceRank`): view the trace as a matrix over `ZMod 2`, one row per
  configuration.  Linear dependence *across configurations* is the natural algebraic cross-row measure.
  But a matrix's rank is at most its number of rows (`Matrix.rank_le_card_height`), so
  `traceRank tr ≤ tr.length` — row-count-dominated, hence capped (`traceRank_hard_imp_traceSize_hard`).
* **Transitions** (`transitions`): the number of adjacent configuration pairs that differ — "how much
  the state changes over time", a temporal cross-cut measure.  At most one per step, so
  `transitions tr ≤ tr.length` — capped too (`transitions_hard_imp_traceSize_hard`).

Both are genuine cross-row functionals, and both are killed by the row-count ceiling.  The same holds
for any communication- or crossing-style measure bounded by the number of steps.  So the super-additive
escape cannot be trace-rank, transition count, or any per-step-bounded cross-row quantity: it must be
superpolynomial in the configuration count itself — the `P` vs `NP` crux, with these named candidates
explicitly excluded.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TraceRankCeiling

open Classical
open PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics
open PallLean.Paper93.DeepMath.PathB.ObserverInvariantBridge
open PallLean.Paper93.DeepMath.PathB.TraceMeasureSchema
open PallLean.Paper93.DeepMath.PathB.TraceRowCountCeiling

/-- The width used to view the trace as a matrix: the longest configuration. -/
def traceWidth (tr : List (List Bool)) : ℕ := (tr.map List.length).foldr max 0

/-- The trace as a matrix over `F₂`: one row per configuration, entry `(i,j)` the `j`-th tape cell. -/
def traceMatrix (tr : List (List Bool)) :
    Matrix (Fin tr.length) (Fin (traceWidth tr)) (ZMod 2) :=
  Matrix.of fun i j => if (tr.get i).getD j.1 false then 1 else 0

/-- **Trace-rank over F₂**: linear dependence across the configurations. -/
noncomputable def traceRank (tr : List (List Bool)) : ℕ := (traceMatrix tr).rank

/-- Rank is at most the number of rows (configurations). -/
theorem traceRank_le (tr : List (List Bool)) : traceRank tr ≤ tr.length := by
  unfold traceRank
  have h := Matrix.rank_le_card_height (traceMatrix tr)
  rwa [Fintype.card_fin] at h

theorem traceRank_rowCountDominated : RowCountDominated traceRank :=
  ⟨1, 1, fun tr => by have := traceRank_le tr; simp only [one_mul, pow_one]; omega⟩

/-- **Trace-rank is capped at time.**  A hard F₂ trace-rank measure only re-proves time is hard. -/
theorem traceRank_hard_imp_traceSize_hard (SATV : NPObs)
    (hH : InvHard SATV (traceInv traceRank)) :
    InvHard SATV (traceInv traceSize) :=
  rowCountDominated_hard_imp_traceSize_hard SATV traceRank traceRank_rowCountDominated hH

theorem traceRank_hard_imp_sep (SATV : NPObs) (hH : InvHard SATV (traceInv traceRank)) :
    ¬ PolyCollapse SATV :=
  rowCountDominated_hard_imp_sep SATV traceRank traceRank_rowCountDominated hH

/-- **Transitions**: the number of adjacent configuration pairs that differ. -/
def transitions (tr : List (List Bool)) : ℕ :=
  (tr.zip tr.tail).countP (fun p => p.1 != p.2)

/-- At most one transition per step. -/
theorem transitions_le (tr : List (List Bool)) : transitions tr ≤ tr.length := by
  unfold transitions
  refine List.countP_le_length.trans ?_
  rw [List.length_zip]
  exact Nat.min_le_left _ _

theorem transitions_rowCountDominated : RowCountDominated transitions :=
  ⟨1, 1, fun tr => by have := transitions_le tr; simp only [one_mul, pow_one]; omega⟩

/-- **Transitions are capped at time.**  A hard transition-count measure only re-proves time is hard. -/
theorem transitions_hard_imp_traceSize_hard (SATV : NPObs)
    (hH : InvHard SATV (traceInv transitions)) :
    InvHard SATV (traceInv traceSize) :=
  rowCountDominated_hard_imp_traceSize_hard SATV transitions transitions_rowCountDominated hH

theorem transitions_hard_imp_sep (SATV : NPObs) (hH : InvHard SATV (traceInv transitions)) :
    ¬ PolyCollapse SATV :=
  rowCountDominated_hard_imp_sep SATV transitions transitions_rowCountDominated hH

end PallLean.Paper93.DeepMath.PathB.TraceRankCeiling
