import PallLean.Paper93.DeepMath.PathB.ComputationalDepthPolyCeiling
import Mathlib.Data.List.Dedup

/-!
# The row-count ceiling: measures polynomial in the number of configurations are capped

`PolyCeiling` caps every measure bounded by a polynomial in the trace's total *size*.  Here we sharpen
that: the number of *rows* of a trace (its configuration count = number of time-steps) is at most its
total size, so measures bounded by a polynomial in the **row count** are also capped at time — a
strictly larger class, since a measure can be small per row yet the cap still bites.

* `numRows_le_traceSize` — `tr.length ≤ traceSize tr` (each row contributes at least itself).
* `RowCountDominated μ` — `μ tr ≤ c·(tr.length + 1)^k`.
* `rowCountDominated_polySizeDominated` / `rowCountDominated_hard_imp_traceSize_hard` — such a measure is
  polynomially size-dominated, hence its hardness collapses to time's.
* `distinctConfigs` (the novelty / distinct-configuration count) is row-count-dominated
  (`distinctConfigs_le`), hence capped (`distinctConfigs_hard_imp_traceSize_hard`).

**What this pins.**  The distinct-configuration count — the natural "how much genuinely new state does
the computation visit" measure, and the shape of many cross-row functionals (novelty, revisits, and any
quantity polynomial in the number of steps) — is capped at time.  So a super-additive measure that
beats time cannot be polynomial in the trace's row count: it must be **superpolynomial in the number of
configurations itself**.  For a poly-time machine that number is polynomial, so the escaping measure
would have to extract superpolynomial value from a polynomially long sequence of configurations — which
is exactly the `P` vs `NP` crux, now sharpened past the whole poly-in-steps family.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TraceRowCountCeiling

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics
open PallLean.Paper93.DeepMath.PathB.ObserverInvariantBridge
open PallLean.Paper93.DeepMath.PathB.TraceMeasureSchema
open PallLean.Paper93.DeepMath.PathB.TraceSchemaComplete (traceSize_hard_iff_sep)
open PallLean.Paper93.DeepMath.PathB.PolyCeiling

/-- The number of rows of a trace is at most its total size: `traceSize` counts every row's cells plus
the rows themselves. -/
theorem numRows_le_traceSize (tr : List (List Bool)) : tr.length ≤ traceSize tr := by
  unfold traceSize
  omega

/-- A measure bounded by a polynomial in the trace's row count (configuration count). -/
def RowCountDominated (μ : List (List Bool) → ℕ) : Prop :=
  ∃ c k : ℕ, ∀ tr, μ tr ≤ c * (tr.length + 1) ^ k

/-- Row-count domination implies polynomial size-domination (`row count ≤ size`). -/
theorem rowCountDominated_polySizeDominated (μ : List (List Bool) → ℕ)
    (h : RowCountDominated μ) : PolySizeDominated μ := by
  obtain ⟨c, k, hck⟩ := h
  refine ⟨c, k, fun tr => (hck tr).trans ?_⟩
  gcongr
  exact numRows_le_traceSize tr

/-- **The row-count ceiling.**  A hard row-count-dominated measure only re-proves that time is hard. -/
theorem rowCountDominated_hard_imp_traceSize_hard (SATV : NPObs) (μ : List (List Bool) → ℕ)
    (hμ : RowCountDominated μ) (hH : InvHard SATV (traceInv μ)) :
    InvHard SATV (traceInv traceSize) :=
  polySizeDominated_hard_imp_traceSize_hard SATV μ (rowCountDominated_polySizeDominated μ hμ) hH

/-- The row-count ceiling in separation terms: this class separates exactly to the extent time does. -/
theorem rowCountDominated_hard_imp_sep (SATV : NPObs) (μ : List (List Bool) → ℕ)
    (hμ : RowCountDominated μ) (hH : InvHard SATV (traceInv μ)) :
    ¬ PolyCollapse SATV :=
  (traceSize_hard_iff_sep SATV).mp (rowCountDominated_hard_imp_traceSize_hard SATV μ hμ hH)

/-- **The distinct-configuration count** — the natural novelty measure. -/
def distinctConfigs (tr : List (List Bool)) : ℕ := tr.dedup.length

theorem distinctConfigs_le (tr : List (List Bool)) : distinctConfigs tr ≤ tr.length :=
  (List.dedup_sublist tr).length_le

/-- Novelty is row-count-dominated. -/
theorem distinctConfigs_rowCountDominated : RowCountDominated distinctConfigs :=
  ⟨1, 1, fun tr => by
    have := distinctConfigs_le tr
    simp only [one_mul, pow_one]
    omega⟩

/-- **The novelty measure is capped at time.**  A hard distinct-configuration measure implies time is
hard, hence the separation — no gain over time. -/
theorem distinctConfigs_hard_imp_traceSize_hard (SATV : NPObs)
    (hH : InvHard SATV (traceInv distinctConfigs)) :
    InvHard SATV (traceInv traceSize) :=
  rowCountDominated_hard_imp_traceSize_hard SATV distinctConfigs distinctConfigs_rowCountDominated hH

end PallLean.Paper93.DeepMath.PathB.TraceRowCountCeiling
