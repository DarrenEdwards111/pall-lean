import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTraceSchemaComplete

/-!
# The size-dominated schema's ceiling: `traceSize` is maximal

Step 5 established that a size-dominated trace measure is generically sound for free
(`traceInv_genSound`) and that the search space is complete (`traceSchema_complete`), with
`traceSize` — time in disguise — as the canonical witness.  This file pins the schema's
**ceiling**: within the size-dominated family, `traceSize` is the *maximal* measure, so the
whole family's separating power is exactly `traceSize`'s = the separation, and no size-
dominated measure does better.

* `traceInv_le_traceSize` — every size-dominated `μ` gives `traceInv μ M n ≤ traceInv
  traceSize M n` pointwise (size-domination lifts through the per-length `Finset.sup`).
* `traceInv_hard_imp_traceSize_hard` — hence `μ`'s hardness implies `traceSize`'s: `traceSize`
  is the top of the family under `InvHard`.
* `sizeDominated_ceiling` — **the ceiling theorem**: a *hard* size-dominated measure exists
  iff `traceSize` itself is hard, i.e. (with `traceSize_hard_iff_sep`) iff `¬ PolyCollapse`.
  The size-dominated schema separates *only* to the extent time does.
* `no_sizeDominated_beyond_time` — the contrapositive: absent time-hardness, **no** size-
  dominated measure is hard.  The whole family lives or dies with raw time.

**Consequence for the frontier.**  Size-domination — the property that made generic soundness
free (S1) — is exactly what caps the schema at time.  Content beyond time therefore requires a
measure that is *not* size-dominated, whose generic soundness must be earned by a genuine
transfer theorem rather than the free S1 bound.  This is the precise fork the search now faces.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TraceSchemaCeiling

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics
open PallLean.Paper93.DeepMath.PathB.ObserverInvariantBridge
open PallLean.Paper93.DeepMath.PathB.SeparationNoGo
open PallLean.Paper93.DeepMath.PathB.TraceMeasureSchema
open PallLean.Paper93.DeepMath.PathB.TraceSchemaComplete (traceSize_hard_iff_sep)
open PallLean.Paper93.DeepMath.PathB.PvsNPSeparatingInvariant (PolyBounded)

/-- **The pointwise ceiling.**  Size-domination lifts through the per-length worst case: every
size-dominated `μ` is bounded by `traceSize` on the invariant. -/
theorem traceInv_le_traceSize (μ : List (List Bool) → ℕ) (hμ : SizeDominated μ)
    (M : Machine) (n : ℕ) : traceInv μ M n ≤ traceInv traceSize M n := by
  unfold traceInv
  apply Finset.sup_le
  intro v _
  exact le_trans (hμ _)
    (Finset.le_sup (f := fun v => traceSize (traceObj M (minHalt M n) (List.ofFn v)))
      (Finset.mem_univ v))

/-- **`traceSize` is the top of the family.**  Any size-dominated measure's hardness implies
`traceSize`'s: if `traceSize` were poly on some decider then so would `μ ≤ traceSize` be,
contradicting `μ`'s hardness. -/
theorem traceInv_hard_imp_traceSize_hard (SATV : NPObs) (μ : List (List Bool) → ℕ)
    (hμ : SizeDominated μ) (hH : InvHard SATV (traceInv μ)) :
    InvHard SATV (traceInv traceSize) := by
  intro M T hD hPB
  exact hH M T hD (polyBounded_of_le (traceInv_le_traceSize μ hμ M) hPB)

/-- **THE CEILING THEOREM.**  A hard size-dominated trace measure exists iff `traceSize`
itself is hard — the family's separating power is exactly `traceSize`'s. -/
theorem sizeDominated_ceiling (SATV : NPObs) :
    (∃ μ, SizeDominated μ ∧ InvHard SATV (traceInv μ)) ↔ InvHard SATV (traceInv traceSize) := by
  constructor
  · rintro ⟨μ, hμ, hH⟩
    exact traceInv_hard_imp_traceSize_hard SATV μ hμ hH
  · intro hH
    exact ⟨traceSize, sizeDominated_traceSize, hH⟩

/-- **The ceiling, in separation terms.**  The size-dominated schema separates exactly to the
extent time does: a hard size-dominated measure exists iff `¬ PolyCollapse`. -/
theorem sizeDominated_hard_iff_sep (SATV : NPObs) :
    (∃ μ, SizeDominated μ ∧ InvHard SATV (traceInv μ)) ↔ ¬ PolyCollapse SATV :=
  (sizeDominated_ceiling SATV).trans (traceSize_hard_iff_sep SATV)

/-- **No size-dominated measure beats time.**  If `traceSize` is not hard (no time separation),
then no size-dominated measure is hard.  The whole family lives or dies with raw time. -/
theorem no_sizeDominated_beyond_time (SATV : NPObs) (μ : List (List Bool) → ℕ)
    (hμ : SizeDominated μ) (h : ¬ InvHard SATV (traceInv traceSize)) :
    ¬ InvHard SATV (traceInv μ) := fun hH =>
  h (traceInv_hard_imp_traceSize_hard SATV μ hμ hH)

end PallLean.Paper93.DeepMath.PathB.TraceSchemaCeiling
