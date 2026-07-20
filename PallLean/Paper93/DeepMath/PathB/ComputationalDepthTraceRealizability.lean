import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTraceCrossingCeiling
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTraceRowCountCeiling

/-!
# The realizability characterization: only realizable traces are ever seen

Every previous cap (size-domination, poly-size, row-count, novelty, F₂ rank, transitions, crossings)
bounds a measure by requiring an inequality on **all** traces `tr : List (List Bool)`.  But the schema's
worst case `traceInv μ M n` only ever feeds `μ` a **realizable** trace — one of the form
`traceObj M t x`, the actual tape evolution of a machine.  So a measure need only be bounded *there* to
be capped, even if it is arbitrarily wild on non-realizable traces.  This strictly broadens the ceiling.

* `Realizable tr` — `∃ M t x, tr = traceObj M t x`.
* `traceObj_length` — a realizable trace has exactly `t + 1` rows (its step count `+ 1`).
* `RealizablyPolyDominated μ` — `μ (traceObj M t x) ≤ c·(t + 1)^k` for all `M, t, x`: bounded by a
  polynomial in the step count, but **only on realizable traces**.
* `rowCountDominated_realizablyPolyDominated` — every row-count-dominated measure is realizably-poly-
  dominated (row count `= t + 1`), so this class contains all the earlier ones.
* `realizablyPolyDominated_traceInv_le` — `traceInv μ M n ≤ c·(traceInv traceSize M n + 1)^k`: the
  realizable bound at the canonical clock (`t = minHalt`) lifts through `minHalt ≤ traceInv traceSize`.
* `realizablyPolyDominated_hard_imp_sep` — hence such a measure's hardness is time's: the separation,
  no gain.

**What this pins.**  Bounding a measure only on the traces a machine can actually produce is already
enough to cap it — the escape cannot come from a measure that is merely wild off the realizable set.
The super-additive escape must be superpolynomial *on realizable traces themselves*, in the step count
— exactly the `P` vs `NP` crux, now with the realizability freedom removed as an avenue.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TraceRealizability

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics
open PallLean.Paper93.DeepMath.PathB.ObserverInvariantBridge
open PallLean.Paper93.DeepMath.PathB.TraceMeasureSchema
open PallLean.Paper93.DeepMath.PathB.PolyCeiling
open PallLean.Paper93.DeepMath.PathB.TraceRowCountCeiling
open PallLean.Paper93.DeepMath.PathB.TraceCrossingCeiling (minHalt_le_traceInv_traceSize)
open PallLean.Paper93.DeepMath.PathB.TraceSchemaComplete (traceSize_hard_iff_sep)

/-- A trace is **realizable** if it is the tape evolution of some machine on some input. -/
def Realizable (tr : List (List Bool)) : Prop :=
  ∃ (M : Machine) (t : ℕ) (x : List Bool), tr = traceObj M t x

/-- A realizable trace of `t` steps has exactly `t + 1` rows. -/
theorem traceObj_length (M : Machine) (t : ℕ) (x : List Bool) :
    (traceObj M t x).length = t + 1 := by
  unfold traceObj; rw [List.length_map, List.length_range]

/-- A measure bounded by a polynomial in the step count — **but only on realizable traces**. -/
def RealizablyPolyDominated (μ : List (List Bool) → ℕ) : Prop :=
  ∃ c k : ℕ, ∀ (M : Machine) (t : ℕ) (x : List Bool), μ (traceObj M t x) ≤ c * (t + 1) ^ k

/-- Row-count domination implies realizable-poly domination: on a realizable trace the row count is
`t + 1`.  So this class contains every earlier capped class. -/
theorem rowCountDominated_realizablyPolyDominated (μ : List (List Bool) → ℕ)
    (h : RowCountDominated μ) : RealizablyPolyDominated μ := by
  obtain ⟨c, k, hck⟩ := h
  refine ⟨c * 2 ^ k, k, fun M t x => ?_⟩
  have h1 := hck (traceObj M t x)
  rw [traceObj_length] at h1
  refine h1.trans ?_
  rw [mul_assoc, ← mul_pow]
  gcongr
  omega

/-- The realizable bound lifts to the schema: `traceInv μ M n ≤ c·(traceInv traceSize M n + 1)^k`,
using that the canonical clock produces a realizable trace of `minHalt` steps and `minHalt ≤ traceInv
traceSize`. -/
theorem realizablyPolyDominated_traceInv_le (μ : List (List Bool) → ℕ) (c k : ℕ)
    (hb : ∀ (M : Machine) (t : ℕ) (x : List Bool), μ (traceObj M t x) ≤ c * (t + 1) ^ k)
    (M : Machine) (n : ℕ) :
    traceInv μ M n ≤ c * (traceInv traceSize M n + 1) ^ k := by
  have h1 : traceInv μ M n ≤ c * (minHalt M n + 1) ^ k := by
    unfold traceInv
    apply Finset.sup_le
    intro v _
    exact hb M (minHalt M n) (List.ofFn v)
  refine h1.trans ?_
  gcongr
  exact minHalt_le_traceInv_traceSize M n

/-- **The realizability ceiling.**  A hard realizably-poly-dominated measure only re-proves that time
is hard. -/
theorem realizablyPolyDominated_hard_imp_traceSize_hard (SATV : NPObs) (μ : List (List Bool) → ℕ)
    (hμ : RealizablyPolyDominated μ) (hH : InvHard SATV (traceInv μ)) :
    InvHard SATV (traceInv traceSize) := by
  obtain ⟨c, k, hb⟩ := hμ
  intro M T hD hPB
  exact hH M T hD
    (polyBounded_of_le (realizablyPolyDominated_traceInv_le μ c k hb M) (polyBounded_polyComp c k hPB))

/-- The realizability ceiling in separation terms: bounding a measure only on realizable traces already
caps it at time. -/
theorem realizablyPolyDominated_hard_imp_sep (SATV : NPObs) (μ : List (List Bool) → ℕ)
    (hμ : RealizablyPolyDominated μ) (hH : InvHard SATV (traceInv μ)) :
    ¬ PolyCollapse SATV :=
  (traceSize_hard_iff_sep SATV).mp
    (realizablyPolyDominated_hard_imp_traceSize_hard SATV μ hμ hH)

end PallLean.Paper93.DeepMath.PathB.TraceRealizability
