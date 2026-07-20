import PallLean.Paper93.DeepMath.PathB.ComputationalDepthCrossingComplexity
import PallLean.Paper93.DeepMath.PathB.ComputationalDepthTraceSchemaComplete

/-!
# The crossing-sequence count is capped at time

The Phase-1 crossing-sequence measure lives on the machine's *run* (it needs head positions), so it is
not a tape-trace measure `μ : List (List Bool) → ℕ` and does not fit `traceInv μ`.  But its ceiling is
exactly the same, and it fits the separation framework one level up, at the `Invariant` level:

* `InvHard_mono` — hardness is monotone: a *smaller* hard invariant forces a *larger* one hard (a
  bigger invariant `≥` a superpolynomial one is superpolynomial).
* `crossingInv` — the worst-case boundary-crossing count over length-`n` inputs and boundaries at the
  canonical clock.
* `crossingInv_le_minHalt` — a boundary is crossed at most once per step
  (`crossingCount_le_time`), so `crossingInv M n ≤ minHalt M n` (the time).
* `minHalt_le_traceInv_traceSize` — time is dominated by the trace-size invariant.
* `crossingInv_hard_imp_sep` — hence a hard crossing invariant, being `≤ traceInv traceSize`, forces
  `traceInv traceSize` hard, which is the separation.  **Crossing-sequence hardness ⇒ separation, with
  no gain over time** — the crossing method's polynomial ceiling (`crossingCount ≤ time`), now stated
  inside the separation framework.

So the crossing-sequence count joins the capped family (novelty, F₂ trace-rank, transitions): its
hardness is exactly time's, so it too cannot be the super-additive escape.

Nothing here is `NEXP ⊄ ACC⁰` or `P ≠ NP`.
-/

namespace PallLean.Paper93.DeepMath.PathB.TraceCrossingCeiling

open Classical
open PallLean.Paper93.DeepMath.PathB.ComposableMachine
open PallLean.Paper93.DeepMath.PathB.ObserverClassSemantics
open PallLean.Paper93.DeepMath.PathB.ObserverInvariantBridge
open PallLean.Paper93.DeepMath.PathB.TraceMeasureSchema
open PallLean.Paper93.DeepMath.PathB.CrossingComplexity
open PallLean.Paper93.DeepMath.PathB.TraceSchemaComplete (traceSize_hard_iff_sep)

/-- **Hardness is monotone.**  If `Inv1 ≤ Inv2` pointwise and `Inv1` is hard, so is `Inv2`. -/
theorem InvHard_mono (SATV : NPObs) (Inv1 Inv2 : Invariant)
    (hmono : ∀ M n, Inv1 M n ≤ Inv2 M n) (h1 : InvHard SATV Inv1) : InvHard SATV Inv2 := by
  intro M T hD hpb2
  exact h1 M T hD (polyBounded_of_le (fun n => hmono M n) hpb2)

/-- Time (`minHalt`) is dominated by the trace-size invariant: a trace has at least as many cells as
rows, and there are `minHalt + 1` rows. -/
theorem minHalt_le_traceInv_traceSize (M : Machine) (n : ℕ) :
    minHalt M n ≤ traceInv traceSize M n := by
  have key : traceSize (traceObj M (minHalt M n) (List.ofFn (fun _ : Fin n => false)))
      ≤ traceInv traceSize M n := by
    unfold traceInv
    exact Finset.le_sup
      (f := fun v : Fin n → Bool => traceSize (traceObj M (minHalt M n) (List.ofFn v)))
      (Finset.mem_univ (fun _ : Fin n => false))
  have hlen : (traceObj M (minHalt M n) (List.ofFn (fun _ : Fin n => false))).length
      = minHalt M n + 1 := by
    unfold traceObj; rw [List.length_map, List.length_range]
  have hge : (traceObj M (minHalt M n) (List.ofFn (fun _ : Fin n => false))).length
      ≤ traceSize (traceObj M (minHalt M n) (List.ofFn (fun _ : Fin n => false))) := by
    unfold traceSize; omega
  omega

/-- **The crossing-sequence invariant.**  The worst-case number of boundary crossings over length-`n`
inputs and boundaries `< minHalt + 1`, at the canonical clock. -/
noncomputable def crossingInv : Invariant := fun M n =>
  Finset.univ.sup fun v : Fin n → Bool =>
    (Finset.range (minHalt M n + 1)).sup fun b =>
      crossingCount M (init M (List.ofFn v)) b (minHalt M n)

/-- A boundary is crossed at most once per step, so the crossing invariant is at most the time. -/
theorem crossingInv_le_minHalt (M : Machine) (n : ℕ) : crossingInv M n ≤ minHalt M n := by
  unfold crossingInv
  apply Finset.sup_le
  intro v _
  apply Finset.sup_le
  intro b _
  exact crossingCount_le_time (init M (List.ofFn v)) b (minHalt M n)

theorem crossingInv_le_traceInv_traceSize (M : Machine) (n : ℕ) :
    crossingInv M n ≤ traceInv traceSize M n :=
  le_trans (crossingInv_le_minHalt M n) (minHalt_le_traceInv_traceSize M n)

/-- **The crossing-sequence count is capped at time.**  A hard crossing-sequence invariant only
re-proves that time is hard, hence the separation — the crossing method's polynomial ceiling, inside
the separation framework. -/
theorem crossingInv_hard_imp_sep (SATV : NPObs) (hH : InvHard SATV crossingInv) :
    ¬ PolyCollapse SATV :=
  (traceSize_hard_iff_sep SATV).mp
    (InvHard_mono SATV crossingInv (traceInv traceSize) crossingInv_le_traceInv_traceSize hH)

end PallLean.Paper93.DeepMath.PathB.TraceCrossingCeiling
